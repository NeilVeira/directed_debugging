import os 
import argparse
import re
import random
import math
import sys
import numpy as np
import sklearn.metrics
from sklearn.model_selection import KFold 

from suspect_prediction import SuspectPrediction
from suspect2vec import Suspect2Vec

INF = 1e12

#define hierarchical levels of all rtl types
HIERARCHY = {"module":1, 
            "func":1,
            "input":4, 
            "inout":4,
            "wire":4, 
            "reg":4,
            "gate":4,
            "always":2,
            "if":2,
            "cond":3,
            "stmt":3,
            "block":2,
            "assign":3,
            "expr":3,
            "inst":2,
            "case":2,
            "for":2,
            "sequence":2,
            "assume":2,
            "property":2,
            "assert":2,
            "constraint":2,
            "external":4,
            }
            
class Suspect(object):
    '''
    Class to encapsulate info of a suspect
    '''
    def __init__(self, filename, name, l, r, rtl_type, id):
        self.filename = filename
        self.name = name
        self.rtl_type = rtl_type 
        if rtl_type not in HIERARCHY.keys():
            raise Exception("Unknown type %s (file %s: %s-%s)" %(rtl_type, filename,l,r))
        self.level = HIERARCHY[rtl_type]
        #self.level = name.count("/")+1
        self.l = l 
        self.r = r 
        self.id = id
        
    def __eq__(self, other):
        return self.name == other.name 

    def __hash__(self):
        return hash(self.name)
        
    def __lt__(self,other):
        return self.id < other.id
        
    def __str__(self):
        return "suspect %s: %s %s %s %s - %s" %(str(self.id).ljust(3), self.name.ljust(50), self.rtl_type.ljust(20), \
                self.filename.ljust(30),self.l.ljust(6),self.r.ljust(8))
        
        
class Failure(object):
    '''
    Class to encapsulate info of a failure
    '''
    def __init__(self, fail_dir, suspectz, timez, fail_time):
        self.fail_dir = fail_dir
        self.suspectz = suspectz
        self.timez = timez
        self.fail_time = fail_time
        self.module = None
        self.num_suspects = len(suspectz)
        self.num_suffix_suspects = 0
        self.runtime = 0 
        self.suffix_runtime = 0
        
    def __str__(self):
        return "Failure %s" %(self.fail_dir)
        
        
def do_prediction_random(sample, n, k, args):
    '''
    Random prediction mechanism, for comparison purposes. 
    '''
    if args.verbose >= 2:
        print("Doing random prediction with initial sample", sample)
    ranking = list(sample)
    
    not_sample = []
    for j in range(n):
        if j not in ranking:
            not_sample.append(j)
    
    while len(ranking) < k:
        id = random.choice(not_sample)
        ranking.append(id)
        not_sample.remove(id)
        
    return ranking
        
        
def do_prediction_optimal(sample, n, k, target, args):
    '''
    Optimal prediction mechanism, for comparison purposes. 
    '''
    if args.verbose >= 2:
        print("Doing optimal prediction with initial sample", sample)
    ranking = list(sample)
    
    #first predict all correct suspects
    for id in target:
        if len(ranking) >= k:
            break
        if id not in ranking:
            ranking.append(id)
            
    #predict remaining suspects arbitrarily until we have k 
    for i in range(n):
        if len(ranking) >= k:
            break
        if i not in ranking:
            ranking.append(i)
        
    return ranking
        
                
def evaluate_prediction(suspect_union, target_ids, ranking, est_size):
    '''
    Compute the metric measuring the precision of the prediction algorithm.
    This metric is the area under the curve of (% correct) vs (number of suspects). 
    suspect_union: list of Suspect objects sorted by id
    target_ids: list of ids of the full set of suspects 
    ranking: list of ids of the ranking suspects 
    '''      
    total = len(ranking)
    actual_size = len(target_ids)
    for i in range(total):
        assert 0 <= ranking[i] < len(suspect_union) #ranking valid suspect
        assert ranking[i] not in ranking[i+1:] #no suspect should be ranking twice  
        
    correct_cnt = 0
    incorrect_cnt = 0 
    mean_prec = 0 #mean precision over all sizes
    mean_rec = 0 #mean recall over all sizes
    mean_jac = 0 #mean jaccard index over all sizes
    exact_prec = 0 #precision at correct size 
    exact_rec = 0 #recall at correct size 
    exact_jac = 0 #jaccard index at correct size 
    est_jac = 0 #jaccard index at estimated size 
    
    for i in range(total):
        if ranking[i] in target_ids:
            correct_cnt += 1 
        else:
            incorrect_cnt += 1
        mean_prec += float(correct_cnt)/(i+1)          #precision = tp/(tp+fp)
        mean_rec += float(correct_cnt)/actual_size #recall = tp / (tp+fn)
        mean_jac += float(correct_cnt) / (actual_size + incorrect_cnt)
        if i == actual_size-1:
            exact_prec = float(correct_cnt) / (i+1)
            exact_jac = float(correct_cnt) / (actual_size + incorrect_cnt)
            exact_rec = float(correct_cnt) / actual_size
        if i == est_size-1:
            est_jac = float(correct_cnt) / (actual_size + incorrect_cnt)
            
    mean_prec /= total 
    mean_rec /= total
    mean_jac /= total
    
    size_err = float(abs(est_size-actual_size)) / actual_size
    return mean_prec, mean_rec, mean_jac, exact_prec, exact_rec, exact_jac, est_jac, size_err
 
def eval_pred_v2(n, pred, target):
    true_1hot = np.zeros(n, dtype=np.bool_)
    true_1hot[target] = 1
    pred_1hot = np.zeros(n, dtype=np.bool_)
    pred_1hot[pred] = 1 

    precision, recall, fscore, support = sklearn.metrics.precision_recall_fscore_support(true_1hot, pred_1hot, labels=[0,1])
    size_err = abs(len(target)-len(pred)) / float(len(target))
    return precision[1], recall[1], fscore[1], size_err 
    
def eval_fscore(n, pred, target):
    return eval_pred_v2(n,pred,target)[2]
    

def process_report(fail_dir, suspect_union=set([]), debug_level=INF):
    '''
    Parse the debug reports and other data from the given failure directory. 
    Create Suspect objects for each suspect found. Add unique suspects to suspect_union. 
    debug_level: maximum level of suspects to consider (all suspects at a deeper 
    level are ignored).
    Returns: Failure object containing all important data about the failure, or 
    None if unsuccessful due to missing data / bad path.
    '''
    suspect_path = os.path.join(fail_dir, "suspects.txt")
    time_path = os.path.join(fail_dir, "suspect_times.txt")
    suffix_path = os.path.join(fail_dir, "suffix_data.txt")
    if not (os.path.exists(suspect_path) and os.path.exists(time_path) and os.path.exists(suffix_path)):
        return None
    with open(suspect_path) as f:
        suspect_report = f.read()
    with open(time_path) as f:
        time_report = f.read()
    with open(suffix_path) as f:
        suffix_data = f.read()
        
    report_suspects = []
    timex = {}
    suspect_timez = []  
    
    #parse all available times from time_report 
    for m in re.findall(r"solution\s+\d+\s+([\w/]+)@(\d+)-\d+",time_report):
        if m[0] not in timex.keys() or int(m[1]) > timex[m[0]]: #take maximum time
            timex[m[0]] = int(m[1])            
            
    m = re.search(r"Failure time: (\d+)", suffix_data)
    fail_time = int(m.group(1))
   
    # Parse suspect report 
    for suspect_parse in re.findall(r"rtl\s+([\w/\.]+)\s+(\w+)\s+([\w\./]+)\s+([\d\.]+)\s+([\d\.]+)", suspect_report, flags=re.DOTALL):
        s = Suspect(suspect_parse[2], suspect_parse[0], suspect_parse[3], \
            suspect_parse[4], suspect_parse[1], len(suspect_union))
        if s.level > debug_level:
            continue
            
        # Need to find item in suspect_union which is "equal" to s.
        # How to do a find efficiently on a set in python???
        for item in suspect_union:
            if item == s:
                s = item
                break
        else:
            suspect_union.add(s)
        
        # Try to determine a time for suspect s 
        if s.name in timex.keys():
            suspect_timez.append((timex[s.name],s.id,s.name))
        else:                
            # Check if s.name is a prefix of any suspect in timex, and use the maximum
            # of all such suspects for s's time
            t = 0
            for suspect in timex.keys():
                if suspect.startswith(s.name+"/") and timex[suspect] > t:
                    t = timex[suspect]
            timex[s.name] = t 
            suspect_timez.append((t,s.id,s.name))
    
    suspect_timez.sort()
    suspect_timez.reverse()
    
    idz = [x[1] for x in suspect_timez]
    timez = [x[0] for x in suspect_timez]
    failure = Failure(fail_dir, idz, timez, fail_time)
    
    # Get info on suffix debugging. Note that "Number of suffix suspects: 0" means 
    # that no suffix debug data actually exists for this failure. 
    m = re.search(r"Number of suffix suspects: (\d+)", suffix_data)
    failure.num_suffix_suspects = int(m.group(1))
    m = re.search(r"Debug runtime: ([\.\d]+)", suffix_data)
    failure.runtime = float(m.group(1))
    m = re.search(r"Suffix debug runtime: ([\.\d]+)", suffix_data)
    failure.suffix_runtime = float(m.group(1))
    
    return failure

   
def experiment_k(all_suspectz, suspect_union, args):
    '''
    Evaluate suspect prediction over all values of k
    '''
    m = len(all_suspectz)
    n = len(suspect_union)
    mean_precs = np.zeros(m)
    all_rankingz = []
    rand_rankingz = []
    
    # Axis 0 of all_metrics (in order): 
    # mean precision, mean recall, mean jaccard index, exact precision, exact recall, exact jaccard index, estimated jaccard index, size error 
    # where "mean" = mean over all k, "exact" = value at true k, "estimated" = value at estimated k
    # Axis 1 of all metrics: Prediction, random, optimal 
    # Axis 2 of all metrics: result for each data point in leave-one-out evaluation
    all_metrics = np.zeros((8,3,m))
    est_sizes = np.zeros(m)
    
    predictor = SuspectPrediction(args.prior_var)
    
    # leave-one-out evaluation
    for i in range(m):
        if args.verbose:
            print("Running fold %i/%i" %(i+1,m))
        # Generate training & test data
        train_data = all_suspectz[:i] + all_suspectz[i+1:]
        test_data = all_suspectz[i]
        if args.sample_type == "random":
            random.shuffle(test_data)
        sample = test_data[:int(math.ceil(args.sample_size*len(test_data)))]
        
        # Prediction
        predictor.fit(train_data)
        pred,ranking = predictor.predict(sample, return_full_rank=True)        
        est_size = len(pred)
        est_sizes[i] = est_size
        
        # Comparison with random and optimal
        rand = do_prediction_random(sample, n, n, args)
        opt = do_prediction_optimal(sample, n, n, test_data, args)
        all_rankingz.append(ranking)
        rand_rankingz.append(rand)
        
        # Evaluation
        all_metrics[:,0,i] = evaluate_prediction(suspect_union, test_data, ranking, est_size)
        all_metrics[:,1,i] = evaluate_prediction(suspect_union, test_data, rand, est_size)
        all_metrics[:,2,i] = evaluate_prediction(suspect_union, test_data, opt, len(test_data))
        
    print("Overall stats (%i failures)" %(m))
    print("Means over all k:")
    print("    precision = %.3f" %(np.mean(all_metrics[0][0])))
    print("        random = %.3f" %(np.mean(all_metrics[0][1])))
    print("        optimal = %.3f" %(np.mean(all_metrics[0][2])))
    print("    recall = %.3f" %(np.mean(all_metrics[1][0])) )
    print("    jaccard index = %.3f" %(np.mean(all_metrics[2][0])))
    print("        random = %.3f" %(np.mean(all_metrics[2][1])))
    print("        optimal = %.3f" %(np.mean(all_metrics[2][2])))
    print("At exact k:")
    print("    precision = %.3f" %(np.mean(all_metrics[3][0])))
    print("        random = %.3f" %(np.mean(all_metrics[3][1])))
    print("        optimal = %.3f" %(np.mean(all_metrics[3][2])))
    print("    recall = %.3f" %(np.mean(all_metrics[4][0])))
    print("    jaccard index = %.3f" %(np.mean(all_metrics[5][0])))
    print("        random = %.3f" %(np.mean(all_metrics[5][1])))
    print("        optimal = %.3f" %(np.mean(all_metrics[5][2])))
    print("At estimated k:")
    print("    jaccard_index = %.3f" %(np.mean(all_metrics[6][0])))
    print("        random = %.3f" %(np.mean(all_metrics[6][1])))
    print("        optimal = %.3f" %(np.mean(all_metrics[6][2])))
    print("    size estimation error = %.3f" %(np.mean(all_metrics[7][0])))
       

def experiment_sample_size(all_suspectz, suspect_union, args, all_failurez):
    '''
    Evaluate the prediction at multiple sample sizes from 10% to 80% in 10% increments. 
    '''
    m = len(all_suspectz)
    n = len(suspect_union)
    sample_interval = 0.1
    num_points = int(0.8/sample_interval)+1
    results = np.zeros((m,num_points+1))
    predicted_suspectz = [[] for _ in range(num_points)] #suspect lists for each failure, for each sample size
    
    predictor = SuspectPrediction()
    
    for i in range(m):
        if args.verbose:
            print("Running fold %i/%i" %(i+1,m))
        train_data = all_suspectz[:i] + all_suspectz[i+1:]
        test_data = all_suspectz[i]
        predictor.fit(train_data)
        
        results[i][-1] = 1.0 #perfect accuracy at full sample        
        for j in range(num_points):
            sample_size = 0.1 + j*sample_interval
            sample = test_data[:int(math.ceil(sample_size*len(test_data)))]
            ranking, full_ranking = predictor.predict(sample, return_full_rank=True)
            est_size = len(ranking)
            
            metrics = evaluate_prediction(suspect_union, test_data, full_ranking, n)
            results[i][j] = metrics[3] # precision at exact k 
            predicted_suspectz[j].append(ranking)
            
    x = np.linspace(10,100,num_points+1)
    results = np.mean(results,axis=0)
    for i in range(num_points):
        print("At %i%% sample: %.3f" %(int(x[i]), results[i]))
        
        
def experiment_train_size(data, suspect_union, args):
    '''
    Evaluate the prediction at various sizes of the training data set. 
    '''
    m = len(data)
    n = len(suspect_union)
    train_fractions = [0.2,0.4,0.6,0.8,1.0]
    date = SuspectPrediction() 
    folds = min(args.folds,m)
    
    for t in train_fractions:
        print("Training size %.1f" %(t))
        fscore_base = np.zeros(m)
        fscore_new = np.zeros(m)
    
        kf = KFold(n_splits=folds, random_state=42, shuffle=False)
        for fold, (train_index,test_index) in enumerate(kf.split(data)):
            if args.verbose:
                print("Running fold %i/%i" %(fold+1,folds))
            all_train_data = [data[i] for i in train_index]
            random.shuffle(all_train_data) 
            l = int(t*len(all_train_data))
            train_data = all_train_data[:l]
            
            # Train
            date.fit(train_data)
            s2v = Suspect2Vec(eta=args.eta, epochs=args.epochs, dim=args.dim, lambd=args.lambd)
            s2v.fit(train_data)
            
            # test & evaluate 
            for i in test_index:
                test_data = data[i]
                if args.sample_type == "random":
                    random.shuffle(test_data)
                sample = test_data[:int(math.ceil(args.sample_size*len(test_data)))]

                pred_base = date.predict(sample)  
                fscore_base[i] = eval_fscore(n, pred_base, test_data)   

                # Prediction using suspect2vec model 
                pred_new = s2v.predict(sample)
                fscore_new[i] = eval_fscore(n, pred_new, test_data)   
        
        print("Base f1-score: %.4f" %(np.mean(fscore_base)))
        print("New f1-score: %.4f" %(np.mean(fscore_new)))
        
       
def experiment_suspect2vec(data, suspect_union, args):
    '''
    Evaluate suspect2vec and compare it to the baseline method
    '''
    m = len(data)
    n = len(suspect_union)
    date = SuspectPrediction(args.prior_var)

    metrics_base = np.zeros((m,4)) # (precision, recall, fscore, size_error)
    metrics_new = np.zeros((m,4))
    
    folds = min(args.folds,m)
    kf = KFold(n_splits=folds, random_state=42, shuffle=False)
    for fold, (train_index,test_index) in enumerate(kf.split(data)):
        #if args.verbose:
        print("Running fold %i/%i" %(fold+1,folds))
        train_data = [data[i] for i in train_index]
        
        # Train models
        date.fit(train_data)
        s2v = Suspect2Vec(eta=args.eta, epochs=args.epochs, dim=args.dim, lambd=args.lambd, train=args.train)
        s2v.fit(train_data)

        # Testing
        res = []
        for i in test_index:
            test_data = data[i]
            if args.sample_type == "random":
                random.shuffle(test_data)
            sample = test_data[:int(math.ceil(args.sample_size*len(test_data)))]

            pred_base = date.predict(sample)  
            metrics_base[i] = eval_pred_v2(n, pred_base, test_data)   

            # Prediction using suspect2vec model 
            pred_new = s2v.predict(sample)
            metrics_new[i] = eval_pred_v2(n, pred_new, test_data)   
            res.append(metrics_new[i][2])
            # TODO: plot suspect embeddings?
            # print len(test_data),len(pred_new),len(pred_base)           
            # if args.verbose:
                # print("test %i base: %s" %(i,metrics_base[i]))
                # print("test %i new: %s" %(i,metrics_new[i]))
        print("f1-score: %.4f" %(np.mean(res)))
                
    metrics_base = np.mean(metrics_base,axis=0)
    metrics_new = np.mean(metrics_new,axis=0)
    print("Base metrics:")
    print("    precision = %.3f" %(metrics_base[0]))
    print("    recall = %.3f" %(metrics_base[1]))
    print("    f1-score = %.3f" %(metrics_base[2]))
    print("    size error = %.3f" %(metrics_base[3]))
    print("New metrics:")
    print("    precision = %.3f" %(metrics_new[0]))
    print("    recall = %.3f" %(metrics_new[1]))
    print("    f1-score = %.3f" %(metrics_new[2]))
    print("    size error = %.3f" %(metrics_new[3]))

            
def main(args):
    design_dir = args.design_dir.rstrip("/") 
    debug_level = args.level
    if not os.path.exists(design_dir):
        raise ValueError("design %s does not exist" %(design_dir))
        return False     
        
    suspect_union = set([]) 
    all_suspectz = []
    all_failurez = []
    num_bugs = 0
    
    # Parse debug reports to extract suspect sets
    print("Reading suspects...")
    for bug_dir in sorted(os.listdir(design_dir)):  
        num_bugs += 1     
        # parse bug module 
        bug_desc = open(os.path.join(design_dir,bug_dir,"bug_desc.txt")).read()
        module = re.search(r"Module:\s+(\w+)",bug_desc).group(1)
        
        for item in sorted(os.listdir(os.path.join(design_dir,bug_dir))):
            fail_dir = os.path.join(design_dir, bug_dir, item)
            if os.path.isdir(fail_dir):                    
                failure = process_report(fail_dir, suspect_union, debug_level)
                if failure is not None:
                    failure.module = module
                    if args.verbose:
                        print("Parsed",failure)
                    all_suspectz.append(failure.suspectz)
                    all_failurez.append(failure)

    suspect_union = list(suspect_union)
    if sys.version_info[0] >= 3:
        suspect_union.sort(key=lambda x: x.id)
    else:
        cmp_by_id = lambda a,b: 0 if a.id == b.id else (-1 if a.id < b.id else 1)
        suspect_union.sort(cmp=cmp_by_id) 

    n = len(suspect_union)
    m = len(all_suspectz)    
    print("Number of bugs: %i" %(num_bugs))
    print("Number of failures: %i" %(m))
    print("Total number of suspects across all bugs: %i" %(n))
    if args.verbose:
        print("Suspect union:")
        for item in suspect_union:
            print(item)
        print("")
        # print "All suspect sets:"
        # for sset in all_suspectz:
            # print sorted(sset)
        # print ""
    
    if args.experiment == "k":
        experiment_k(all_suspectz, suspect_union, args)
    elif args.experiment == "sample_size":
        experiment_sample_size(all_suspectz, suspect_union, args, all_failurez)
    elif args.experiment == "train_size":
        experiment_train_size(all_suspectz, suspect_union, args) 
    elif args.experiment == "suspect2vec":
        experiment_suspect2vec(all_suspectz, suspect_union, args)
    else:
        raise ValueError("Invalid experiment option %s" %(args.experiment))
    
        
def init(parser):
    parser.add_argument("design_dir",help="Design to run")
    parser.add_argument("--experiment",default="suspect2vec",help="Type of evaluation experiment to run on the design." \
        "Must be one of ['k','sample_size','train_size','suspect2vec']")
    parser.add_argument("--level",type=int,default=INF,help="Maximum hierarchical level of suspects to consider. Default is all.")
    parser.add_argument("--sample_size",type=float,default=0.5 ,help="Number of suspects in initial subset (sample) of suspect set that" \
                        " is to be ranking.")
    parser.add_argument("--prior_var",type=float,default=0.2,help="Hyperparameter for prior in MAP estimation")
    parser.add_argument("-v","--verbose",action="store_true",default=False,help="Verbose mode")
    parser.add_argument("--sample_type",default="suffix",help="Strategy to choose an observed suspect sample." \
        "Must be one of ['suffix','random']")
    parser.add_argument("--folds",type=int,default=10)
    parser.add_argument("--epochs",type=int,default=4000)
    parser.add_argument("--eta",type=float,default=0.01,help="Learning rate")
    parser.add_argument("--dim",type=int,default=20,help="Embedding dimension")
    parser.add_argument("--lambd",type=float,default=None,help="Regularization factor")
    parser.add_argument("--train",type=int,default=0,help="Training scheme")
   

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)

    