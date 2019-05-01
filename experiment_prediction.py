import os 
import argparse
import re
import random
import math
import numpy as np
import sklearn.metrics
from sklearn.model_selection import KFold 

import utils 
from suspect_prediction.date import DATEPrediction
from suspect_prediction.suspect2vec import Suspect2Vec
from suspect_prediction.naive import RandomPrediction 
from suspect_prediction.naive import NaivePrediction 

INF = 1e12
        
def eval_pred(pred, scores, target, n):
    y_true = np.zeros(n, dtype=np.bool_)
    y_true[target] = 1
    y_pred = np.zeros(n, dtype=np.bool_)
    y_pred[pred] = 1 

    precision, recall, fscore, support = sklearn.metrics.precision_recall_fscore_support(y_true, y_pred, labels=[0,1])
    size_err = abs(len(target)-len(pred)) / float(len(target))    
    
    auprc = sklearn.metrics.average_precision_score(y_true, scores)
    return precision[1], recall[1], fscore[1], auprc, size_err             
        
        
def run_train_test(model, data, train_index, test_index, results, n, args):
    train_data = [data[i] for i in train_index]
    model.fit(train_data)
        
    # Testing
    for i in test_index:
        assert i not in train_index 
        test_data = data[i]
        if args.sample_type == "random":
            random.shuffle(test_data)
        sample = test_data[:int(math.ceil(args.sample_size*len(test_data)))] 
        assert len(sample) > 0 
            
        pred, scores = model.predict(sample, score_query=range(n))
        assert len(scores) == n                 
        
        sample_scores = [scores[j] for j in sample]
        non_sample_scores = [scores[j] for j in range(n) if j not in sample]
        assert min(sample_scores) >= max(non_sample_scores)
                
        results[i] = eval_pred(pred, scores, test_data, n)  
            
        if args.verbosity >= 1:   
            print "%s f1-score:         %.9f" %(type(model).__name__.ljust(20), results[i][2])
            print "%s auc-pr:         %.9f" %(type(model).__name__.ljust(20), results[i][3])
    

def run_all(data, train_index, test_index, all_results, n, date, args):
    for i,model_name in enumerate(args.models):
        if model_name.lower() == "date":
            model = date 
            
        elif model_name.lower() in ["s2v","suspect2vec"]:
            model = Suspect2Vec(eta=args.eta, epochs=args.epochs, dim=args.dim)
            
        elif model_name.lower() == "random":
            model = RandomPrediction()
            
        elif model_name.lower() == "naive":
            model = NaivePrediction()
            
        else:
            raise ValueError("Unknown model %s" %(model_name))            
        
        run_train_test(model, data, train_index, test_index, all_results[i], n, args)


def experiment(data, suspect_union, args, all_failurez):
    '''
    Evaluate suspect2vec and compare it to the baseline method
    '''
    m = len(data)
    n = len(suspect_union)
    date = DATEPrediction(args.prior_var, args.delta) # Instantiate it once to save time precomputing MAP weights

    all_results = np.zeros((len(args.models), m, 5)) # (precision, recall, fscore, auprc, size_error)
    
    if args.train_test_split == "leave-one-out":
        args.train_test_split = "folds"
        args.folds = INF 
    
    if args.train_test_split == "folds":    
        folds = min(args.folds, m)
        kf = KFold(n_splits=folds, random_state=42, shuffle=False)
        
        for fold, (train_index,test_index) in enumerate(kf.split(data)):
            if args.verbosity >= 1:
                print "Running fold %i/%i" %(fold+1,folds)
                
            run_all(data, train_index, test_index, all_results, n, date, args)
            
            
    elif args.train_test_split == "random-to-buggy":
        # Divide among random and buggy failures 
        train_index = []
        test_index = []
        for i in range(m):
            if "/random_bug_" in all_failurez[i]:
                train_index.append(i)
            elif "/buggy" in all_failurez[i]:
                test_index.append(i)                
        # for i in test_index:
            # print i,all_failurez[i]
          
        if len(test_index) == 0:
            print "WARNING: No buggy data found"
            return all_results
            
        if args.verbosity >= 1:
            print "Running random-to-buggy on %i random failures to %i buggy failures" %(len(train_index), len(test_index))
        run_all(data, train_index, test_index, all_results, n, date, args)
        
        # Remove the slots for random bugs from results since we don't evaluate those 
        compressed_results = np.zeros((len(args.models), len(test_index), 5))
        for i in range(len(args.models)):
            compressed_results[i] = np.zeros((len(test_index),5))
            for j,test_idx in enumerate(test_index):
                compressed_results[i][j] = all_results[i][test_idx]
        all_results = compressed_results
        
        
    elif args.train_test_split == "random-vs-buggy":
        train_size = m-1         
        random_results = []
        buggy_results = []
        
        for i in range(m):        
            if args.verbosity >= 1:
                print "Testing on failure %i/%i" %(i+1,m)
                print all_failurez[i] 
                
            # Generate train training data as a random subset of data excluding i 
            train_index = range(m)
            random.shuffle(train_index)
            
            # Make sure i is excluded 
            j = train_index.index(i)
            if j < train_size:
                train_index[j], train_index[-1] = train_index[-1], train_index[j]
                
            run_all(data, train_index[:train_size], [i], all_results, n, date, args)
            
            if "random_bug" in all_failurez[i]:
                random_results.append(all_results[:,i,:])
            else:
                buggy_results.append(all_results[:,i,:])

        print np.mean(random_results, axis=0)
        print np.mean(buggy_results, axis=0)
    
    else:
        # Assume train_test_split indicates the number of data points to use for training 
        train_size = min(int(args.train_test_split), m-1)
        assert train_size > 0
        
        for i in range(m):
            if args.verbosity >= 1:
                print "Testing on failure %i/%i" %(i+1,m)
            # Generate train training data as a random subset of data excluding i 
            train_index = range(m)
            random.shuffle(train_index)
            
            # Make sure i is excluded 
            j = train_index.index(i)
            if j < train_size:
                train_index[j], train_index[-1] = train_index[-1], train_index[j]
                
            run_all(data, train_index[:train_size], [i], all_results, n, date, args)
    
                
    mean_results = np.mean(all_results, axis=1) 
    median_results = np.median(all_results, axis=1) 
    
    if args.verbosity >= 1:
        for i,model in enumerate(args.models):
            print "%s metrics:" %(model)
            print("    precision = %.3f" %(mean_results[i][0]))
            print("    recall = %.3f" %(mean_results[i][1]))
            print("    f1-score = %.3f" %(mean_results[i][2]))
            print("    AUC-PR = %.3f" %(mean_results[i][3]))
    
    return all_results

            
def main(args):
    design_dir = args.design_dir.rstrip("/") 
    if not os.path.exists(design_dir):
        raise ValueError("design %s does not exist" %(design_dir))
        return False  

    if type(args.models) == str:
        args.models = args.models.split(",")
        
    all_failurez = []
    suspect_union = set([]) 
    data = []
    for item in os.listdir(design_dir):
        for failure in os.listdir(os.path.join(design_dir,item)):
            failure = os.path.join(design_dir,item,failure)
            if os.path.isfile(failure):
                all_failurez.append(failure)
                suspectz = [line.strip() for line in open(failure)]
                data.append(suspectz)
                suspect_union = suspect_union.union(set(suspectz)) 

    all_suspectz = list(suspect_union)
    all_suspectz.sort()
    suspect2id = dict(zip(all_suspectz,range(len(all_suspectz))))
    for i in range(len(data)):
        data[i] = [suspect2id[s] for s in data[i]]

    n = len(suspect_union)
    m = len(data)    
    if args.verbosity >= 1:
        print("Number of failures: %i" %(m))
        print("Total number of suspects across all bugs: %i" %(n))
    if args.verbosity >= 2:
        print("Suspect union:")
        for item in suspect_union:
            print(item)
        print("")
    
    return experiment(data, suspect_union, args, all_failurez)
    
        
def init(parser):
    parser.add_argument("design_dir", help="Path to design to run")
    parser.add_argument("models", help="List of models to run")
    parser.add_argument("--train_test_split", default="folds", help="Strategy to use for generating train and test " \
                        "splits. Must be one of ['leave-one-out', 'folds', 'random-to-buggy'] or whole number.")
    parser.add_argument("--sample_size", type=float, default=0.5, help="Fraction of suspects in initial subset (sample) of " \
                        "suspect set that is to be ranked.")
    parser.add_argument("--sample_type", default="solver", help="Method to choose observed suspect set. 'random' for "
                        "random or 'solver' for order in which the solver finds them.")
    parser.add_argument("--prior_var", type=float, default=0.2, help="Hyperparameter for prior in MAP estimation")
    parser.add_argument("--verbosity", "-v", type=int, default=0, help="Verbosity level")
    parser.add_argument("--folds", type=int, default=INF)
    parser.add_argument("--epochs", type=int, default=4000)
    parser.add_argument("--eta", type=float, default=0.01, help="Learning rate")
    parser.add_argument("--dim", type=int, default=20, help="Embedding dimension")
    parser.add_argument("--delta", type=int, default=60, help="Denominator in smoothing width")
    # parser.add_argument("--lambd", type=float, default=0, help="Regularization factor")
   

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)

      