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


def experiment_suspect2vec(data, suspect_union, args, all_failurez):
    '''
    Evaluate suspect2vec and compare it to the baseline method
    '''
    m = len(data)
    n = len(suspect_union)
    date = DATEPrediction(args.prior_var)

    metrics_base = np.zeros((m,5)) # (precision, recall, fscore, auprc, size_error)
    metrics_new = np.zeros((m,5))
    
    folds = min(args.folds,m)
    kf = KFold(n_splits=folds, random_state=42, shuffle=False)
    for fold, (train_index,test_index) in enumerate(kf.split(data)):
        if args.verbosity >= 1:
            print("Running fold %i/%i" %(fold+1,folds))
        train_data = [data[i] for i in train_index]
        
        # Train models
        date.fit(train_data)
        # if args.load_pretrain:
            # if args.verbosity >= 1:
                # print "Loading pretrained model"
            # fname = all_failurez[i].replace("suspect_lists","designs")[:-len("_suspects.txt")] + ".suspect2vec.pkl"
            # s2v = Suspect2Vec.load(fname)
        # else:
        s2v = Suspect2Vec(eta=args.eta, epochs=args.epochs, dim=args.dim, lambd=args.lambd)
        s2v.fit(train_data)

        # Testing
        new = []
        base = []
        for i in test_index:
            test_data = data[i]
            if args.sample_type == "random":
                random.shuffle(test_data)
            sample = test_data[:int(math.ceil(args.sample_size*len(test_data)))] 
                
            pred_base, scores = date.predict(sample, score_query=range(n))
            assert len(scores) == n                 
            metrics_base[i] = eval_pred(pred_base, scores, test_data, n)  
            base.append(metrics_base[i][2])

            # Prediction using suspect2vec model 
            pred_new, scores = s2v.predict(sample, score_query=range(n))
            assert len(scores) == n 
            metrics_new[i] = eval_pred(pred_new, scores, test_data, n)   
            new.append(metrics_new[i][2])
            # print len(test_data),len(pred_new),len(pred_base)  
            
            if args.verbosity >= 2:
                print("failure %s metrics" %(all_failurez[i]))
                print("\tbase: %s" %(metrics_base[i]))
                print("\tnew: %s" %(metrics_new[i]))
                
        if args.verbosity >= 1:    
            print("DATE f1-score:         %.9f" %(np.mean(base)))
            print("suspect2vec f1-score:  %.9f" %(np.mean(new)))
                
    mean_metrics_base = np.mean(metrics_base,axis=0)
    mean_metrics_new = np.mean(metrics_new,axis=0)
    median_metrics_base = np.median(metrics_base,axis=0)
    median_metrics_new = np.median(metrics_new,axis=0)
    if args.verbosity >= 1:
        print("DATE metrics:")
        print("    precision = %.3f" %(mean_metrics_base[0]))
        print("    recall = %.3f" %(mean_metrics_base[1]))
        print("    f1-score = %.3f" %(mean_metrics_base[2]))
        print("    AUC-PR = %.3f" %(median_metrics_base[3]))
        print("suspect2vec metrics:")
        print("    precision = %.3f" %(mean_metrics_new[0]))
        print("    recall = %.3f" %(mean_metrics_new[1]))
        print("    f1-score = %.3f" %(mean_metrics_new[2]))
        print("    AUC-PR = %.3f" %(median_metrics_new[3]))
    
    return metrics_base, metrics_new


            
def main(args):
    design_dir = args.design_dir.rstrip("/") 
    if not os.path.exists(design_dir):
        raise ValueError("design %s does not exist" %(design_dir))
        return False     
        
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
    
    return experiment_suspect2vec(data, suspect_union, args, all_failurez)
    
        
def init(parser):
    parser.add_argument("design_dir", help="Path to design to run")
    parser.add_argument("--sample_size", type=float,default=0.5, help="Fraction of suspects in initial subset (sample) of suspect set that" \
                        " is to be ranking.")
    parser.add_argument("--sample_type", default="solver", help="Method to choose observed suspect set. 'random' for random or "
                        "'solver' for order in which the solver finds them.")
    parser.add_argument("--prior_var", type=float, default=0.2, help="Hyperparameter for prior in MAP estimation")
    parser.add_argument("--verbosity", "-v", type=int, default=1, help="Verbosity level")
    parser.add_argument("--folds" ,type=int, default=INF)
    parser.add_argument("--epochs", type=int, default=4000)
    parser.add_argument("--eta", type=float, default=0.01, help="Learning rate")
    parser.add_argument("--dim", type=int, default=20, help="Embedding dimension")
    parser.add_argument("--lambd", type=float, default=None, help="Regularization factor")
    parser.add_argument("--load_pretrain", action="store_true", default=False, 
        help="Load suspect2vec model from disk rather than retraining")
   

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)

      