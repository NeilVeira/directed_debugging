import os 
import argparse 
import re
import numpy as np

import utils 
from suspect_prediction.date import DATEPrediction
from suspect_prediction.suspect2vec import Suspect2Vec

    
def load_embeddings(file_name):
    embedx = {}
    for line in open(file_name):
        stuff = line.split()
        embedx[stuff[0]] = np.array(map(float,stuff[1:]))
    return embedx
    
def load_suspects(failure):
    suspect_list = failure.replace("designs","suspect_lists") + "_suspects.txt"
    return [line.strip() for line in open(suspect_list)]
    
    
def simulate_prediction(failure, args):
    if args.verbose:
        print "\nRunning failure",failure
    pieces = failure.split("/")
    design = "/".join(pieces[:-2])
    ground_truth = set(load_suspects(failure))
    
    if args.method != "loaded":
        train_data = []
        for f in utils.find_all_failures(design):
            if f != failure:
                train_data.append(load_suspects(f))
            
    loaded_embed_inx = load_embeddings(failure+"_input_embeddings.txt")
    loaded_embed_outx = load_embeddings(failure+"_output_embeddings.txt")
    known_suspects = set(loaded_embed_inx.keys())
    
    log_file = failure+"_1pass.vennsawork/logs/vdb/vdb.log"
    obs = []
    active = set([])
    suspect_union = set([]) # all suspects modeled in this failure 
    for line in open(log_file):
        m = re.search(r"## suspect: (\S+), output\(s\): \d+, literal: \d+", line)
        if m:
            suspect_union.add(m.group(1))
            if len(obs) < args.min_suspects:
                active.add(m.group(1))
                
        if len(obs) < args.min_suspects:
            m = re.search(r"##  ==> solver solution:  { \S+:(\S+) }", line)
            if m:
                obs.append(m.group(1))
    
    if len(obs) < args.min_suspects:
        if args.verbose:
            print "No prediction (%i suspects)" %(len(obs))
        return 1.0, 1.0, 0        
    
    # print obs
    known_true = ground_truth.intersection(known_suspects)
    true_active = ground_truth.intersection(active)

    # suspect_union = known_suspects.union(active).union(ground_truth) # not quite but probably close 
        
    if args.method == "suspect2vec":
        if args.verbose:
            print "Training..."
        predictor = Suspect2Vec()
        predictor.fit(train_data)
        pred = set(predictor.predict(obs, aggressiveness=args.aggressiveness)) 

    elif args.method == "loaded":
        print obs
        embed_inx = loaded_embed_inx 
        embed_outx = loaded_embed_outx
        v_obs = np.mean([embed_inx[s] for s in obs if s in embed_inx], axis=0)
    
        pred = set(obs)
        for s in suspect_union:
            if s in embed_outx:
                v = embed_outx[s]
                score = 1.0 / (1 + np.exp(-np.sum(v*v_obs)))
                if score >= args.aggressiveness:
                    pred.add(s)
                
    elif args.method.upper() == "DATE":
        if args.verbose:
            print "Training..."
        predictor = DATEPrediction()
        predictor.fit(train_data)
        pred = set(predictor.predict(obs))  
        
    else:
        raise ValueError("Invalid method %s" %(args.method))
    
    # for s in suspect_union:
        # if s not in known_suspects:
            # pred.add(s)
    
    correct = 0
    blocked = set([])
    for s in suspect_union:
        if s not in pred:
            blocked.add(s)
            # assert s in known_suspects
            if s not in true_active:
                correct += 1  
                
    cnt = len(true_active.intersection(pred))
    recall = cnt/float(len(true_active))
    acc =  float(correct)/len(blocked) if len(blocked) > 0 else 1    
    percent_blocked = len(blocked) / float(len(suspect_union))
    
    if args.verbose:
        print "Suspect union:",len(suspect_union)
        print "Active suspects:",len(active)
        print "Ground truth suspects:",len(ground_truth)
        print "True active suspects:",len(true_active)
        print "Known active suspects:", len(active.intersection(known_suspects))
        print "Known true suspects: %i (%.1f%%)" %(len(known_true), float(len(known_true))/len(ground_truth)*100)
        print "Total predicted: %i" %(len(pred))
        print "Total blocked: %i (%.3f)" %(len(blocked),percent_blocked)
        print "Active blocked: %i" %(len(blocked.intersection(active)))
        print "Blocking accuracy: %.3f" %(acc)    
        print "Recall: %.3f" %(recall)
        print "predicted/true: %i/%i" %(len(pred),len(true_active))    
    return acc, recall, percent_blocked
    
            
def main(args):
    if args.failure is not None:
        simulate_prediction(args.failure, args)
    elif args.design is not None:
        metrics = []
        num_failures = 0
        all_failurez = utils.find_all_failures(args.design)
        for failure in all_failurez:
            runtime = utils.parse_runtime(failure)
            if runtime >= args.min_runtime:
                results = simulate_prediction(failure, args)
                if results is not None:
                    num_failures += 1
                    metrics.append(results)
                
        metrics = np.mean(np.array(metrics), axis=0)
        print ""
        print "Number of failures: %i/%i" %(num_failures,len(all_failurez))
        print "Mean block prediction accuracy: %.3f" %(metrics[0])
        print "Mean recall: %.3f" %(metrics[1])
        print "Mean percent blocked: %.3f" %(metrics[2])
        
    else:
        raise ValueError("At least one of --failure or --design must be specified.")
    
    
def init(parser):
    parser.add_argument("--failure", help="Run on this single failure")    
    parser.add_argument("--design", help="Run on all failures in this design and take mean")
    parser.add_argument("--aggressiveness",type=float,default=0.5)
    parser.add_argument("--min_suspects", type=int, default=40, help="Minimum number of suspects to find before predicting")
    parser.add_argument("--min_runtime", type=int, default=1, help="Exclude failures with runtime less than this.")
    parser.add_argument("-v", "--verbose", action="store_true", default=False)
    parser.add_argument("--method", default="loaded", help="Prediction method. Must be one of ['loaded','suspect2vec','DATE'].")
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)