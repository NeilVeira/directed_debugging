import os 
import argparse
import numpy as np
import pandas as pd 

import utils
import experiment_prediction

INF = 1e12

def fill_row(row, metrics):
    mean_metrics = np.mean(metrics, axis=0)
    median_metrics = np.median(metrics, axis=0)
    names = ["precision","recall","fscore","auprc","size_err"]
    for i in range(5):
        row["mean_"+names[i]] = mean_metrics[i]
        row["median_"+names[i]] = median_metrics[i]
        

def main(args):
    assert args.sample_type in ["random","solver"]
    
    data_file = "raw_results.csv"
    if os.path.exists(data_file):
        # append to existing data
        data = pd.read_csv(data_file, index_col=0)
    else:
        data = pd.DataFrame(
            columns=["design","predictor","sample_type","sample_size","train_size","folds","dim",
                    "mean_precision","mean_recall","mean_fscore","mean_auprc","mean_size_err",
                    "median_precision","median_recall","median_fscore","median_auprc","median_size_err",
                    ]
        )
        
    args.models = args.models.split(",")
    
    if args.train_test_split == "leave-one-out":
        args.folds = experiment_prediction.INF 
        args.train_test_split = "folds"
        
    row_common = {"sample_type":args.sample_type, "sample_size":args.sample_size, "folds":args.folds}
    if args.train_test_split == "folds":
        row_common["folds"] = args.folds 
    else: 
        row_common["train_size"] = args.train_test_split
    
    for design in args.designs.split(","):
        design_dir = "suspect_lists/"+design.strip()
        args.design_dir = design_dir
        print design_dir     
        all_results = experiment_prediction.main(args)
        
        row_common["design"] = design
        
        for i,model in enumerate(args.models):
            row = dict(row_common)
            row.update({"predictor":model.lower()})
            fill_row(row, all_results[i])
            data = data.append(row, ignore_index=True)
        
        data.to_csv(data_file)
        
    data.drop_duplicates(subset=["design","predictor","sample_type","train_size","sample_size","folds","dim"], inplace=True, keep="last")
    data.sort_values(by=["sample_size","train_size","sample_type","folds","design","predictor","dim"], inplace=True)
    data.reset_index(drop=True, inplace=True)
    data.to_csv(data_file)
        

def init(parser):
    parser.add_argument("designs",help="Comma-separated list of designs to run")
    parser.add_argument("models", help="List of models to run")
    parser.add_argument("--train_test_split", default="folds", help="Strategy to use for generating train and test " \
                        "splits. Must be one of ['leave-one-out', 'folds', 'random-to-buggy'] or whole number.")
    parser.add_argument("--sample_size", type=float,default=0.5, help="Number of suspects in initial subset (sample) of suspect set " \
                        "that is to be ranking.")
    parser.add_argument("--sample_type", default="solver", help="Method to choose observed suspect set. 'random' for random or "
                        "'solver' for order in which the solver finds them.")
    parser.add_argument("--verbosity", "-v", type=int, default=0, help="Verbosity level")
    parser.add_argument("--prior_var", type=float, default=0.2, help="Hyperparameter for prior in MAP estimation")
    parser.add_argument("--folds", type=int, default=INF)
    parser.add_argument("--epochs", type=int, default=4000)
    parser.add_argument("--eta", type=float, default=0.01, help="Learning rate")
    parser.add_argument("--dim", type=int, default=20, help="Embedding dimension")
    parser.add_argument("--delta", type=int, default=60, help="Denominator in smoothing width")
   

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)