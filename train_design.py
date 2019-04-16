import os 
import argparse 
import sys 
import re

import utils 
from suspect_prediction.suspect2vec import Suspect2Vec
from suspect_prediction.date import DATEPrediction 

    
def write_embeddings(embeddingx, file_name):
    with open(file_name,"w") as f:
        for key in embeddingx:
            f.write(key)
            for x in embeddingx[key]:
                f.write(" %.6f" %(x))
            f.write("\n")
         
def load_data(failure):
    design = "/".join(failure.split("/")[:2])
    all_failurez = utils.find_all_failures(design)
    data = []
    for f in all_failurez:
        if f != failure:
            suspect_list_file = f.replace("designs","suspect_lists")+"_suspects.txt"
            suspectz = open(suspect_list_file).readlines()
            data.append([s.strip() for s in suspectz])
    return data 
    
                
def train_s2v(failure):
    train_data = load_data(failure) 
    predictor = Suspect2Vec(eta=args.eta, epochs=args.epochs, dim=args.dim, lambd=args.lambd)
    predictor.fit(train_data)
    embed_inx, embed_outx = predictor.get_embeddings()
    write_embeddings(embed_inx, failure+"_input_embeddings.txt")
    write_embeddings(embed_outx, failure+"_output_embeddings.txt")
    
    
def train_DATE(failure):
    train_data = load_data(failure) 
    date_pred = DATEPrediction()
    date_pred.fit(train_data)        
    with open(failure+"_DATE_info.txt", "w") as f:
        for s in date_pred.suspect_union:
            f.write(s+" ")
        f.write("\n")
        
        for row in date_pred.weights:
            for x in row:
                f.write("%.9f " %(x))
            f.write("\n")
    
    
def main(args):
    if args.skip_check:
        # search for failures by template file instead of .vennsawork
        all_failurez = []
        for item in sorted(os.listdir(args.design)):
            if item.startswith("random_bug_") or item.startswith("buggy"):             
                for sub_item in sorted(os.listdir(os.path.join(args.design,item))):
                    m = re.match(r"fail_\d+\.template\Z", sub_item)
                    if m:
                        failure_name = os.path.join(args.design, item, sub_item[:-len(".template")])
                        all_failurez.append(failure_name)
    else:
        all_failurez = utils.find_all_failures(args.design)

    for failure in all_failurez:
        print "Training %i failures in leave-one-out" %(len(all_failurez))
        train_DATE(failure)
        if not args.skip_s2v:
            train_s2v(failure)
        

def init(parser):
    parser.add_argument("design")
    parser.add_argument("--skip_check", action="store_true", default=False, \
        help="Skip check for successful debug runs. This should not be used on pczisis.")
    parser.add_argument("--skip_s2v", action="store_true", default=False)

    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)