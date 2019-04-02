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

    print "Training %i failures in leave-one-out" %(len(all_failurez))
    all_suspectz = []
    for failure in all_failurez:
        suspect_list_file = failure.replace("designs","suspect_lists")+"_suspects.txt"
        suspectz = open(suspect_list_file).readlines()
        all_suspectz.append([s.strip() for s in suspectz])
    
    date_pred = DATEPrediction()
        
    for i,failure in enumerate(all_failurez):
        print failure
        train_data = all_suspectz[:i] + all_suspectz[i+1:]
        
        if not args.skip_s2v:
            predictor = Suspect2Vec(eta=args.eta, epochs=args.epochs, dim=args.dim, lambd=args.lambd)
            predictor.fit(train_data)
            embed_inx, embed_outx = predictor.get_embeddings()
            write_embeddings(embed_inx, failure+"_input_embeddings.txt")
            write_embeddings(embed_outx, failure+"_output_embeddings.txt")
            # predictor.save(failure+".suspect2vec.pkl")
        
        # DATE training
        date_pred.fit(train_data)        
        with open(failure+"_DATE_info.txt", "w") as f:
            for s in date_pred.suspect_union:
                f.write(s+" ")
            f.write("\n")
            
            for row in date_pred.weights:
                for x in row:
                    f.write("%.9f " %(x))
                f.write("\n")
        

def init(parser):
    parser.add_argument("design")
    parser.add_argument("--skip_check", action="store_true", default=False, \
        help="Skip check for successful debug runs. This should not be used on pczisis.")
    parser.add_argument("--epochs", type=int, default=4000)
    parser.add_argument("--eta", type=float, default=0.01, help="Learning rate")
    parser.add_argument("--dim", type=int, default=20, help="Embedding dimension")
    parser.add_argument("--lambd", type=float, default=0, help="Regularization factor")
    parser.add_argument("--skip_s2v", action="store_true", default=False)

    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)