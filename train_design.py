import os 
import argparse 
import sys 

import utils 
from suspect_prediction.suspect2vec import Suspect2Vec

def init(parser):
    parser.add_argument("design")
    
    
def write_embeddings(embeddingx, file_name):
    with open(file_name,"w") as f:
        for key in embeddingx:
            f.write(key)
            for x in embeddingx[key]:
                f.write(" %.6f" %(x))
            f.write("\n")
                
    
def main(args):
    all_failurez = utils.find_all_failures(args.design)
    all_suspectz = []
    for failure in all_failurez:
        suspect_list_file = failure.replace("designs","suspect_lists")+"_suspects.txt"
        suspectz = open(suspect_list_file).readlines()
        all_suspectz.append([s.strip() for s in suspectz])
    
    for i in range(len(all_failurez)):
        print all_failurez[i]
        train_data = all_suspectz[:i] + all_suspectz[i+1:]
        predictor = Suspect2Vec()
        predictor.fit(train_data)
        embed_inx, embed_outx = predictor.get_embeddings()
        write_embeddings(embed_inx, all_failurez[i]+"_input_embeddings.txt")
        write_embeddings(embed_outx, all_failurez[i]+"_output_embeddings.txt")
        
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    
    init(parser)
    args = parser.parse_args()
    main(args)