import os 
import argparse
import re 

import utils


def parse_suspects_from_log(log_file):
    suspectz = []
    if os.path.exists(log_file):
        for line in open(log_file):
            pattern = r"##  ==> solver solution:  .*:([\w/]+)"
            m = re.search(pattern,line)
            if m:
                s = m.group(1)
                if s not in suspectz:
                    suspectz.append(s)
    return suspectz


def merge_suspect_lists(A,B):
    for s in B:
        if s not in A:
            A.append(s)
    return A 


def do(failure, suffix=""): 
    ordered_suspectz = []
    for i in range(1,100):
        log_file = failure+suffix+".vennsawork/logs/abr%s/vdb.log" %(str(i).zfill(3))
        # print log_file
        ordered_suspectz_file = parse_suspects_from_log(log_file)
        ordered_suspectz = merge_suspect_lists(ordered_suspectz, ordered_suspectz_file)

    log_file = failure+suffix+".vennsawork/logs/vdb/vdb.log"
    ordered_suspectz_file = parse_suspects_from_log(log_file)
    ordered_suspectz = merge_suspect_lists(ordered_suspectz, ordered_suspectz_file)
    print "Number of suspects found by solver:",len(ordered_suspectz)

    # add suspects from vennsa.stdb.gz of base debugging instance in case some are missed. 
    stdb_suspects = utils.parse_suspects(failure)        
    print "Suspects in %s.vennsawork/vennsa.stdb.gz: %i" %(failure,len(stdb_suspects))
    merge_suspect_lists(ordered_suspectz, stdb_suspects)
    print "Total number of suspects:",len(ordered_suspectz)
    
    with open("suspects.txt","w") as f:
        for s in ordered_suspectz:
            f.write(s+"\n")
    utils.copy_file("suspects.txt", failure.replace("designs","suspect_lists")+"_suspects.txt", verbose=False)
    
def main(args):   
    for failure in utils.find_all_failures(args.design):
        print "Failure",failure 
        do(failure, args.suffix)         
    
    
def init(parser):
    parser.add_argument("design")
    parser.add_argument("suffix", nargs='?', default="", help="Suffix to append to the name of the project")
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)
