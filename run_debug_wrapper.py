import os 
import argparse
import random
import time
import run_debug_data
import re


def main(design_dir, args):
    if args.buggy:
        bug_dir_start = "buggy"
    else:
        bug_dir_start = "random_bug_"
            
    if args.ids == None:
        ids_to_debug = []
        for item in os.listdir(design_dir):
            if item.startswith(bug_dir_start):
                ids_to_debug.append(int(item[len(bug_dir_start):]))
        
    else:
        ids_to_debug = []
        for item in args.ids.split(","):
            if "-" in item:
                begin,end = item.split("-")[:2]
                ids_to_debug.extend(range(int(begin),int(end)+1))
            else:
                ids_to_debug.append(int(item))
                
    ids_to_debug.sort()
    for i in xrange(len(ids_to_debug)):
        if i == 0 or ids_to_debug[i] != ids_to_debug[i-1]:
            id = ids_to_debug[i]
            dir = os.path.join(design_dir, bug_dir_start+str(id))
            if os.path.exists(dir):
                cmd = "python run_debug_data.py %s --max_fails=%i --min_window=%i" %(dir, args.max_fails, args.min_window)
                if args.xabr:
                    cmd += " --xabr"
                if args.dryrun:
                    cmd += " --dryrun"
                if args.overwrite:
                    cmd += " --overwrite"
                if args.show:
                    cmd += " -s"
                print cmd
                os.system(cmd)
                print "\n"
         
   
def init(parser):
    parser.add_argument("design_dir",help="Directory of design to debug")
    parser.add_argument("--ids",help="Comma-seperated list of indices of random_bug_* directories to debug")
    parser.add_argument("--xabr",action="store_true",default=False,help="Don't use abr strategy")
    parser.add_argument("--overwrite",action="store_true",default=False,help="Delete any pre-existing template file")
    parser.add_argument("--max_fails",type=int,default=1,help="Number of distinct failures to debug")
    parser.add_argument("--buggy",action="store_true",default=False,help="Run buggy* designs rather than random_bug*")
    parser.add_argument("-n","--dryrun",action="store_true",default=False,\
                        help="Set up template file but don't run it")
    parser.add_argument("-s", "--show", action="store_true", default=False, help="Show failures but don't do anything")
    parser.add_argument("--min_window", type=int, default=1000, help="Size in ns of smallest (initial) debug window")
   
   
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args.design_dir, args)
    
    