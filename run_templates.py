import os 
import argparse
import random
import time
import re

import run_debug_data
import utils 
import write_suspect_lists
import run_debug_prediction_wrapper


# fail_list =  '''buggy2/fail_1
                # buggy9/fail_1
                # buggy10/fail_1
                # buggy11/fail_1'''
# failurez = fail_list.split()

def main(args):
    design_dir = args.design_dir.rstrip("/") 
    failurez = utils.find_all_templates(design_dir) 
    orig_dir = os.getcwd()
    
    start = run_debug_prediction_wrapper.find_failure(args.start, failurez) if args.start else 0 
    stop = run_debug_prediction_wrapper.find_failure(args.stop, failurez) if args.stop else len(failurez)-1

    for i in range(start, stop+1):
        f = failurez[i]
        # f = os.path.join(design_dir, f)
        print f 
        template_file = f+".template" 

        # parse out start and finish times so we can vary the window
        found_start = found_end = False 
        for line in open(template_file):
            m = re.match(r"START_TIME=(\d+)ns*", line)
            if m: 
                found_start = True
                start_time = int(m.group(1))
            m = re.match(r"FINISH_TIME=(\d+)ns*", line)
            if m: 
                found_end = True 
                finish_time = int(m.group(1))

        if not found_start or not found_end:
            print "Could not parse start and finish times"
            continue 

        # temporary hack 
        # print "WARNING: setting start time to 0"
        # start_time = 0
        # utils.write_template(template_file, "START_TIME=", "START_TIME=0ns")

        if args.window:
            init_window = int(args.window)
        else:
            init_window = finish_time - start_time  
        project = os.path.basename(f)
        
        if not args.dryrun:
            os.chdir(os.path.dirname(f))
            success = run_debug_data.run_window_debug(project, init_window, finish_time)    
            os.chdir(orig_dir) 

            if success:
                write_suspect_lists.do(f)
            print "" 


def init(parser):
    parser.add_argument("design_dir", help="Directory of design to debug")
    parser.add_argument("--window", help="Initial window size")
    parser.add_argument("--dryrun", "-n", action="store_true", default=False, help="Dryrun")
    parser.add_argument("--start",help="Failure (suffix) to start running at")
    parser.add_argument("--stop",help="Failure (suffix) to stop running at")
   
   
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)