import os 
import argparse
import random
import time
import re

import run_debug_data
import utils 


def main(args):
    design_dir = args.design_dir.rstrip("/") 
    failurez = utils.find_all_failures(design_dir, include_failed=True) 
    if args.ids:
        ids = utils.parse_ids(args.ids) 
    orig_dir = os.getcwd()

    for f in failurez: 
        pattern = r"%s/((?:random_bug_)|(?:buggy))(\d+)/*" %(design_dir) 
        m = re.match(pattern, f)
        bug_type = m.group(1)
        id = int(m.group(2))

        if (args.bug_type is None or args.bug_type == bug_type) and (args.ids is None or id in ids):
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
                print "" 

                if success:
                    utils.write_suspect_list(f)



def init(parser):
    parser.add_argument("design_dir", help="Directory of design to debug")
    parser.add_argument("--ids", help="Comma-seperated list of indices and index ranges of bugs to debug")
    parser.add_argument("--bug_type", help="buggy, random_bug_, or None")
    parser.add_argument("--window", help="Initial window size")
    parser.add_argument("--dryrun", "-n", action="store_true", default=False, help="Dryrun")
   
   
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)