import os
#import subprocess
import subprocess32 as subprocess
import signal
import argparse
import random
import bug_inject
import re
import run_debug_data
import logging 

MAX_ATTEMPTS = 500
SIM_TIMEOUT = 120
SIM_ERROR_MSGS = [r"\*\* Error:", r"ERROR:", r"Total\s+Error:\s*[123456789]"]
LOG_FILE = "/fs1/eecg/veneris/nveira/directed_debugging/_build_data.log"
    
    
def run_sim(design_dir, dump_vcd=True, timeout=SIM_TIMEOUT):
    '''
    Run "make clean" followed by "make sva" in design_dir/sim.
    Return True if error is detected in simulation output. 
    '''
    logging.debug("Running simulation...")
    prev_dir = os.getcwd()
    os.chdir(os.path.join(design_dir,"sim"))
    subprocess.Popen("make clean", shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).communicate()
    cmd = "make sva DUMP_VCD=%i" %int(dump_vcd)
    try:
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
        stdout, stderr = proc.communicate(None, timeout=timeout)
    except subprocess.TimeoutExpired:
        logging.debug("Simulation exceeded time limit of %is" %(timeout))
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        os.chdir(prev_dir)
        return False
        
    os.chdir(prev_dir)
    #if verbose:
    #    print stdout 
    #check for errors in stdout
    '''for err in SIM_ERROR_MSGS:
        if re.search(err,stdout):
            return True 
    return False '''
    return True
    
    
def copy_golden(dest): 
    os.system("mkdir %s" %(dest))
    for item in ["filelist.l","rtl","tb","sva"]:
        os.system("cp -r golden/%s %s/%s" %(item,dest,item))
    os.system("mkdir %s/sim" %(dest))
    os.system("cp -r golden/sim/Makefile %s/sim/Makefile" %(dest))
     

def main(design, args):
    # Get simulation time factor from design_info.csv 
    design_infox = run_debug_data.load_design_info()
    design_name = os.path.basename(design)
    time_fact = int(design_infox[design_name]["time factor"])
    
    os.chdir(design)
    os.chdir("golden")
    filez = bug_inject.get_files()
    random.shuffle(filez)
    os.chdir("..")    
    dir_idx = 0
    
    # Load list of bugs that have already been tried for this design
    tried_bugs = []
    if os.path.exists("tried_bugs.txt"):
        for line in open("tried_bugs.txt"):
            tried_bugs.append(line.strip())
    
    cnt_success = 0
    i = 0
    for _ in range(MAX_ATTEMPTS):
        if cnt_success >= args.num_bugs:
            break      
        
        # Find available directory name
        while os.path.exists("random_bug_"+str(dir_idx)):
            dir_idx += 1
        bug_dir = "random_bug_"+str(dir_idx)

        logging.info("")
        logging.info("Creating new buggy design directory %s/%s" %(design,bug_dir))     
        copy_golden(bug_dir)
        # os.system("cp -r golden "+bug_dir)
        os.chdir(bug_dir)  
        
        # Inject random bug and check if simulation fails
        sim_failed = False        
        
        attempts = 0 
        f = filez[i%len(filez)] #rotate through the files 
        i += 1
        bug = bug_inject.inject_bug(f, args.bug_type, verbose=args.verbose, blacklist=tried_bugs)
        while not bug and attempts < 20:
            f = filez[i%len(filez)] #rotate through the files 
            i += 1 
            bug = bug_inject.inject_bug(f, args.bug_type, verbose=args.verbose, blacklist=tried_bugs)
            attempts += 1            
        
        if bug:    
            tried_bugs.append(str(bug))
            success = run_sim(".", dump_vcd=True, timeout=args.sim_to)
            
            # Check the whether for any assertion failures or signal differences from golden 
            # in the simulation output
            golden_sim = run_debug_data.get_sim_file("../golden")
            buggy_sim = run_debug_data.get_sim_file(".")
            logging.debug("Checking simulation output for failures")
            failures = run_debug_data.get_failures(buggy_sim, golden_sim, ".*", time_fact=time_fact)
            sim_failed = len(failures) >= 1
            
        os.chdir("..")
            
        if sim_failed:
            cnt_success += 1
            logging.info("Successfully injected bug into file %s" %(f))
            if args.transfer_files:
                logging.debug("Copying files to pczisis")
                cmd = "scp -r %s neil@avgrp-pczisis.eecg.toronto.edu:/home/neil/directed_debugging/%s" %(bug_dir,design)
                subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE).communicate()
                
        else:
            logging.info("Unsuccessful")
            os.system("rm -rf "+bug_dir)  

        # Write out tried_bugs
        with open("tried_bugs.txt","w") as tried_bugs_file:
            for line in tried_bugs:
                tried_bugs_file.write(line+"\n")

    
def init(parser):
    parser.add_argument("design", help="Base design to build buggy designs from")
    parser.add_argument("--num_bugs", type=int, default=1, help="Number of buggy designs to create")
    parser.add_argument("--sim_to", type=int, default=SIM_TIMEOUT, help="simulation timeout in seconds")
    parser.add_argument("--verbose", "-v", action="store_true", default=False)
    parser.add_argument("--bug_type", default="assignment", help="Type of bug to insert." \
        + " Currently supported types: "+str(bug_inject.BUG_TYPEX.keys()))
    parser.add_argument("--transfer_files", action="store_true", default=False, help="Copy files to pczisis after successful bug injection")
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args() 

    logging_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(format='%(asctime)s : %(levelname)s : %(message)s', level=logging_level, filename=LOG_FILE)
    logging.getLogger().setLevel(logging_level)
    logging.getLogger().addHandler(logging.StreamHandler())

    main(args.design.rstrip("/"), args)
