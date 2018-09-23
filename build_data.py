import os
#import subprocess
import subprocess32 as subprocess
import signal
import argparse
import random
import bug_inject
import re
import run_debug

MAX_ATTEMPTS = 500
SIM_TIMEOUT = 120
SIM_ERROR_MSGS = [r"\*\* Error:", r"ERROR:", r"Total\s+Error:\s*[123456789]"]
    
    
def run_sim(design_dir, dump_vcd=True, timeout=SIM_TIMEOUT, verbose=False):
    '''
    Run "make clean" followed by "make sva" in design_dir/sim.
    Return True if error is detected in simulation output. 
    '''
    if verbose:
        print "Running simulation..."
    prev_dir = os.getcwd()
    os.chdir(os.path.join(design_dir,"sim"))
    proc = subprocess.Popen("make clean", shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    proc.communicate()
    cmd = "make sva DUMP_VCD=%i" %int(dump_vcd)
    try:
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
        stdout, stderr = proc.communicate(None, timeout=timeout)
    except subprocess.TimeoutExpired:
        if verbose:
            print "Simulation exceeded time limit of %is" %(timeout) 
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
     

def main(design, args):
    os.chdir(design)
    os.chdir("golden")
    filez = bug_inject.get_files()
    random.shuffle(filez)
    os.chdir("..")    
    dir_idx = 0
    
    #load list of bugs that have already been tried for this design
    tried_bugs = []
    if os.path.exists("tried_bugs.txt"):
        for line in open("tried_bugs.txt"):
            tried_bugs.append(line.strip())
    
    cnt_success = 0
    i = 0
    while cnt_success < args.num_bugs and i < MAX_ATTEMPTS:
        f = filez[i%len(filez)] #rotate through the files
        i += 1
        log = open("/fs1/eecg/veneris/nveira/suspect_prediction/build_data.log","a")        
        
        #find available directory name
        while os.path.exists("random_bug_"+str(dir_idx)):
            dir_idx += 1
        bug_dir = "random_bug_"+str(dir_idx)
        print "Creating new buggy design directory %s" %(bug_dir)
        log.write("Creating new buggy design directory %s\n" %(bug_dir))
        
        #inject random bug and check if simulation fails
        sim_failed = False        
        
        # TODO: do not copy, do not copy sva and tb - just create symlinks 
        os.system("cp -r golden "+bug_dir)
        os.chdir(bug_dir)    
        bug = bug_inject.inject_bug(f, args.bug_type, verbose=args.verbose, blacklist=tried_bugs, log=log)
        if bug != None:    
            tried_bugs.append(str(bug))
            success = run_sim(".", dump_vcd=True, timeout=args.sim_to, verbose=args.verbose)
            
            #check the whether for any assertion failures or signal differences from golden 
            #in the simulation output
            golden_sim = run_debug.get_sim_file("../golden")
            buggy_sim = run_debug.get_sim_file(".")
            if args.verbose:
                print "Checking simulation output for failures"
                log.write("Checking simulation output for failures\n")
            failures = run_debug.get_failures(buggy_sim, golden_sim, ".*", time_fact=args.time_fact)
            sim_failed = len(failures) >= 1
            
        os.chdir("..")
        
        #write out tried_bugs
        tried_bugs_file = open("tried_bugs.txt","w")
        for line in tried_bugs:
            tried_bugs_file.write(line+"\n")
        tried_bugs_file.close()
            
        if sim_failed:
            cnt_success += 1
            print "Successfully injected bug into file %s" %(f)
            log.write("Successfully injected bug into file %s\n" %(f))
            if args.verbose:
                print "Copying files to pczisis"
                log.write("Copying files to pczisis\n")
            cmd = "scp -r %s neil@avgrp-pczisis.eecg.toronto.edu:/home/neil/Suspect2vec-ASPDAC19/%s" %(bug_dir,design)
            proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE)
            proc.communicate()
        else:
            print "Unsuccessful"
            log.write("Unsuccessful\n")
            os.system("rm -rf "+bug_dir)  
            
        print ""
        log.write("\n")
        log.close()

    if i == MAX_ATTEMPTS:
        print "Unable to produce %i bugs after %i attempts. Giving up." %(args.num_bugs,i)

    
def init(parser):
    parser.add_argument("design",help="Base design to build buggy designs from")
    parser.add_argument("--num_bugs",type=int,default=1,help="Number of buggy designs to create")
    parser.add_argument("--sim_to",type=int,default=SIM_TIMEOUT,help="simulation timeout")
    parser.add_argument("--verbose","-v",action="store_true",default=False)
    parser.add_argument("--bug_type",default="assignment",help="Type of bug to insert." \
        + " Currently supported types: "+str(bug_inject.BUG_TYPEX.keys()))
    parser.add_argument("--time_fact",type=int,default=1,help="Conversion ratio from simulation time to ns")
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args() 
    main(args.design.rstrip("/"), args)
