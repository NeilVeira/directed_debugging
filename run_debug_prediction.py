import os 
import argparse
import re
import signal
import random

import utils
import analyze
import run_debug_data 
import train_design 

METHODS = [None, "assump", "optAssump", "assumpBlock", "optAssumpBlock", "optAssumpBlock0", 
            "2pass", None, None, None, 
            "optMulti", "Multi", "Multiv2", "MultiDATE", "MultiOpt",
            ]

def run_debug(name, timeout=60*60*24, verbose=False):
    print "Running debug on %s..." %(name)
    log_file = "onpoint-cmd-%s.log" %(name)
    if os.path.exists(log_file):
        os.remove(log_file)
        
    stdout,stderr = utils.run("onpoint-cmd --template-file=%s.template" %(name), timeout=timeout)    
    
    #check logs for errors
    if not os.path.exists(log_file):
        print "Error:"
        print stdout
        print stderr 
        return False       
        
    log = open(log_file).read()
    if "error:" in log.lower():
        print "vdb failed, check logs"
        return False       

    if stdout == None:
        print "onpoint-cmd exceeded time limit of %i seconds" %(int(timeout))        

    return True 
    
    
def parse_pre_runtime(name):
    log_file = "onpoint-cmd-%s.log" %(name)
    if not os.path.exists(log_file):
        return 0 
    log = open(log_file).read()
    m = re.search(r".*\((\d+):(\d+):(\d+)\) ## Running VDB\.\.\.", log, flags=re.DOTALL)
    if m:
        return 3600*int(m.group(1)) + 60*int(m.group(2)) + int(m.group(3))
    else:
        return 0 
    
    
def main(base_name, new_name=None, min_suspects=999999, aggressiveness=0.5, guidance_method=None, 
    timeout=10800, pass_timeout=100000, verbose=False):
    if not os.path.exists(base_name+".template"):
        raise ValueError("File %s does not exist" %(base_name+".template"))

    dir = os.path.dirname(base_name)    
    orig_dir = os.getcwd()
    suspect_list_file = base_name.replace("designs","suspect_lists") + "_suspects.txt"
    cmd = "cp %s %s/true_suspects.txt" %(suspect_list_file, dir)
    assert os.system(cmd) == 0
    
    if guidance_method == "MultiDATE":
        # Generate and write DATE_info.txt file. Do this only as needed because storing all these 
        # files can take up a lot of space for some designs 
        train_design.train_DATE(base_name) 
        if os.system("mv %s_DATE_info.txt %s/DATE_info.txt" %(base_name,os.path.dirname(base_name)) ) != 0:
            raise Exception("Could not copy DATE_info file into bug directory")
                
    os.chdir(dir)
    base_name = os.path.basename(base_name)
    if new_name:
        new_name = os.path.basename(new_name)
    
    if min_suspects == -1:
        num_true_suspects = len(open("true_suspects.txt").readlines())
        min_suspects = int(0.3*num_true_suspects)
        print "Cheat: Setting min_suspects to",min_suspects

    with open("args.txt","w") as f:
        f.write("%i\n" %(min_suspects))
        f.write("%.3f\n" %(aggressiveness))
        f.write("%i\n" %METHODS.index(guidance_method))
            
    if new_name is None:
        success = run_debug(base_name, timeout=timeout, verbose=verbose)
        os.system("rm args.txt")
        os.chdir(orig_dir)  
        return success
    
    else:         
        print base_name, new_name
        if guidance_method is not None:
            if os.system("cp %s_input_embeddings.txt input_embeddings.txt" %(base_name)) != 0 or \
                os.system("cp %s_output_embeddings.txt output_embeddings.txt" %(base_name)) != 0:
                print "WARNING: Could not copy embeddings file into bug directory" 
                
        assert os.system("cp %s.template %s.template" %(base_name,new_name)) == 0
        
        # Modify template file as needed 
        utils.write_template(new_name+".template", "PROJECT=", "PROJECT="+new_name)
        general_options = run_debug_data.VDB_OPTIONS + " --solver-cpu-limit=%i" %(pass_timeout)
        utils.write_template(new_name+".template", "GENERAL_OPTIONS=", "GENERAL_OPTIONS=\"%s\"" %(general_options))
        utils.write_template(new_name+".template", "VERBOSITY=", "VERBOSITY=debug")
    
        pre_runtime = parse_pre_runtime(base_name)
        if verbose:
            print "Adding %i seconds for pre-vdb operations" %(pre_runtime)
        
        success = run_debug(new_name, timeout=timeout+pre_runtime, verbose=verbose)
        os.system("rm -rf DATE_info.txt")
        os.system("rm args.txt")
        
        if not success:
            os.chdir(orig_dir) 
            return False
                
        assert os.path.exists(new_name+".vennsawork")
        num_suspects = utils.parse_suspects(new_name)
        if len(num_suspects) == 0:
            os.chdir(orig_dir)
            return False 
            
        try:
            analyze.analyze(base_name, new_name, verbose=verbose, min_runtime=0)
        except Exception as e:
            print "analyze failed" 
            print e 
            os.chdir(orig_dir)
            return False 
        
        os.chdir(orig_dir)  
        return True
    
    
def init(parser):
    parser.add_argument("base_name", help="Name of baseline failure.")
    parser.add_argument("new_name", nargs='?', default=None, help="Name of new failure to run. " \
        "If not specified base_name will be run.")
    parser.add_argument("--min_suspects", type=int, default=999999, 
        help="Minimum number of suspects to find before predicting")
    parser.add_argument("--aggressiveness", type=float, default=0.5, help="Threshold below which suspects are blocked")
    parser.add_argument("-v","--verbose", action="store_true", default=False, help="Display more info")
    parser.add_argument("--timeout", type=int, default=10800, help="Time limit in seconds for a single debugging run.")
    parser.add_argument("--pass_timeout", type=int, default=100000, help="Time limit in seconds for a single pass.")
    parser.add_argument("--method", type=str, default=None, help="Solver guidance method. " \
        "Must be one of %s" %METHODS)
   
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args.base_name, args.new_name, args.min_suspects, args.aggressiveness, args.method, args.timeout, 
        args.pass_timeout, args.verbose)