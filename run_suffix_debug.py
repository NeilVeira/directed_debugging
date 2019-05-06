import os 
import argparse
import re
import subprocess32 as subprocess
import signal
import random

import utils
import analyze 
import run_debug_prediction

def find_failure(failure, all_failurez):
    for i in range(len(all_failurez)):
        if all_failurez[i].endswith(failure):
            return i 
    else:
        raise ValueError("No failure %s found" %(failure))
        
        
def count_suspects(failure):
    report_file = failure + ".vennsawork/vennsa.stdb.gz"    
    if not os.path.exists(report_file):
        print "stdb report not found" 
        return 0 
    else:
        cmd = "stdb " + report_file
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
        report, _ = proc.communicate(None)
    
    suspect_cnt = 0
    for suspect in re.findall(r"rtl\s+[\w/]+\s+\w+\s+([\w\./]+)\s+([\d\.]+)\s+([\d\.]+)", report, flags=re.DOTALL):
        suspect_cnt += 1 
    return suspect_cnt
        
    
def run_suffix_instance(failure, window, start_time, end_time, id):
    window = max(window, 40)
    print "Truncating debug window from %i to %i" %(end_time-start_time, window)
    new_start = end_time - window 
    
    new_name = "%s_suffix_%i" %(failure,id)
    new_template = new_name + ".template" 
    assert os.system("cp %s.template %s" %(failure, new_template)) == 0
    utils.write_template(new_template, "PROJECT=", "PROJECT="+os.path.basename(new_name))
    utils.write_template(new_template, "START_TIME=", "START_TIME=%ins" %(new_start))
    
    success = run_debug_prediction.run_debug(new_name, timeout=3*60*60)
    if success:
        print "Vdb successful" 
        total = count_suspects(failure)
        cnt = count_suspects(new_name)
        print "%i/%i suspects found in suffix instance" %(cnt,total) 
        return cnt 
    else:
        print "Vdb failed" 
    
    
def main(args):
    design = args.design 
    all_failurez = utils.find_all_failures(design, include_failed=False)
    if args.start is not None:
        start = find_failure(args.start, all_failurez)
    else:
        start = 0
    if args.stop is not None:
        stop = find_failure(args.stop, all_failurez)
    else:
        stop = len(all_failurez)-1
        
    orig_dir = os.getcwd() 
        
    for i in range(start, stop+1):
        failure = all_failurez[i]
        if os.path.exists(failure+"_1pass.vennsawork/logs/vdb/vdb.log"):
            start_time,end_time,_ = analyze.parse_start_end_time(failure+"_1pass")
            if start_time:
                runtime = end_time - start_time 
            else:
                runtime = 0
            
        else: 
            runtime = utils.parse_runtime(failure) 
            
        if runtime < 900:
            continue 
        
        print "Running failure",failure 
        os.chdir(os.path.dirname(failure))
        failure = os.path.basename(failure)
        
        template = failure + ".template"
        contents = open(template).read() 
        m = re.search(r"START_TIME=(\d+)ns", contents)
        start_time = int(m.group(1))
        m = re.search(r"FINISH_TIME=(\d+)ns", contents)
        end_time = int(m.group(1))
        window = end_time - start_time 
        
        total = count_suspects(failure) 
        
        window1 = random.randint(window/5, window/3)
        cnt1 = run_suffix_instance(failure, window1, start_time, end_time, 1)
        
        if cnt1 >= 0.4*total: 
            # try to go smaller  
            window2 = random.randint(window/10, window1/2)       
        else:
            # try to go larger
            window2 = random.randint(window/3, 3*window/4)
        cnt2 = run_suffix_instance(failure, window2, start_time, end_time, 2)

        if cnt1 >= 0.7*total:
            assert window2 <= window1 
            if cnt2 >= 0.4*total:
                # try hard to go smaller 
                window3 = random.randint(40, max(40,3*window2/4))
            else:
                # try for somewhere in between 
                window3 = random.randint(window2+(window1-window2)/3, window1-(window1-window2)/3)
                
        elif cnt1 >= 0.4*total:
            assert cnt2 <= cnt1 
            # try to go larger 
            window3 =  random.randint(2*window1/3, 3*window/4)
            
        else:
            assert window2 >= window1 
            if cnt2 <= 0.6*total:
                # try hard to go larger 
                window3 = random.randint(4*window2/3, window)
            else:
                # try for somewhere in between 
                window3 = random.randint(window1+(window2-window1)/3, window2-(window2-window1)/3)
        
        cnt3 = run_suffix_instance(failure, window3, start_time, end_time, 3)   
        
        os.chdir(orig_dir)
        print "" 
   
   
def init(parser):
    parser.add_argument("design")
    parser.add_argument("--start",help="Failure (suffix) to start running at")
    parser.add_argument("--stop",help="Failure (suffix) to stop running at")
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)

    