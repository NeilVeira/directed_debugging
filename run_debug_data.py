import os 
import argparse
import re
import subprocess32 as subprocess
import signal
import random

DESIGN_INFO_FILE = "design_info.csv"
ASSERT_FAILED_PATTERN = r"Error:.*?Time:\s*(\d+)\s*([np]s)\s+Started:\s*(\d+)\s*([np]s)\s*Scope:\s*DUT_PATH\.([^\s]+)"
TIME_PATTERN = r".*Time:\s*(\d+)\s*([np]s)"
                    
                        
class SignalFailure(object):
    def __init__(self, name, time, buggy, golden):
        self.name = name
        self.time = time 
        self.buggy = buggy 
        self.golden = golden 
        m = re.match(r"\w+\[(\d+):(\d+)\]",self.name)
        if m:
            self.size = int(m.group(1))-int(m.group(2))+1
        else:
            self.size = 1
        self.id = 0
        
    def __lt__(self,other):
        if self.size == other.size:
            return self.time < other.time 
        else:
            return self.size > other.size
        
    def __str__(self):
        ret = "Failure in signal %s at time %i ns\n" %(self.name,self.time)
        ret += "Buggy: %s\n" %(self.buggy)
        ret += "Golden: %s" %(self.golden)
        return ret
        
    def get_setting(self):
        return "CONSTRAIN_SIGNAL=%s:h%s:%ins\n" %(self.name,self.golden,self.time)
        
    def get_debug_start(self, window_size):
        return max(0, self.time-window_size)
    
    def get_debug_end(self):
        return self.time+50
        
            
class AssertionFailure(object):
    def __init__(self, name, start_time, start_unit, end_time, end_unit, id=0):
        self.name = name 
        self.start_time = int(start_time) 
        if start_unit == "ps":
            self.start_time = self.start_time/1000 + 1
        self.end_time = int(end_time)
        if end_unit == "ps":
            self.end_time = self.end_time/1000 + 1
        self.start_time = max(0, min(self.start_time, self.end_time-50))
        self.id = id
        
    def __str__(self):
        return "Assertion failure at time %i: %s" %(self.end_time, self.name)
        
    def get_setting(self):
        return "TARGET_ASSERTION=%s:%ins-%ins\n" %(self.name,self.start_time,self.end_time)
        
    def get_debug_start(self, window_size):
        return max(0, min(self.start_time-50, self.end_time-window_size))
        
    def get_debug_end(self):
        return self.end_time+50
 
 
def run(cmd, verbose=True, timeout=5*60*60*24):
    if verbose:
        print cmd
    try:
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
        stdout, stderr = proc.communicate(None, timeout=timeout)
        return stdout,stderr
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        return None,None   
    
  
def load_design_info():
    '''
    Return dict of dicts mapping each design to its info in DESIGN_INFO_FILE
    '''
    design_infox = {}
    linez = open(DESIGN_INFO_FILE).readlines()
    
    cols = linez[0].split(",")    
    for line in linez[1:]:
        vals = line.split(",")
        design = vals[0].strip()
        design_infox[design] = {}
        for i in xrange(1,len(cols)):
            if i < len(vals):
                design_infox[design][cols[i].strip()] = vals[i].strip()
            else:
                design_infox[design][cols[i].strip()] = ""
    return design_infox
    
   
def get_sim_file(bug_dir):
    if os.path.exists(os.path.join(bug_dir,"sim","transcript")):
        return os.path.join(bug_dir,"sim","transcript")
    elif os.path.exists(os.path.join(bug_dir,"sim","qverilog.log")):
        return os.path.join(bug_dir,"sim","qverilog.log")
    else:
        return ""
        
   
def parse_assertions(sim_file, dut_path):
    '''
    Parse the simulation output for assertion failed messages.
    '''
    sim = open(sim_file).read()
    resultx = {}
    
    #parse all unique assertion failures from sim
    pattern = ASSERT_FAILED_PATTERN.replace("DUT_PATH",dut_path)
    for m in re.findall(pattern, sim, flags=re.DOTALL):
        f = AssertionFailure(m[4],m[2],m[3],m[0],m[1])
        if not resultx.has_key(f.name):
            resultx[f.name] = []
        resultx[f.name].append(f)  
    return resultx 
    

def load_signal_valuex(sim_file,time_fact):
    signal_valuex = {}
    cur_time = 0
    for line in open(sim_file):
        line = line.strip()
        m = re.match(r"#\s*Signals at\s+(\d+)", line)
        if m:
            cur_time = int(m.group(1))/time_fact
            
        m = re.match(r"#\s*(\w+(?:\[\d+:\d+\])?)\s*=\s*(\w+)",line)
        if m:
            sig = m.group(1)
            val = m.group(2).lower()
            if not signal_valuex.has_key(sig):
                signal_valuex[sig] = []
            signal_valuex[sig].append((cur_time,val))
    return signal_valuex
    
    
def choose_failures(all_failx, num_results):
    if num_results < 0:
        num_results = min(-num_results,len(all_failx.keys()))
        
    chosen = []
    #randomly pick num_results items from all_failx
    keyz = all_failx.keys()
    random.shuffle(keyz)
    for sig in keyz:
        random.shuffle(all_failx[sig])
    num_results = min(num_results, len(chosen)+sum(map(len,all_failx.values())))
    
    indices = [0]*len(keyz)
    i = 0
    while len(chosen) < num_results:
        if indices[i] < len(all_failx[keyz[i]]):
            chosen.append(all_failx[keyz[i]][indices[i]])
            chosen[-1].id = len(chosen)-1
            indices[i] += 1
        i = (i+1)%len(keyz)
    
    return chosen
        
    
def get_failures(buggy_sim, golden_sim, dut_path, num_results=1, time_fact=1):
    if not os.path.exists(buggy_sim):
        print "Error: file %s does not exist" %(buggy_sim)
        return []
    elif not os.path.exists(golden_sim):
        print "Error: file %s does not exist" %(golden_sim)
        return []      
        
    buggy_valuex = load_signal_valuex(buggy_sim,time_fact)
    golden_valuex = load_signal_valuex(golden_sim,time_fact)
    signalz = buggy_valuex.keys()
    all_failx = {}
            
    for sig in signalz:
        i = 0
        j = 0
        sig_fails = []
        buggy_valuez = buggy_valuex[sig]
        if not golden_valuex.has_key(sig):
            continue
        golden_valuez = golden_valuex[sig]
        
        while j < len(buggy_valuez) and i < len(golden_valuez):
            while i < len(golden_valuez) and golden_valuez[i][0] <= buggy_valuez[j][0]:
                i += 1
            i -= 1
                
            try:
                buggy_val = buggy_valuez[j][1] #wtf is this failing?
            except:
                print buggy_valuez 
                print "j =",j
                print buggy_valuez[j]
                print "j =",j
                assert False 
            golden_val = golden_valuez[i][1]
            if "x" not in buggy_val and "x" not in golden_val and "z" not in buggy_val and "z" not in golden_val and buggy_val != golden_val:
                f = SignalFailure(sig,buggy_valuez[j][0],buggy_val,golden_val)
                sig_fails.append(f)
            j += 1
        if len(sig_fails) > 0:
            all_failx[sig] = sig_fails
            
    assertion_failx = parse_assertions(buggy_sim, dut_path)
    all_failx.update(assertion_failx)
    ret_fails = choose_failures(all_failx, num_results)
    return ret_fails
    
  
def get_preexisting_failures(bug_path):
    '''
    Return a list containing names of all failures already covered by vennsawork 
    folders in the bug_path. A second list contains their corresponding ids.
    '''
    failurez = []
    idz = []
    for item in os.listdir(bug_path):
        m = re.match(r"fail_(\d+)\.vennsawork",item)
        if not m:
            continue 
            
        id = int(m.group(1))
        template_path = os.path.join(bug_path,"fail_%i.template" %id)
        if os.path.exists(template_path):
            for line in open(template_path):
                m = re.match(r"TARGET_ASSERTION\s*=\s*([\w\.]+)",line)
                if m:
                    failurez.append(m.group(1)) 
                    idz.append(id)
                m = re.match(r"CONSTRAIN_SIGNAL\s*=\s*(\w+(?:\[\d+:\d+\])?)",line)
                if m:
                    failurez.append(m.group(1))
                    idz.append(id)
    return failurez,idz
    
    
def filter_failures(failurez, bug_path):
    '''
    Remove any items from failurez which are already covered by vennsawork folders 
    in the bug_path. 
    '''
    pre_failurez,idz = get_preexisting_failures(bug_path)
    i = 0
    while i < len(failurez):
        if failurez[i].name in pre_failurez:
            del failurez[i]
        else:
            i += 1
            
    #reset their ids to avoid conflicts 
    id = 0
    for i in range(len(failurez)):
        while id in idz:
            id += 1 
        failurez[i].id = id
        id += 1
        
    return failurez

  
def create_template(failure, project, design_infox, window_size, args):
    '''
    Create project.template file using onpoint-cmd and fill 
    in the relevant fields.
    '''
    print "Creating new template file %s.template" %(project)
    run("rm -rf %s.template" %(project))
    if os.path.exists(project+".template"):
        print "Template file already exists"
    else:
        run("onpoint-cmd %s.template --generate-template" %(project))
    linez = open(project+".template").readlines()
    
    start_time = failure.get_debug_start(window_size)
    finish_time = failure.get_debug_end()
    constrain_success = False 
    vector_file_success = False
    start_time_success = False 
    finish_time_success = False 
    
    #Fill out template file
    for i in xrange(len(linez)):
        if linez[i].startswith("PROJECT="):
            linez[i] = "PROJECT=%s\n" %project 
            
        elif linez[i].startswith("DESIGN="):
            linez[i] = "DESIGN=%s\n" %(design_infox["top-level"])
            
        elif linez[i].startswith("DUT_PATH="):
            linez[i] = "DUT_PATH=%s\n" %(design_infox["dut path"])
            
        elif linez[i].startswith("FILELIST="):
            linez[i] = "FILELIST=filelist.l\n"
            
        elif linez[i].startswith("VECTOR_FILE="):
            #look for any vcd or fsdb file
            for item in os.listdir("sim"):
                if item.endswith(".vcd") or item.endswith(".fsdb"):
                    linez[i] = "VECTOR_FILE=sim/%s\n" %(item)
                    vector_file_success = True 
                    break 
            else:
                print "Error: no vector file found in sim"
            
        elif linez[i].startswith("RUN="):
            if args.xabr:
                linez[i] = "RUN=setup,vdb\n"
            else:
                linez[i] = "RUN=setup,abr,vdb\n"
            
        elif linez[i].startswith("TARGET_ASSERTION=") and type(failure) == AssertionFailure:
            linez[i] = failure.get_setting()
            constrain_success = True 
            
        elif linez[i].startswith("CONSTRAIN_SIGNAL="):
            #check if constrain signal is already set to something 
            if len(linez[i]) > len("CONSTRAIN_SIGNAL=")+5:
                constrain_success = True 
            elif type(failure) == SignalFailure and not constrain_success:
                linez[i] = failure.get_setting()
                constrain_success = True 
                
        elif linez[i].startswith("START_TIME="):
            #Note: don't do this. start time must be overwritten for suffix expansion
            #if len(linez[i]) > len("START_TIME=")+2:
            #    start_time_success = True 
            if start_time != None:
                linez[i] = "START_TIME=%ins\n" %(start_time) 
                start_time_success = True
            elif len(linez[i]) > len("START_TIME=")+2:
                start_time_success = True 
            
        elif linez[i].startswith("FINISH_TIME="):
            if len(linez[i]) > len("FINISH_TIME=")+2:
                finish_time_success = True 
                try:
                    finish_time = int(linez[i].strip()[12:-2].strip())
                    start_time = max(0, finish_time-window_size)
                except:
                    pass
            elif finish_time != None:
                linez[i] = "FINISH_TIME=%ins\n" %(finish_time)
                finish_time_success = True 
                
        elif linez[i].startswith("TIME_LIMIT="):
            linez[i] = "#TIME_LIMIT=\n"
            
    f = open(project+".template","w")
    for line in linez:
        f.write(line)
    f.close()
    
    success = finish_time_success and start_time_success and vector_file_success and constrain_success
    if success:
        print "Successfully completed template file"
    else:
        print "Error: unable to complete template file"
    return success
    
    
def check_solutions(report):
    '''
    Check whether the suspect report from stdb contains the actual bug. 
    '''
    if not os.path.exists("bug_desc.txt"):
        return False,0 
        
    bug_desc = open("bug_desc.txt").read()
    m = re.search(r"Location:\s+([\w/\.]+)\s*:\s*(\d+)", bug_desc)
    if m:
        bug_file = "../"+m.group(1)
        bug_line = int(m.group(2))
    else:
        return False,0
        
    suspect_cnt = 0
    found = False 
    for suspect in re.findall(r"rtl\s+[\w/]+\s+\w+\s+([\w\./]+)\s+([\d\.]+)\s+([\d\.]+)", report, flags=re.DOTALL):
        suspect_cnt += 1 
        if suspect[0] == bug_file:
            line_start = int(float(suspect[1]))
            line_end = int(float(suspect[2]))
            #some bug descriptions are off by 2 because they point to the original line in the golden design 
            if bug_line <= line_start <= bug_line+2: 
            #if line_start == bug_line:
                found = True 
    return found,suspect_cnt
    
    
def run_suffix_expansion(failure, design_name, design_infox, args):
    '''
    Main function for creating and running the debug instance. 
    '''
    print "Creating debug instance for design",design_name
    print failure
    window_size = 1000
    project = "fail_"+str(failure.id)
    if args.dryrun:
        project += "_dryrun"
    
    while True:
        success = create_template(failure, project, design_infox[design_name], window_size, args)
        if not success or args.dryrun:
            return False             
        
        os.system("rm -f onpoint-cmd-%s.log" %(project))
        print "Running debug..."
        stdout,stderr = run("onpoint-cmd --template-file=%s.template" %(project))
        
        if stdout == None:
            print "onpoint-cmd exceeded time limit of 48 hours"
            if os.path.exists("vennsa.stdb.gz"):
                run("mv vennsa.stdb.gz %s.vennsawork" %(project))
            return False 
        
        #check logs for errors
        log_file = "onpoint-cmd-%s.log" %(project)
        if not os.path.exists(log_file):
            print "Error:"
            print stdout
            print stderr 
            return False
            
        log = open(log_file).read()
        if "error:" in log.lower():
            print "vdb failed, check logs"
            #restore stdb file from last successful run 
            if os.path.exists("vennsa.stdb.gz"):
                run("mv vennsa.stdb.gz %s.vennsawork" %(project))
            return False
            
        elif "warning: solutions were found to fix the problem at the beginning of the diagnose window" in log.lower():
            window_size *= 2 
            print "Solutions were found at the beginning the the diagnose window. Expanding window size to %i ns." %(window_size)
            report,_ = run("stdb %s.vennsawork/vennsa.stdb.gz report" %(project))
            #backup stdb file as .tmp in case the next run fails 
            run("cp %s.vennsawork/vennsa.stdb.gz ." %(project))
            
        else:
            report,_ = run("stdb %s.vennsawork/vennsa.stdb.gz report" %(project))
            break    
        
    run("rm -f vennsa.stdb.gz")
    print report
    if not check_solutions(report)[0]:
        print "vdb did not find actual bug location"
        return False
    else:
        print report
        print "vdb successful!"
        return True
        
        
'''def build_suffix_instance(design_name, design_infox):
    print "Creating suffix debug instance for design",design_name
    project = design_name+"_suffix"
    
    #get number of suspects in full debug intsance 
    stdb_path = "%s.vennsawork/vennsa.stdb.gz" %(design_name)
    if not os.path.exists(stdb_path):
        print "Error: must run full debug before suffix debug"
        return False 
    report,_ = run("stdb %s report" %(stdb_path))
    total_suspects = check_solutions(report)[1]
    
    print "Trying to create debug instance with %i suspects" %(total_suspects/2)
    low = 100
    high = 1000
    while (high-low > 100):
        mid = (low+high)/2
        print "window size:",mid
        
        success = create_template(project, design_name, design_infox, mid, args)
        if not success: 
            return False 
        os.system("rm -f onpoint-cmd-%s.log" %(project))
        print "Running debug..."
        stdout,stderr = run("onpoint-cmd --template-file=%s.template" %(project))
            
        log_file = "onpoint-cmd-%s.log" %(project)
        if not os.path.exists(log_file):
            print "vdb failed"
            low = mid+1 
        else:
            log = open(log_file).read()
            if "error:" in log.lower():
                print "vdb failed"
                low = mid+1
            else: 
                report,_ = run("stdb %s.vennsawork/vennsa.stdb.gz report" %(project))
                num_suspects = check_solutions(report)[1]
                print "number of suspects:",num_suspects
                if 0.4*total_suspects <= num_suspects <= 0.6*total_suspects:
                    print "Success!" 
                    return True 
                elif num_suspects < 0.4*total_suspects:
                    #too few suspects, increase window 
                    low = mid+1
                else:
                    #too many suspects, decrease window 
                    high = mid 
    print "Unsuccessful"
    return False '''
      
    
def main(args):
    bug_dir = args.bug_dir.rstrip("/")
    golden_dir = os.path.join(bug_dir,"..","golden")
    if not os.path.exists(bug_dir):
        print "Error: design directory %s does not exist" %(bug_dir)
        return False 
    elif not os.path.exists(golden_dir):
        print "Error: could not find golden design"
        return False 
    buggy_sim = get_sim_file(bug_dir)
    golden_sim = get_sim_file(golden_dir)
    if buggy_sim == "":
        print "Error: could not find simulation file"
        return False 
    if golden_sim == "":
        print "Error: could not find golden simulation file"
        return False
    design_infox = load_design_info()
    design_name = bug_dir.split("/")[-2]
    if not design_infox.has_key(design_name):
        print "Error: Unknown design %s" %design_name 
        return False 
          
    failurez = get_failures(buggy_sim, golden_sim, design_infox[design_name]["dut path"], args.num_fails, args.time_fact)
    print "Failures:"
    for f in failurez:
        print f 
    
    if not args.overwrite:
        failurez = filter_failures(failurez,bug_dir)
    
    os.chdir(bug_dir)
    for f in failurez:
        run_suffix_expansion(f, design_name, design_infox, args)
        print ""
    if len(failurez) == 0:
        print "Error: No new failures found"
   
   
def init(parser):
    parser.add_argument("bug_dir",help="Directory of design to debug")
    parser.add_argument("--xabr",action="store_true",default=False,help="Don't use abr strategy")
    parser.add_argument("--overwrite",action="store_true",default=False,help="Delete any pre-existing template file")
    parser.add_argument("--num_fails",type=int,default=1,help="Number of distinct failures to debug")
    parser.add_argument("--time_fact",type=int,default=1,help="Conversion ratio from simulation time to ns")
    parser.add_argument("-n","--dryrun",action="store_true",default=False,\
                        help="Set up template file but don't run it")
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)

    