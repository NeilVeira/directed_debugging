import os 
import re 
import subprocess32 as subprocess
import signal

TIMESTAMP_PATTERN = "\d+-\w+-\d+ \d+:\d+:\d+ \((\d+):(\d+):(\d+)\.(\d+)\)"

def run(cmd, verbose=False, timeout=5*60*60*24):
    '''
    Run a command with a time limit. 
    '''
    if verbose:
        print cmd
    try:
        proc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
        stdout, stderr = proc.communicate(None, timeout=timeout)
        return stdout,stderr
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
        return None,None  


def debug_passed(failure):
    stdb_file = os.path.join(failure+".vennsawork","vennsa.stdb.gz")
    if not os.path.exists(stdb_file):
        return False 
    else:
        suspectz = parse_suspects(failure)
        if len(suspectz) == 0:
            return False 
    
    log_file = os.path.join(failure+".vennsawork","logs","vdb","vdb.log")
    if not os.path.exists(log_file):
        return False 
    
    log = open(log_file).read()
    return "error:" not in log 
        

def find_all_templates(dir):
    results = []
    for item in sorted(os.listdir(dir)):
        if item.startswith("random_bug") or item.startswith("buggy"):             
            for sub_item in sorted(os.listdir(os.path.join(dir,item))):
                m = re.match(r"fail_\d+\.template\Z", sub_item)
                if m:
                    failure_name = os.path.join(dir, item, sub_item[:-len(".template")])
                    results.append(failure_name)
    return results 
        
def find_all_failures(dir, include_failed=False):
    results = []
    failed_cnt = 0
    for item in sorted(os.listdir(dir)):
        if item.startswith("random_bug") or item.startswith("buggy"):             
            for sub_item in sorted(os.listdir(os.path.join(dir,item))):
                m = re.match(r"fail_\d+\.vennsawork\Z", sub_item)
                if m:
                    failure_name = os.path.join(dir, item, sub_item[:-len(".vennsawork")])
                    if include_failed or debug_passed(failure_name):
                        results.append(failure_name)
                    else:
                        print "WARNING: Ignoring failure %s which appears to have failed" %(failure_name)
                        failed_cnt += 1 
    # if failed_cnt > 0:
        # print "WARNING: Ignoring %i failures where debug appears to have failed" %(failed_cnt)
    return results 
    
    
def find_all_bugs(dir):
    results = set([])
    for f in find_all_failures(dir):
        bug_dir = os.path.dirname(f)
        results.add(bug_dir)
    
    results = list(results)
    results.sort()
    return results
                
                
def parse_suspects(failure):
    cache_path = os.path.join(failure+".vennsawork", "suspect_cache.txt")
    stdb_path = os.path.join(failure+".vennsawork","vennsa.stdb.gz")
    if os.path.exists(cache_path) and os.path.exists(stdb_path) and  os.path.getmtime(cache_path) > os.path.getmtime(stdb_path):
        report = open(cache_path).read()
    elif os.path.exists(stdb_path):
        report, _ = run("stdb %s report" %(stdb_path))
        with open(cache_path,"w") as f:
            f.write(report)
    else:
        return []
    
    suspectz = []
    for suspect_parse in re.findall(r"rtl\s+([\w/]+)\s+(\w+)\s+([\w\./]+)\s+([\d\.]+)\s+([\d\.]+)", report, flags=re.DOTALL):
        suspectz.append(suspect_parse[0])
    # assert len(suspectz) > 0, "No suspects found for failure %s" %(failure)
    return suspectz 
        
        
def parse_time_of(line, pattern):
    full_pattern = r".*%s ##\s*%s" %(TIMESTAMP_PATTERN,pattern)
    m = re.search(full_pattern,line)
    if m:
        return 3600*int(m.group(1)) + 60*int(m.group(2)) + int(m.group(3)) + float("0."+m.group(4))
    else:
        return None 
        
        
def find_time_of(failure, pattern, default=None):
    log_path = os.path.join(failure+".vennsawork","logs","vdb","vdb.log")
    assert os.path.exists(log_path)        
    for line in open(log_path):
        t = parse_time_of(line, pattern)
        if t:
            return t
    return default
        
        
def parse_runtime(failure, time_limit=3600):
    start = find_time_of(failure, "Oracle::ask\(\)")
    if not start:
        start = find_time_of(failure, "OracleSolver::solveAll\(\)")
        if not start:
            start = 0 
    
    end = find_time_of(failure, "\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*  VDB Process Ends  \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*")
    if end:
        return end - start 
    else:
        # No way to know actual time limit since it's not recorded anywhere...
        print "WARNING: failure %s did not finish. Assuming a total runtime of %i seconds." %(failure, time_limit)
        return time_limit - start
        
        
def parse_run_finished(failure):
    end = find_time_of(failure, "\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*  VDB Process Ends  \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*")
    if end:
        return 1
    else:
        return 0 
    
    
def copy_file(source, target, strip_header=False, verbose=True):
    if verbose:
        print source,target
    parts = target.split("/")
    for i in range(1,len(parts)):
        dir = "/".join(parts[:i])
        if not os.path.exists(dir):
            os.system("mkdir %s" %(dir))
    
    if strip_header:
        with open(source) as f:
            data = f.readlines()
        data = "".join(data[13:])
        with open(target,"w") as f:
            f.write(data)
    else:
        os.system("cp %s %s" %(source,target))
        
        
def write_template(fname, key, line):
    '''
    Set the line starting with key in the template file given by fname 
    to the given line. 
    '''
    linez = open(fname).readlines()
    for i in range(len(linez)):
        if linez[i].startswith(key):
            linez[i] = line 
            if line[-1] != "\n":
                linez[i] += "\n"
    
    with open(fname,"w") as f:
        f.write("".join(linez))

        
def rename_project(old_name, new_name):
    if os.path.exists(old_name+".template"):
        os.system("mv %s.template %s.template" %(old_name,new_name))
        write_template(new_name+".template", "PROJECT=", "PROJECT="+os.path.basename(new_name))
        
    if os.path.exists(old_name+".vennsawork"):
        if os.path.exists(new_name+".vennsawork"):
            os.system("mv %s.vennsawork %s_garbage.vennsawork" %(new_name,new_name))
            print "WARNING: project %s.vennsawork already exists" %(new_name)
        os.system("mv %s.vennsawork %s.vennsawork" %(old_name, new_name))
    

def parse_ids(string):
    '''
    Convert comma-seperated string of ints and ranges (eg '3-6') into a list of ints. 
    '''
    tokens = string.split(",")
    ids = []
    for token in tokens:
        if "-" in token:
            low,high = map(int,token.split("-"))
            ids.extend(range(low,high+1))
        else:
            ids.append(int(token))
    return ids 

