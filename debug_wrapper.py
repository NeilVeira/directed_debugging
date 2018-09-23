import os 
import argparse
import random
import time
import suspect_inference
import run_debug_data
import re

def create_template(fail, start_time, overwrite=False):
    template_path = "%s_suffix.template" %(fail)
    if os.path.exists(template_path) and not overwrite:
        return None
    project = fail+"_suffix"
    os.system("cp %s.template %s" %(fail,template_path))
    linez = open(template_path).readlines()
    
    for i in xrange(len(linez)):
        if linez[i].startswith("PROJECT="):
            linez[i] = "PROJECT=%s\n" %(project)
        if linez[i].startswith("START_TIME="):
            linez[i] = "START_TIME=%ins\n" %(start_time)
            
    f = open(template_path,"w")
    for line in linez:
        f.write(line)
    f.close()
    return template_path  


def do_debug(fail, start_time, log):
    project = fail+"_suffix"
    while True:
        print "Running with start time",start_time
        log.write("Running with start time %i\n" %(start_time))
        stdout,stderr = run_debug_data.run("onpoint-cmd --template-file=%s.template" %project)
        onpoint_log_file = "onpoint-cmd-%s.log" %(project)
        if not os.path.exists(onpoint_log_file):
            print "Error:"
            print stdout
            print stderr 
            return False
            
        onpoint_log = open(onpoint_log_file).read()
        if "OnPoint could not reproduce the failure in the current diagnosis run" in onpoint_log \
            or "error: there are no posedges for the clock" in onpoint_log:
            #debug failed - push back start time and retry
            print "Time window is too small, pushing back start time and retrying"
            log.write("Time window is too small, pushing back start time and retrying\n")
            os.system("rm -rf "+onpoint_log_file)
            if start_time == 0:
                return False 
            start_time  = max(0, start_time-50)
            create_template(fail, start_time, overwrite=True)
        elif "error:" in onpoint_log.lower():
            print "Error: vdb failed, check logs"
            log.write("Error: vdb failed, check logs\n")
            return False
        else:
            print "Success!"
            log.write("Success!\n")
            num_suspects = suspect_inference.count_suspects(project+".vennsawork/vennsa.stdb.gz")
            total_suspects = suspect_inference.count_suspects(fail+".vennsawork/vennsa.stdb.gz")
            print "Number of suspects: %i/%i" %(num_suspects,total_suspects)
            log.write("Number of suspects: %i/%i\n" %(num_suspects,total_suspects))
            return True   
            
    return False 
    
 
def build_suffix_instances(args):
    os.chdir(args.design_dir)
    #get all vennsawork and template dirs 
    all_infoz = []
    
    for item1 in os.listdir(os.getcwd()):
        if os.path.isdir(item1) and item1.startswith("random_bug"):
            for item2 in os.listdir(item1):
                if item2.endswith(".vennsawork") and not "_suffix" in item2:                    
                    failure = suspect_inference.process_report(os.path.join(item1,item2))
                    if failure is None:
                        continue                        
                    timez = failure.timez
                    timez.sort()
                    timez.reverse()
                    if 0 in timez:
                        timez = timez[:timez.index(0)]
                    if len(timez) == 0:
                        continue
                    trace_len = timez[0]-timez[-1]
                    #if trace_len >= 100:
                    all_infoz.append((trace_len, item1, item2[:-len(".vennsawork")], timez))
                        
    #all_infoz.sort() 
    #all_infoz.reverse()
    random.shuffle(all_infoz)
    cnt_new = 0
    
    for trace_len,fail_dir,fail,timez in all_infoz:
        os.chdir(fail_dir)
        n = len(timez) - timez.count(0) #zeros are suspects whose time is unknown
        
        #estimate earliest debug start time to get most of the suspects
        min_start = timez[min(len(timez)-1,int(round(0.75*n)))] / args.time_fact
        
        #parse out end time
        template = open(fail+".template").read()
        m = re.search(r"FINISH_TIME=(\d+)ns", template, flags=re.DOTALL)
        if m is None:
            os.chdir("..")
            continue 
            
        max_start = max(min_start,int(m.group(1))-50)
        print ""
        print "Creating suffix debug instance for failure",fail_dir,fail
        print min_start, max_start 
        log = open("/home/neil/date18/suffix_debug.log","a")
        log.write("\nCreating suffix debug instance for failure %s/%s/%s\n" %(args.design_dir,fail_dir,fail))
        log.write("%i %i\n" %(min_start,max_start))
        
        project = fail + "_suffix"
        start_time = random.randint(min_start,max_start)
        template_path = create_template(fail, start_time)
        if template_path == None: #suffix debug already exists for this failure
            os.chdir("..")
            log.close()
            continue
            
        result = do_debug(fail, start_time, log)
        log.close()
        
        if result:
            cnt_new += 1
        os.chdir("..")
        if cnt_new == args.num_fails:
            break


def main(design_dir, ids=None, xabr=False, buggy=False, dryrun=False, overwrite=False):
    if buggy:
        bug_dir_start = "buggy"
    else:
        bug_dir_start = "random_bug_"
            
    if ids == None:
        ids_to_debug = []
        for item in os.listdir(design_dir):
            if item.startswith(bug_dir_start):
                ids_to_debug.append(int(item[len(bug_dir_start):]))
        
    else:
        ids_to_debug = []
        for item in ids.split(","):
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
                cmd = "python run_debug_data.py %s --num_fails=%i --time_fact=%i" %(dir,args.num_fails,args.time_fact)
                if xabr:
                    cmd += " --xabr"
                if dryrun:
                    cmd += " --dryrun"
                if overwrite:
                    cmd += " --overwrite"
                print cmd
                os.system(cmd)
                print "\n"
         
   
def init(parser):
    parser.add_argument("design_dir",help="Directory of design to debug")
    parser.add_argument("--ids",help="Comma-seperated list of indices of random_bug_* directories to debug")
    parser.add_argument("--xabr",action="store_true",default=False,help="Don't use abr strategy")
    parser.add_argument("--suffix",action="store_true",default=False,help="Debug only a suffix window")
    parser.add_argument("--overwrite",action="store_true",default=False,help="Delete any pre-existing template file")
    parser.add_argument("--num_fails",type=int,default=1,help="Number of distinct failures to debug")
    parser.add_argument("--time_fact",type=int,default=1,help="Conversion ratio from simulation time to ns")
    parser.add_argument("--buggy",action="store_true",default=False,help="Run buggy* designs rather than random_bug*")
    parser.add_argument("-n","--dryrun",action="store_true",default=False,\
                        help="Set up template file but don't run it")
   
   
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    if args.suffix:
        build_suffix_instances(args)
    else:
        main(args.design_dir, args.ids, args.xabr, args.buggy, args.dryrun, args.overwrite)
    
    