import os 
import argparse 
import re
import numpy as np
from scipy.stats.mstats import gmean 
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.pylab
from matplotlib import gridspec
from matplotlib.font_manager import FontProperties

import utils 

FLOAT_PATTERN = "([\d\.]+)"
INT_PATTERN = "(\d+)"


def parse_peak_memory(failure):
    mem_file = os.path.join(failure+".vennsawork","logs","vdb","vdb.plot")
    peak_mem = 0
    for line in open(mem_file):
        m = re.match(r"\s+{}\s+{}\s+{}\s+".format(FLOAT_PATTERN,INT_PATTERN,INT_PATTERN), line)
        if m:
            mem = int(m.group(3))
            peak_mem = max(peak_mem,mem)
    return peak_mem

    
# Old version
# def recall_vs_time_single(failure):
    # log_file = os.path.join(failure+".vennsawork","logs","vdb","vdb.log")
    # start = utils.find_time_of(failure, "Oracle::ask\(\)", default=0)            
    # end_time = utils.parse_runtime(failure)

    # cnt = 0
    # points = []
    # for line in open(log_file):
        # t = utils.parse_time_of(line, "==> solver solution:")
        # if t:
            # cnt += 1 
            # points.append([t-start,cnt])
    # points.append([end_time,cnt])
    # print points 
    # return points
    
    
def parse_start_end_times_1pass(failure): 
    log_file = os.path.join(failure+".vennsawork","logs","vdb","vdb.log")  
    # Find the start and end of the second pass that runs solveAll. 
    # It may not be pass 0 in case of abr, and strangely, some passes don't run solveAll. 
    num_starts = 0
    found_start = False 
    
    for line in open(log_file):    
        if "Starting pass" in line:
            num_starts += 1 
                
        elif num_starts >= 2 and "OracleSolver::solveAll()" in line:
            found_start = True 
            start_time = utils.parse_time_of(line, "OracleSolver::solveAll()")
            
        elif found_start and "Finished pass" in line:
            end_time = utils.parse_time_of(line, "Finished pass")
            return start_time, end_time 
            
    # Couldn't find end of pass. Use last time in log file instead. 
    end_time = utils.parse_runtime(failure)
    return start_time, end_time 
    
    
def parse_start_end_times_2pass(failure):
    log_file = os.path.join(failure+".vennsawork","logs","vdb","vdb.log")  
    num_main_passes = 0 # Number of times it's started a new main pass 
    num_starts = 0 
    found_start = False 
    num_finishes = 0
    
    for line in open(log_file): 
        if "Running diagnosePassAndRetry" in line:
            assert num_main_passes <= 1 
            num_main_passes += 1 
            
        elif num_main_passes == 2 and "Starting pass" in line:  
            num_starts += 1
            
        elif num_starts == 2 and "OracleSolver::solveAll()" in line:
            found_start = True 
            start_time = utils.parse_time_of(line, "OracleSolver::solveAll()")
            
        elif found_start and "Finished pass" in line:
            num_finishes += 1
            if num_finishes >= 2:
                end_time = utils.parse_time_of(line, "Finished pass")
                # print "start_time =",start_time 
                # print "end_time =",end_time 
                return start_time, end_time 
            
    assert num_main_passes > 0 
    # Couldn't find end of pass. Use last time in log file instead. 
    end_time = utils.parse_runtime(failure)
    # TODO: this includes significant overhead of starting a new pass in between 
    return start_time, end_time 
    
    
def recall_vs_time_single(failure, num_passes=1):
    if num_passes == 1:
        start_time, end_time = parse_start_end_times_1pass(failure)
    elif num_passes == 2:
        start_time, end_time = parse_start_end_times_2pass(failure)
    else:
        start_time = utils.find_time_of(failure, "Oracle::ask\(\)", default=0)            
        end_time = utils.parse_runtime(failure, time_limit=10800)
    assert start_time <= end_time 

    # Search for solutions 
    log_file = os.path.join(failure+".vennsawork","logs","vdb","vdb.log") 
    cnt = 0
    points = []
    for line in open(log_file):       
        t = utils.parse_time_of(line, "==> solver solution:")
        if t and start_time <= t <= end_time:
            cnt += 1 
            points.append([t-start_time,cnt])
            
    points.append([end_time-start_time,cnt])
    # print failure 
    # print start_time, end_time
    # print points
    # print "" 
    return points
    
  
def recall_vs_time(base_failure, new_failure, num_passes, end_method="min"):
    base_points = recall_vs_time_single(base_failure, 1 if num_passes == 2 else num_passes)
    new_points = recall_vs_time_single(new_failure, num_passes)
    
    # Normalize against base failure
    if end_method == "max":
        end_time = max(base_points[-1][0], new_points[-1][0]) 
    elif end_method == "min":
        end_time = min(base_points[-1][0], new_points[-1][0]) 
    else:
        end_time = base_points[-1][0]
    base_points.append([end_time,base_points[-1][1]])
    new_points.append([end_time,new_points[-1][1]])    
    max_n = float(base_points[-1][1])
    
    for i in range(len(base_points)):
        base_points[i][0] /= end_time
        base_points[i][1] /= max_n 
    for i in range(len(new_points)):
        new_points[i][0] /= end_time 
        new_points[i][1] /= max_n 
    return base_points, new_points
    
    
def auc_recall_time(points):
    '''
    Compute area under recall vs time curve from t = 0 to 1. 
    '''
    auc = 0
    dt_tot = 0
    points = [[0,0]] + list(points)
    i = 1
    while i < len(points):
        if points[i][0] > 1:
            break
        recall = points[i-1][1]
        dt = points[i][0] - points[i-1][0]
        assert dt >= 0
        auc += recall*dt  
        dt_tot += dt  
        i += 1

    if points[i-1][0] < 1:
        dt = 1-points[i-1][0]
        assert dt >= 0 
        dt_tot += dt 
        recall = points[i-1][1]
        auc += recall*dt 
    assert abs(1-dt_tot) < 1e-6 
    return auc 
    
        
def interpolate_value(points, x):
    if x < points[0][0]:
        return 0 
    for i in range(len(points)-1):
        if points[i+1][0] > x:
            return points[i][1]
    return points[-1][1]

def plot_recall_vs_time(base_points, new_points, outfile=None):
    n_points = 101
    x = np.linspace(0,1,n_points)
    y_base = []
    y_new = []
    for i in range(len(x)):
        ys = []
        for points in base_points:
            ys.append(interpolate_value(points,x[i]))
        y_base.append(np.mean(ys))
        ys = []
        for points in new_points:
            ys.append(interpolate_value(points,x[i]))
        y_new.append(np.mean(ys))
    
    c1 = [_/255.0 for _ in (31, 119, 180)]
    c2 = [_/255.0 for _ in (255, 127, 14)]
    # c1 = "r" 
    # c2 = "b"
    plt.clf()
    plt.plot(x, y_base, color=c2, label="baseline debug", linestyle="--", linewidth=3)
    plt.plot(x, y_new, color=c1, label="directed debug", linewidth=2)
    plt.fill_between(x, np.zeros(len(x)), y_base, color=c2, alpha=0.5)
    plt.fill_between(x, y_base, y_new, color=c1, alpha=0.25)

    if len(base_points) == 1:
        R_base = auc_recall_time(base_points[0])
        R_new = auc_recall_time(new_points[0])
        font = FontProperties()
        font.set_weight("heavy")
        plt.text(0.7, 0.3, "$R_{base}=%.3f$" %(R_base), fontsize=18, weight="heavy")
        plt.text(0.56, 0.6, "$R_{new}=%.3f$" %(R_new), fontsize=18, weight="heavy")

    plt.xlabel("Relative runtime", fontsize=16)
    plt.ylabel("Suspect recall", fontsize=16)
    plt.xlim((0,1))
    plt.ylim((-0.05,1.05))
    plt.legend(loc="lower right")
    if outfile:
        plt.savefig(outfile)

        
def plot_improvements(outfile, recall_auc_improvementz):    
    plt.clf()
    x = recall_auc_improvementz
    x.sort()
    y = np.array(range(1,len(x)+1)) / float(len(x)) * 100 
    plt.xlabel("Improvement in area under recall-time curve")
    plt.ylabel("Percentage of failures")
    plt.plot(x,y)
    plt.savefig(outfile)
    
    
def check_good_for_analysis(failure, num_passes, min_runtime, verbose=False):
    log_file = failure+".vennsawork/logs/vdb/vdb.log"
    if not os.path.exists(log_file):
        if verbose:
            print "Skipping failure %s (failed or not run)" %(failure)
        return False 
        
    log = open(log_file).read() 
    if log.count("Starting pass") < 2:
        if verbose:
            print "Skipping failure %s due to missing fine-grained debugging pass" %(failure) 
        return False         
        
    if num_passes == 1:
        start_time, end_time = parse_start_end_times_1pass(failure)
    else:
        start_time, end_time = parse_start_end_times_2pass(failure)
        
    if end_time - start_time < min_runtime:
        if verbose:
            print "Skipping failure %s due to short runtime" %(failure)
        return False 
        
    # if "tcmalloc: large alloc" in log:
        # if verbose:
            # print "Skipping failure %s due to tcmalloc error" %(failure)
        # return False 
        
    return True 

     
def analyze_1or2_pass(base_failure, new_failure, num_passes, verbose=False, min_runtime=0, end_method="min"):
    if not check_good_for_analysis(base_failure, 1, min_runtime, verbose) or \
        not check_good_for_analysis(new_failure, num_passes, min_runtime, verbose):
        return None,None,None,None,None

    print "%i-pass analyzing %s" %(num_passes,new_failure)
        
    start_time, end_time = parse_start_end_times_1pass(base_failure)
    base_runtime = end_time - start_time
    if num_passes == 1:
        start_time, end_time = parse_start_end_times_1pass(new_failure)
    elif num_passes == 2:
        start_time, end_time = parse_start_end_times_2pass(new_failure)
    new_runtime = end_time - start_time 
    speedup = new_runtime / base_runtime 
    
    # Analyze peak memory usage
    base_mem = parse_peak_memory(base_failure)
    new_mem = parse_peak_memory(new_failure)
    mem_reduce = new_mem / float(base_mem)
        
    # Parse predictions, solutions, and compute accuracy
    log_file = new_failure+".vennsawork/logs/vdb/vdb.log"
    predictions = []
    found_suspects = set([])
    
    for line in open(log_file):
        m = re.search(r"Predicting next suspect (\S+)", line)
        if m:
            s = m.group(1)
            if s != 0:
                predictions.append(s)
            
        m = re.search(r"==> solver solution:.*:(\S+)\s+", line)
        if m:
            s = m.group(1)
            found_suspects.add(s)
            
    auc_acc = 0
    correct = 0
    total = 0
    for s in predictions:
        total += 1 
        if s in found_suspects:
            correct += 1
        auc_acc += float(correct)/total 
    if total > 0:
        auc_acc /= total
    
    base_points, new_points = recall_vs_time(base_failure, new_failure, num_passes, end_method=end_method)
    base_recall_auc = auc_recall_time(base_points)
    new_recall_auc = auc_recall_time(new_points)
    if base_recall_auc == 0 or new_recall_auc == 0 or not 0.1 <= new_recall_auc / base_recall_auc <= 10:
        # This can happen when using end_method=min in the rare case that one of the experiments finds 
        # all or almost all suspects before the other finds any.
        # Such cases are probably not very meaningful so skipping is probably justified. 
        print "WARNING: skipping extreme outlier" 
        return None,None,None,None,None
        
    recall = len(new_points)/float(len(base_points)) if len(base_points) > 0 else np.nan 
    recall_auc_improvement = new_recall_auc / base_recall_auc
    runs_finished = np.array([utils.parse_run_finished(base_failure), utils.parse_run_finished(new_failure)], dtype=np.int32)
    
    # print base_points 
    # print new_points 
    # print base_recall_auc
    # print new_recall_auc    

    print "Recall auc improvement: %.3f" %(recall_auc_improvement)
    if verbose:
        print "Number of base points: %i" %(len(base_points))
        print "Number of new points: %i (recall %.3f)" %(len(new_points), recall)
        print "Runtime: %.1fs" %(base_runtime)
        print "Relative runtime: %.3f" %(speedup)
        print "Prediction accuracy auc: %.3f" %(auc_acc)
        print "Peak memory reduction: %.3f" %(mem_reduce)
        print ""
        
    return recall_auc_improvement, speedup, base_points, new_points, runs_finished


def analyze_multi_pass(base_failure, new_failure, verbose=False, min_runtime=0, end_method="min"):
    # if not check_good_for_analysis(base_failure, 1, 4) or not check_good_for_analysis(new_failure, 1, 4):
    #     return None,None,None,None,None
    base_log = base_failure+".vennsawork/logs/vdb/vdb.log"
    if not os.path.exists(base_log):
        if verbose:
            print "Skipping failure %s (failed or not run)" %(base_failure)
        return None,None,None,None,None

    num_passes = open(base_log).read().count("Starting pass")
    if num_passes < 4:
        if verbose:
            print "Skipping failure %s due to too few passes" %(failure) 
        return None,None,None,None,None

    print "Multi-pass analyzing",new_failure 

    base_runtime = utils.parse_runtime(base_failure, time_limit=10800)
    new_runtime = utils.parse_runtime(new_failure, time_limit=10800)
    speedup = new_runtime / base_runtime 

    # Analyze peak memory usage
    base_mem = parse_peak_memory(base_failure)
    new_mem = parse_peak_memory(new_failure)
    mem_reduce = new_mem / float(base_mem)

    # TODO: some kind of prediction accuracy analysis 

    base_points, new_points = recall_vs_time(base_failure, new_failure, num_passes=-1, end_method=end_method)
    base_recall_auc = auc_recall_time(base_points)    
    new_recall_auc = auc_recall_time(new_points)
    
    if base_recall_auc == 0 or new_recall_auc == 0 or not 0.1 <= new_recall_auc / base_recall_auc <= 10:
        # This can happen when using end_method=min in the rare case that one of the experiments finds 
        # all or almost all suspects before the other finds any.
        # Such cases are probably not very meaningful so skipping is probably justified. 
        print "WARNING: skipping extreme outlier" 
        return None,None,None,None,None
        
    recall = len(new_points)/float(len(base_points)) if len(base_points) > 0 else np.nan 
    recall_auc_improvement = new_recall_auc / base_recall_auc

    runs_finished = np.array([utils.parse_run_finished(base_failure), utils.parse_run_finished(new_failure)], dtype=np.int32)
    print "Recall auc improvement: %.3f" %(recall_auc_improvement)
    if verbose:
        print "Number of base points: %i" %(len(base_points))
        print "Number of new points: %i (recall %.3f)" %(len(new_points), recall)
        print "Number of passes: %i" %(num_passes)
        print "Runtime: %.1fs" %(base_runtime)
        print "Relative runtime: %.3f" %(speedup)
        print "Peak memory reduction: %.3f" %(mem_reduce)
        print ""

    return recall_auc_improvement, speedup, base_points, new_points, runs_finished


def analyze(base_failure, new_failure, verbose=False, min_runtime=0, end_method="min"):
    # determine what analysis function to use 
    log_file = new_failure+".vennsawork/logs/vdb/vdb.log"
    if not os.path.exists(log_file):
        if verbose:
            print "Skipping failure %s (failed or not run)." %(new_failure)
        return None, None, None, None, None  

    log = open(log_file).read()
    m = re.search(r"Guidance method = (\d+)", log)
    if m:
        method = int(m.group(1))
        if method >= 10:
            return analyze_multi_pass(base_failure, new_failure, verbose, min_runtime, end_method)
        elif method == 6:
            return analyze_1or2_pass(base_failure, new_failure, 2, verbose, min_runtime, end_method)
        elif method > 0:
            return analyze_1or2_pass(base_failure, new_failure, 1, verbose, min_runtime, end_method)
    
    print "Could not determine analysis method for failure", new_failure 
    return None, None, None, None, None 

  
def main(args):
    if args.design:
        all_failurez = utils.find_all_failures(args.design)
    else:
        assert args.failure 
        all_failurez = [args.failure]    
    
    all_base_points = []
    all_new_points = []
    recall_auc_improvementz = []
    speedupz = []
    tot_runs_finished = np.zeros(2, dtype=np.int32)
    
    for failure in all_failurez: 
        recall_auc_improvement, speedup, base_points, new_points, runs_finished = analyze(failure+args.base_suffix, 
            failure+args.new_suffix, verbose=args.verbose, min_runtime=args.min_runtime)
        
        if recall_auc_improvement is not None:
            tot_runs_finished += runs_finished 
            recall_auc_improvementz.append(recall_auc_improvement)
            if runs_finished[0] and runs_finished[1]:
                speedupz.append(speedup)
            all_base_points.append(base_points)
            all_new_points.append(new_points)

            if args.plot_individual:
                outfile = "plots/%s_recall_vs_time.png" %(failure.replace("/","_"))
                plot_recall_vs_time([base_points], [new_points], outfile=outfile)
                plt.clf()
            
    if args.plot:   
        if args.design:
            design = os.path.basename(args.design)
        else:
            design = args.failure.rstrip("/").replace("/","_")
        outfile = "plots/%s_recall_vs_time.png" %(design)
        plot_recall_vs_time(all_base_points, all_new_points, outfile=outfile)
        plot_improvements("plots/%s_improvements.png" %(design), recall_auc_improvementz)

    print "Geometric mean recall auc improvement (%i failures): %.3f" %(len(recall_auc_improvementz),gmean(recall_auc_improvementz))
    print "Geometric mean relative runtime: %.3f" %(gmean(speedupz))
    print "Number of failures solved (base): %i/%i" %(tot_runs_finished[0],len(recall_auc_improvementz))
    print "Number of failures solved (new): %i/%i" %(tot_runs_finished[1],len(recall_auc_improvementz))
    
    
def init(parser):
    parser.add_argument("new_suffix", default="", help="Suffix of failure names to compare against the baseline")
    parser.add_argument("base_suffix", nargs='?', default="", help="[optional] Suffix of failure names to compare against the baseline")
    parser.add_argument("--design", help="Design to analyze.")
    parser.add_argument("--failure", help="Analyze a single failure (base name).")    
    parser.add_argument("--min_runtime", type=int, default=10, help="Exclude designs with runtime less than this.")
    parser.add_argument("-p", "--plot", action="store_true", default=False, help="Generate recall-time plot aggregated over all failures.")
    parser.add_argument("-pi", "--plot_individual", action="store_true", default=False, 
                        help="Generate recall-time plot for individual failures")
    parser.add_argument("--end_method", default="min", help="Use min, max, or base as end time (default min)")
    parser.add_argument("-v", "--verbose", action="store_true", default=False)
    
  
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)
