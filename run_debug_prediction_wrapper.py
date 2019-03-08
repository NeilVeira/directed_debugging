import os 
import argparse 

import utils 
import run_debug_prediction


def find_failure(failure, all_failurez):
    for i in range(len(all_failurez)):
        if all_failurez[i].endswith(failure):
            return i 
    else:
        raise ValueError("No failure %s found" %(failure))
    
    
def main(args):
    unsuccessful = []
    all_failurez = utils.find_all_failures(args.design, include_failed=False)
    if args.start is not None:
        start = find_failure(args.start, all_failurez)
    else:
        start = 0
    if args.stop is not None:
        stop = find_failure(args.stop, all_failurez)
    else:
        stop = len(all_failurez)-1
        
    for i in range(start,stop+1):
        failure = all_failurez[i]
        print failure
        if args.new_suffix is None:
            success = run_debug_prediction.main(failure, verbose=args.verbose)
        else:
            if args.min_runtime > 0:
                runtime = utils.parse_runtime(failure)
                if runtime < args.min_runtime:
                    print "Ignoring failure %s, runtime is too short" %(failure)
                    continue
            success = run_debug_prediction.main(failure, failure+args.new_suffix, args.min_suspects, args.aggressiveness, 
                guidance_method=args.method, timeout=args.timeout, pass_timeout=args.pass_timeout, verbose=args.verbose)
        
        if not success:
            unsuccessful.append(failure)
        print "" 
    
    if len(unsuccessful) > 0:
        print "The following runs were unsuccessful:"
        for f in unsuccessful:
            print f 
        
    
def init(parser):
    parser.add_argument("design")
    parser.add_argument("new_suffix", nargs='?', default=None, help="Suffix to append to the name of the new project")
    parser.add_argument("--start",help="Failure (suffix) to start running at")
    parser.add_argument("--stop",help="Failure (suffix) to stop running at")
    parser.add_argument("--min_suspects", type=int, default=999999, help="Minimum number of suspects to "\
        "find before predicting")
    parser.add_argument("--aggressiveness", type=float, default=0.5, help="Threshold below which suspects are blocked")
    parser.add_argument("--timeout", type=int, default=3600, help="Time limit in seconds for a single debugging run.")
    parser.add_argument("--pass_timeout", type=int, default=100000, help="Time limit in seconds for a single pass.")
    parser.add_argument("-v","--verbose", action="store_true", default=False, help="Display more info")
    parser.add_argument("--method", type=str, default=None, help="Solver guidance method. " \
        "Must be one of %s" %run_debug_prediction.METHODS)
    parser.add_argument("--min_runtime", type=int, default=0, help="Don't run failures with runtime less than this.")
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args()
    main(args)