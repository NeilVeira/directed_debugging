import os 
import argparse
import re 
import pickle 
import pandas as pd 
import numpy as np

import analyze  
import utils 

designs = ["ethernet", "fdct", "wb_dma", "mips789", "sudoku_check", "vga", "scam_core", "smoac_core"]
designs = ["mips789", "sudoku_check", "vga", "scam_core", "smoac_core"] 
suffixes = ["_1pass", "", "_multipass_DATE", "_multipass_v2", "_multipass_opt"]
RESULT_FILE = "debug_results.csv"

if os.path.exists(RESULT_FILE):
    results = pd.read_csv(RESULT_FILE, index_col=0)
else:
    results = pd.DataFrame(columns = ["experiment", "runtime", "finished", "R", "speedup"])


for design in designs: 
    for suffix in suffixes :
        failurez = utils.find_all_failures("designs/"+design)
        
        for f in failurez:
            if "_multipass" in suffix:
                base = f 
            else:
                base = f + "_1pass" 
            new = f + suffix
            
            R, speedup, runtime, _, _, runs_finished = analyze.analyze(base, new, verbose=False, min_runtime=0)
            if R is not None:
                if "_multipass" in suffix:
                    # convert to vs _1pass 
                    base_row = results.loc[results["experiment"] == f]
                    if len(base_row) > 0:
                        base_R = base_row.iloc[0]["R"]
                        base_speedup = base_row.iloc[0]["speedup"]
                        R *= base_R 
                        speedup *= base_speedup
                
                row = {"experiment":new, "runtime":runtime, "finished":runs_finished[1], "R":R, "speedup":speedup}
                results = results.append(row, ignore_index=True)
                    
        results.drop_duplicates(subset=["experiment"], inplace=True, keep="last")
        results.sort_values(by=["experiment"], inplace=True)
        results.reset_index(drop=True, inplace=True)
        results.to_csv(RESULT_FILE)
