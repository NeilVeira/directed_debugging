import subprocess 
import argparse 
import re 
import numpy as np

DESIGNS = ["aemb","divider","ethernet","fdct","fpu","mips789","rsdecoder","scam_core","spi","vga"]
LAMBDS = [0.1, 0, 0, 0, 0.1, 0.1, 0, 0, 0, 0.1]

def experiment_suspect2vec(args):
    base = []
    new = []
    for design,lambd in zip(DESIGNS,LAMBDS):
        cmd = "python experiments.py data/%s %s" %(design,args.args)
        if args.lambd:
            cmd += " --lambd=%.1f" %(lambd)
        print(cmd)
        stdout,stderr = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE).communicate()
        m = re.search(r"Base metrics:.*f1-score = ([\d\.]+).*New metrics:.*f1-score = ([\d\.]+)", stdout, flags=re.DOTALL)
        base_score = float(m.group(1))
        new_score = float(m.group(2))
        print("%.3f %.3f" %(base_score, new_score))
        base.append(base_score)
        new.append(new_score)
    print("mean: %.3f" %(np.mean(new)))
    print("")
    for val in new:
        print("%.3f" %(val))
        
        
def experiment_train_size(args):
    basez = [[] for _ in range(5)]
    newz = [[] for _ in range(5)]
    for design,lambd in zip(DESIGNS,LAMBDS):
        cmd = "python experiments.py data/%s --experiment=train_size %s" %(design,args.args)
        if args.lambd:
            cmd += " --lambd=%.1f" %(lambd)
        print(cmd)
        stdout,stderr = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE).communicate()
        #print(stdout)
        
        pattern = r"Training size ([\d\.]+)\s+Base f1-score: ([\d\.]+)\s+New f1-score: ([\d\.]+)"
        for i,m in enumerate(re.findall(pattern, stdout, flags=re.DOTALL)):
            base = float(m[1])
            new = float(m[2])
            basez[i].append(base)
            newz[i].append(new)
            
        print("Base: %s" %(basez[-1]))
        print("New: %s" %(newz[-1]))
    
    basez = np.mean(basez, axis=1)
    newz = np.mean(newz, axis=1)
    for i in range(5):
        print("%.4f\t%.4f" %(basez[i],newz[i]))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--args",default="")
    parser.add_argument("--lambd",action="store_true",default=False,help="Do lambda hack")
    parser.add_argument("--experiment",default="suspect2vec",help="'suspect2vec' or 'train_size'")
    args = parser.parse_args()
    
    if args.experiment == "suspect2vec":
        experiment_suspect2vec(args)
    elif args.experiment == "train_size":
        experiment_train_size(args)
    else:
        raise ValueError("Unknown experiment %s" %(args.experiment))
