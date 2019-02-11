import os 
import re 

os.chdir("designs/mips789")

for i in range(0,35):
	if os.path.exists("random_bug_%i" %(i)):
		for item in ["rtl","filelist.l","bug_desc.txt"]:
			fname = "random_bug_%i/%s" %(i,item)
			if os.path.exists(fname):
				cmd = "git add -f " + fname 
				print cmd 
				os.system(cmd)
		
		for item in os.listdir("random_bug_%i" %(i)):
			if re.match(r"fail_\d+\.template", item):
				cmd = "git add -f random_bug_%i/%s" %(i,item)
				print cmd 
				os.system(cmd) 
