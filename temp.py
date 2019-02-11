import os

fail_list = '''
random_bug_13/fail_1
random_bug_15/fail_1
random_bug_16/fail_0
random_bug_16/fail_2
random_bug_18/fail_0
random_bug_18/fail_1
random_bug_1/fail_3
random_bug_20/fail_0
random_bug_20/fail_1
random_bug_21/fail_0
random_bug_21/fail_2
random_bug_23/fail_0
random_bug_23/fail_1
random_bug_23/fail_2
random_bug_25/fail_1
random_bug_2/fail_0
random_bug_3/fail_0
random_bug_4/fail_0
random_bug_4/fail_2
random_bug_5/fail_0
random_bug_6/fail_0
random_bug_6/fail_1
random_bug_7/fail_0
random_bug_7/fail_1
random_bug_9/fail_0
random_bug_9/fail_2'''
fail_list = fail_list.split()

os.chdir("designs/mips789")

for f in fail_list:
	print f 
	os.chdir(os.path.dirname(f))
	template_file = os.path.basename(f)+".template"
	print template_file 
	os.system("onpoint-cmd --template-file="+template_file)
	os.chdir("..")
