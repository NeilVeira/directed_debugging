import os
import subprocess
import argparse
import re
import random
import verilog_parser

ASSIGN_PATTERN = r"((?:parameter\s*)|(?:localparam\s*))?((?:assign\s+)?[\w\[\]:]+\s*<?=)[^=].*?;"
CONDITION_PATTERN = r"\W(if\s*\(.*?\))"
OPERATOR_PATTERN = r"([\*\+\-&\|\^])"


class BugManager(verilog_parser.VerilogParser):
    def __init__(self,filename):
        verilog_parser.VerilogParser.__init__(self,filename)
        self.bugx = {}
        for bug_type in BUG_TYPEX.keys():
            self.bugx[bug_type] = BUG_TYPEX[bug_type].parse(self.text, self.sanitized_text, self.filename)
    
    
class Bug(object):

    def __init__(self, filename, full_text, start_idx, end_idx):
        self.filename = filename
        self.start_idx = start_idx 
        self.end_idx = end_idx 
        self.full_text = full_text
        self.line = full_text[:start_idx].count("\n")+1
        self.golden_text = full_text[start_idx:end_idx+1]
        self.buggy_text = ""
        self.bug_type = "unknown"
        
    def get_desc(self):
        desc = "Bug Description: %s\n" %(self.bug_type)
        desc += "Location: \t%s : %i\n" %(self.filename, self.line)
        desc += "Golden:   \t%s\n" %(self.golden_text)
        desc += "Bug:      \t%s\n" %(self.buggy_text)
        return desc
        
    def __str__(self):
        return "%s, line %i: %s" %(self.filename, self.line, self.buggy_text)
        
    def inject(self):
        '''
        Inject the buggy text into self.full text, marking the location. 
        '''
        self.full_text = self.full_text[:self.start_idx] + self.buggy_text + self.full_text[self.end_idx+1:]        
        linez = self.full_text.split("\n")
        linez.insert(self.line-1, "//BUG HERE")
        linez.insert(self.line, "/*"+self.golden_text+"*/")
        self.line += 2+self.golden_text.count("\n")
        self.full_text = "\n".join(linez)        
        
    def write(self):
        f = open(self.filename,"w")
        f.write(self.full_text)
        f.close()
        desc_f = open("bug_desc.txt","w")
        desc_f.write(self.get_desc())
        desc_f.close()
        
        
class Assignment(Bug):

    def __init__(self, filename, full_text, start_idx, end_idx, asgn_var):
        Bug.__init__(self, filename, full_text, start_idx, end_idx)
        self.asgn_var = asgn_var
        
    def apply(self):
        val = random.randint(0,1)
        self.bug_type = "stuck-at-%i" %(val)
        self.buggy_text = "%s %i;" %(self.asgn_var,val)
        self.inject()
        
    @staticmethod
    def parse(full_text, sanitized_text, filename):
        '''
        Parse all assignment statements from text according to ASSIGN_PATTERN.
        Return a list of Assignment objects for them. 
        '''
        bugz = []
        prev = 0
        for m in re.finditer(ASSIGN_PATTERN, sanitized_text, flags=re.DOTALL):
            #don't try to parse paramenter assignments
            if m.group(1) != None:
                continue 
            #Some conditional statements look syntatically like assignments and would match.
            #They can be filtered by checking that m is not inside brackets. 
            if not verilog_parser.VerilogParser.check_str_in_brackets(sanitized_text[prev:], m.group(0)):
                continue
                
            start_idx = sanitized_text.find(m.group(0), prev)
            assert start_idx != -1
            end_idx = verilog_parser.VerilogParser.find_end_with_brackets(sanitized_text, start_idx, ";")
            asgn = Assignment(filename, full_text, start_idx, end_idx, m.group(2))
            bugz.append(asgn)
            prev = end_idx+1
        return bugz
        
        
class Condition(Bug):
            
    def __init__(self, filename, full_text, start_idx, end_idx):
        Bug.__init__(self, filename, full_text, start_idx, end_idx)
        self.bug_type = "incorrect condition"
        
    def apply(self):
        self.buggy_text = "if (1)"
        self.inject()
        
    @staticmethod
    def parse(full_text, sanitized_text, filename):
        '''
        Parse all if condition statements and return list of Condition objects 
        for them. 
        '''
        bugz = []
        prev = 0
        for m in re.finditer(CONDITION_PATTERN, sanitized_text, flags=re.DOTALL):
            start_idx = sanitized_text.find(m.group(0), prev)
            start_idx = sanitized_text.find(m.group(1), start_idx)
            assert start_idx != -1 
            end_idx = verilog_parser.VerilogParser.find_end_with_brackets(sanitized_text, start_idx, ")")
            cond = Condition(filename, full_text, start_idx, end_idx)
            bugz.append(cond)
            prev = end_idx+1
        return bugz


class Operator(Bug):
    operator_classes = [["+","-","*"],["^","|","&"]] # defines which operators can be interchanged for each other
    
    def __init__(self, filename, full_text, start_idx, end_idx):
        Bug.__init__(self, filename, full_text, start_idx, end_idx)
        self.bug_type = "incorrect operator"
        
    def apply(self):
        # find operator class and pick a different item from it 
        op = self.full_text[self.start_idx]
        print "op =",op
        op_class = [op_class for op_class in Operator.operator_classes if op in op_class][0]
        new_op = random.choice(op_class)
        while new_op == op:
            new_op = random.choice(op_class)
        self.buggy_text = new_op 
        self.inject()
    
    @staticmethod 
    def parse(full_text, sanitized_text, filename):
        bugz = []
        prev = 0
        for m in re.finditer(OPERATOR_PATTERN, sanitized_text, flags=re.DOTALL):
            start_idx = sanitized_text.find(m.group(0), prev)
            start_idx = sanitized_text.find(m.group(1), start_idx)
            assert start_idx != -1 
            end_idx = start_idx
            cond = Operator(filename, full_text, start_idx, end_idx)
            bugz.append(cond)
            prev = end_idx+1
        return bugz

    
    
'''
Possible further bugs:
    Incorrect binary operator (+, -, *, ^, |, &), (<, >)
    Incorrect signal bit fields
    Incorrect timing delays
'''
        

BUG_TYPEX = {"assignment" :  Assignment,
            "condition" :  Condition,
            "operator" : Operator,
            }
    
    
def get_files():
    '''
    Get list of rtl_obj files
    '''
    filelist = open("filelist.l").readlines()
    filez = []
    for line in filelist:
        line = line.strip()
        if line != "" and os.path.exists(line) and "rtl/" in line and (line.endswith(".v") or line.endswith(".sv")):
            filez.append(line)
    return filez
    
    
def inject_bug(filename, bug_type="assignment", verbose=False, dryrun=False, blacklist=[], log=None):
    '''
    Inject a random bug into the given verilog file f. 
    blacklist: list of bug strings not to inject (only intended for use by build_data.py)
    Returns string describing the injected bug, or None if unsuccessful
    '''
    print "Injecting %s bug into file %s" %(bug_type,filename)
    if log != None:
        log.write("Injecting %s bug into file %s\n" %(bug_type,filename))
        
    if not BUG_TYPEX.has_key(bug_type):
        print "Error: unknown bug type",bug_type
        return None
    
    rtl_obj = BugManager(filename)
    bugz = rtl_obj.bugx[bug_type]
    if len(bugz) == 0:
        if verbose:
            print "Error: no %s bugs found in file %s" %(bug_type,filename)
            if log:
                log.write("Error: no %s bugs found in file %s\n" %(bug_type,filename))
        return None 
        
    #pick random item from bugz which is not in blacklist
    random.shuffle(bugz)
    for i in xrange(len(bugz)):
        bug = bugz[i]
        if str(bug) not in blacklist:
            break
    else:
        print "Error: all possible bugs in file %s are blacklisted" %(filename)
        if log:
            log.write("Error: all possible bugs in file %s are blacklisted\n" %(filename))
        return None
    
    bug.apply()
    #print bug.full_text
    if verbose:
        print "line %i: %s" %(bug.line, bug.golden_text)
        print "changed to %s" %(bug.buggy_text)
        if log:
            log.write("line %i: %s\n" %(bug.line, bug.golden_text))
            log.write("changed to %s\n" %(bug.buggy_text))
    if not dryrun:
        bug.write()
    return bug
    
        
def main(design_dir, bug_type, verbose=False, dryrun=False):
    if not os.path.isdir(design_dir):
        print "Error: no directory",design_dir
        return False  
        
    os.chdir(design_dir)
    filez = get_files()
    #pick a random file in design_dir/rtl_obj
    # f = random.choice(filez)
    f = "rtl/aeMB_decode.v"
    inject_bug(f, bug_type, verbose, dryrun)
    
    

def init(parser):
    parser.add_argument("design_dir",help="Design to insert fault into")
    parser.add_argument("--bug_type",default="assignment",help="Type of bug to insert." \
        + " Currently supported types: "+str(BUG_TYPEX.keys()))
    parser.add_argument("--dryrun","-n",action="store_true",default=False)
    parser.add_argument("--verbose","-v",action="store_true",default=False)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args() 
    main(args.design_dir.rstrip("/"), args.bug_type, args.verbose, args.dryrun)

