import os
import argparse
import re

SIGNAL_PATTERN = r"((?:wire)|(?:reg)|(?:input)|(?:output)|(?:inout))\s+(?:\[\s*(\d+)\s*:\s*(\d+)\s*\])?((?:[\w,\s]*;)|(?:[\w\s]*?,))"
MODULE_PATTERN = r"\bmodule\b\s+(\w+).*?\bendmodule\b"
IFDEF_PATTERN = r"`ifdef\s+(\w+)(.*?)`endif\b"

def init(parser):
    parser.add_argument("filename")    


class Signal(object):
    def __init__(self, name, _type, high=None, low=0, ifdef=None):
        self.name = name.strip()
        self._type = _type.strip()
        self.high = high
        self.low = low 
        self.ifdef = ifdef
        
    def __str__(self):
        return "%s%s" %(self.name,self.get_size())
            
    def get_size(self):
        if self.high == None:
            return ""
        else:
            return "[%i:%i]" %(self.high,self.low)
            
            
class Module(object):
    def __init__(self,name,start_line,end_line):
        self.name = name 
        self.start_line = start_line
        self.end_line = end_line
        
    def __str__(self):
        return "module %s, lines %i-%i" %(self.name,self.start_line,self.end_line)
    
    
class VerilogParser(object):

    def __init__(self, filename):
        self.filename = filename
        self.text = open(filename).read()
        self.sanitize_text()
        self.signalz = []
        self.modulez = []
        self.ifdefz = []
        
    @staticmethod 
    def find_end_with_brackets(text, start_idx, end_symbol):
        '''
        Return the first index i such that:
            start_idx <= i <= len(text) 
            text[i] = end_symbol 
            text[start_idx:i+1] has balanced parentheses
        '''
        depth = 0
        for i in xrange(start_idx, len(text)):
            if text[i] in "([{":
                depth += 1
            elif text[i] in ")]}":
                depth -= 1
                
            if text[i] == end_symbol and depth == 0:
                return i
        return i
            
    @staticmethod        
    def check_str_in_brackets(text, substr):
        '''
        Return true iff the given substring does not occur inside brackets within text.
        '''
        bracket_depth = 0
        for j in xrange(text.find(substr)):
            if text[j] in "([{":
                bracket_depth += 1
            elif text[j] in ")]}":
                bracket_depth -= 1
        return bracket_depth == 0
        
        
    def sanitize_text(self):
        '''
        Remove all comments from text. Every character in a comment section 
        is replaced with a space characeter, except '\n' characters which 
        are preserved. 
        '''
        self.sanitized_text = self.text
        init_len = len(self.sanitized_text)
        comment = 0 
        i = 0
        while i < init_len:
            if self.sanitized_text[i:i+2] == "//":
                #go to end of line
                j = i+2 
                while j < init_len and self.sanitized_text[j] != "\n":
                    j += 1 
                replace_str = " "*(j-i)
                self.sanitized_text = self.sanitized_text[:i] + replace_str + self.sanitized_text[j:]
                i = j
            elif self.sanitized_text[i:i+2] == "/*":
                #go until "*/" string
                j = i+2 
                replace_str = "  "
                while j < init_len and self.sanitized_text[j-2:j] != "*/":
                    if self.sanitized_text[j] == "\n":
                        replace_str += "\n"
                    else: 
                        replace_str += " "
                    j += 1 
                assert len(replace_str) == j-i
                self.sanitized_text = self.sanitized_text[:i] + replace_str + self.sanitized_text[j:]
                i = j
            else:
                i += 1
            assert len(self.sanitized_text) == init_len
            
            
    def parse_signals(self):
        self.signalz = []
        signal_namez = []
        for ifdef,code in self.ifdefz:
            for m in re.findall(SIGNAL_PATTERN, code):
                name = name.strip(",; ").strip()
                if len(name) == 0: 
                    continue 
                for name in m[3].split(","):
                    if m[1] == "":
                        s = Signal(name,m[0],ifdef=ifdef)
                    else:
                        s = Signal(name,m[0],int(m[1]),int(m[2]),ifdef=ifdef)
                    self.signalz.append(s)
                    signal_namez.append(name)
                    
        for m in re.findall(SIGNAL_PATTERN, self.sanitized_text):
            for name in m[3].split(","):
                name = name.strip(",; ").strip()
                if len(name) == 0: 
                    continue 
                if name not in signal_namez:
                    if m[1] == "":
                        s = Signal(name,m[0])
                    else:
                        s = Signal(name,m[0],int(m[1]),int(m[2]))
                    self.signalz.append(s)
                    signal_namez.append(name)
                
                
    def parse_modules(self):
        self.modulez = []
        m = re.search(MODULE_PATTERN,self.sanitized_text,flags=re.DOTALL)
        while m != None:
            start = self.sanitized_text.find(m.group(0))
            end = start + len(m.group(0))
            start_line = self.sanitized_text[:start].count("\n")+1
            end_line = self.sanitized_text[:end].count("\n")+1
            self.modulez.append(Module(m.group(1),start_line,end_line))
            m = re.search(MODULE_PATTERN,self.sanitized_text[end:],flags=re.DOTALL) 

            
    def parse_ifdefs(self):
        self.ifdefz = []
        for m in re.findall(IFDEF_PATTERN, self.sanitized_text, flags=re.DOTALL):
            self.ifdefz.append(m)
    
     
    def get_module(self,line_num):
        for m in self.modulez:
            if m.start_line <= line_num <= m.end_line:
                return m.name
     

def main(args):
    if not os.path.exists(args.filename):
        print "Error: file %s does not exist" %(args.filename)
        return None 
        
    parser = VerilogParser(args.filename)
    parser.parse_modules()
    print "Modules:"
    for module in parser.modulez:
        print module
        
    parser.parse_ifdefs()
    print "\nifdefs:"
    for name,code in parser.ifdefz:
        print name
        print code
        
    print "\nsignals:"
    parser.parse_signals()
    for s in parser.signalz:
        print s.ifdef,s
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args() 
    main(args)
