import os
import argparse
import re
import logging

SIGNAL_PATTERN = r"((?:wire)|(?:reg)|(?:input)|(?:output)|(?:inout)|(?:tri))\s+(?:\[\s*(\d+)\s*:\s*(\d+)\s*\])?((?:[\w,\s]*;)|(?:[\w\s]*?,))"
MODULE_PATTERN = r"\bmodule\b\s+(\w+).*?\bendmodule\b"
IFDEF_PATTERN = r"`ifdef\s+(\w+)(.*?)`endif\b"
INSTANCE_PATTERN = r"\b(\w+)\s+(\w+)\s*\((.*?)\);"

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
        

class Instance(object):
    def __init__(self, _type, name):
        self._type = _type 
        self.name = name 
        self.portx = {}
        self.port_indicex = {}
    
    def add_port(self, name, value, start_idx, end_idx):
        self.portx[name] = value 
        self.port_indicex[name] = (start_idx, end_idx)
        
    def __str__(self):
        ret = "instance %s %s\n" %(self._type, self.name)
        for port in self.portx:
            ret += "    %s (%s)\n" %(port, self.portx[port])
        return ret 
    
    
class VerilogParser(object):

    def __init__(self, filename):
        self.filename = filename
        self.text = open(filename).read()
        self.sanitize_text()
        self.signalz = []
        self.modulez = []
        self.ifdefz = []
        self.instancez = []
        
    @staticmethod 
    def find_end_with_brackets(text, start_idx, end_symbol):
        '''
        Return the first index i such that:
            start_idx <= i <= len(text) 
            text[i] = end_symbol 
            text[start_idx:i+1] has balanced parentheses
        '''
        depth = 0
        i = start_idx
        while i < len(text):
            if text[i] in "([{":
                depth += 1
            elif text[i] in ")]}":
                depth -= 1
                
            if text[i] == end_symbol and depth == 0:
                return i
            i += 1
        return i
        
    @staticmethod
    def split_with_brackets(text, delimiter):
        '''
        Return a list of text split by the given delimeter character while respecting brackets 
        '''
        parts = []
        prev = 0
        while prev < len(text):
            nxt = VerilogParser.find_end_with_brackets(text, prev, delimiter)
            parts.append(text[prev:nxt])
            prev = nxt+1
        return parts 
            
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
            m = re.search(MODULE_PATTERN, self.sanitized_text[end:], flags=re.DOTALL) 

            
    def parse_ifdefs(self):
        self.ifdefz = []
        for m in re.findall(IFDEF_PATTERN, self.sanitized_text, flags=re.DOTALL):
            self.ifdefz.append(m)
    
 
    def parse_instances(self):
        self.instancez = []
        m = re.search(INSTANCE_PATTERN, self.sanitized_text, flags=re.DOTALL)
        prev_idx = 0
        while m:
            _type, name = m.group(1), m.group(2)
            inst_start = self.sanitized_text.find(m.group(0), prev_idx)
            assert inst_start != -1 
            inst_end = VerilogParser.find_end_with_brackets(self.sanitized_text, inst_start, ";")
            content = self.sanitized_text[inst_start:inst_end]
            
            if _type not in ["module","else","if","begin","end"]: # follows the same syntax but is not an instantiation
                inst = Instance(_type, name)
                # print _type,name
                ports = VerilogParser.split_with_brackets(content, ",")
                for port in ports:
                    # print port 
                    inst_start = self.sanitized_text.find(port, prev_idx+1)
                    assert 0 <= inst_start < inst_end 
                    prev_idx = inst_start+1 
                    m = re.search(r"\.(\w+)\s*\((.*)\)", port)
                    
                    if m: 
                        port_name = m.group(1)                       
                        port_val = m.group(2)
                        port_start_idx = self.sanitized_text.find(m.group(0), inst_start)
                        assert 0 <= inst_start < inst_end 
                        # Note: don't use m.group(0) since it isn't guaranteed to follow brackets 
                        # End of this port could be a comma or a semicolon if it's the last port 
                        port_end_idx1 = VerilogParser.find_end_with_brackets(self.sanitized_text, port_start_idx, ",")
                        port_end_idx2 = self.sanitized_text[:inst_end].rfind(")") -1 # closing bracket before the semicolon 
                        port_end_idx = min(port_end_idx1, port_end_idx2)
                        if port_end_idx <= port_start_idx:
                            logging.warning("Tried to parse instance %s %s which seems to be invalid; aborting" %(_type,name))
                            break 
                        
                        inst.portx[port_name] = port_val 
                        inst.port_indicex[port_name] = (port_start_idx, port_end_idx)     
                        
                else:
                    self.instancez.append(inst)
            
            m = re.search(INSTANCE_PATTERN, self.sanitized_text[inst_end:], flags=re.DOTALL) 
            
 
    def get_module(self,line_num):
        for m in self.modulez:
            if m.start_line <= line_num <= m.end_line:
                return m.name
     

def main(args):
    if not os.path.exists(args.filename):
        print "Error: file %s does not exist" %(args.filename)
        return None 
        
    parser = VerilogParser(args.filename)
    # parser.parse_modules()
    # print "Modules:"
    # for module in parser.modulez:
        # print module
        
    # parser.parse_ifdefs()
    # print "\nifdefs:"
    # for name,code in parser.ifdefz:
        # print name
        # print code
        
    # print "\nsignals:"
    # parser.parse_signals()
    # for s in parser.signalz:
        # print s.ifdef,s
        
    print "\nInstances:"
    parser.parse_instances()
    for inst in parser.instancez:
        print inst
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args() 
    main(args)
