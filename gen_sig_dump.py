import os
import argparse
import verilog_parser

def init(parser):
    parser.add_argument("file")
    parser.add_argument("--types",default="output,inout")
    parser.add_argument("--dut_path",default="DUT_PATH")
    parser.add_argument("--verbose","-v",action="store_true",default=False) 

def main(args):
    if not os.path.exists(args.file):
        print "Error: file %s does not exist" %(args.file)
        return None 
        
    #parse all signals of specified types from verilog 
    rtl = verilog_parser.VerilogParser(args.file)
    typez = args.types.split(",")
    rtl.parse_ifdefs()
    rtl.parse_signals()
    signalz = []
    for s in rtl.signalz:
        if s._type in typez:
            signalz.append(s)
    
    print "reg debug_clk;"
    print "initial debug_clk = 1;"
    print "always #50 debug_clk = ~debug_clk;"
    for s in signalz:
        if s.ifdef != None:
            print "`ifdef",s.ifdef
        print "reg %s prev_%s;" %(s.get_size(),s.name)
        if s.ifdef != None:
            print "`endif"
    print "always @(posedge debug_clk) begin"
    
    print "    if ("
    for s in signalz[:-1]:
        if s.ifdef != None:
            print "`ifdef",s.ifdef
        print "        %s.%s != prev_%s ||" %(args.dut_path,s.name,s.name)
        if s.ifdef != None:
            print "`endif"
    print "        %s.%s != prev_%s )" %(args.dut_path,signalz[-1].name,signalz[-1].name)
    print "        $display(\"Signals at %t\",$time);"
    
    for s in signalz:
        if s.ifdef != None:
            print "`ifdef",s.ifdef
        print "    if (%s.%s != prev_%s)" %(args.dut_path,s.name,s.name)
        print "        $display(\"%s = %%h\",%s.%s);" %(str(s),args.dut_path,s.name)
        print "    prev_%s <= %s.%s;" %(s.name,args.dut_path,s.name)
        if s.ifdef != None:
            print "`endif"
    print "end"
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    init(parser)
    args = parser.parse_args() 
    main(args)
