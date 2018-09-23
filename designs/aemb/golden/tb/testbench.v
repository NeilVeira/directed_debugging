/*
 * $Id: testbench.v,v 1.5 2007/05/30 18:44:45 sybreon Exp $
 * 
 * AEMB Generic Testbench
 * Copyright (C) 2004-2007 Shawn Tan Ser Ngiap <shawn.tan@aeste.net>
 *  
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
 * USA
 *
 * DESCRIPTION
 * Top level test bench and fake RAM/ROM.
 *
 * HISTORY
 * $Log: testbench.v,v $
 * Revision 1.5  2007/05/30 18:44:45  sybreon
 * Added interrupt support.
 *
 * Revision 1.4  2007/04/30 15:56:50  sybreon
 * Removed byte acrobatics.
 *
 * Revision 1.3  2007/04/27 15:18:43  sybreon
 * Minor updates as sw/c/aeMB_testbench.c got updated.
 *
 * Revision 1.2  2007/04/25 22:15:05  sybreon
 * Added support for 8-bit and 16-bit data types.
 *
 * Revision 1.1  2007/04/12 20:21:34  sybreon
 * Moved testbench into /sim/verilog.
 * Simulation cleanups.
 *
 */

module testbench ();
    parameter ISIZ = 16;
    parameter DSIZ = 16;   

   
    // INITIAL SETUP //////////////////////////////////////////////////////
   
    reg 	     sys_clk_i, sys_rst_i, sys_int_i, sys_exc_i;
    reg 	     svc;
    integer   inttime;
    
    always #5 sys_clk_i = ~sys_clk_i;   
    
    //initial begin
    //    $dumpfile("dump.vcd");
    //    $dumpvars(1,dut);
    //end
    
    initial begin
        inttime = ($random % 143 * 7) + 2000;      
        svc = 0;      
        sys_clk_i = 1;
        sys_rst_i = 0;
        sys_int_i = 0;
        sys_exc_i = 0;      
        #10 sys_rst_i = 1;
    end
    
    initial fork
        #inttime $display("FSADFASDFSDAF");      
        #1010 sys_int_i = 1;
        #1000 sys_int_i = 0;
        #100000 $displayh("\nTest Completed."); 
        #11000 $finish;
    join   
    
    // FAKE MEMORY ////////////////////////////////////////////////////////
    
    wire [ISIZ-1:0] iwb_adr_o;
    wire 	   iwb_stb_o;
    wire 	   dwb_stb_o;
    reg [31:0] 	   rom [0:65535];
    wire [31:0] 	   iwb_dat_i;
    reg 		   iwb_ack_i, dwb_ack_i;

    reg [31:0] 	   ram[0:65535];
    wire [31:0] 	   dwb_dat_i;
    reg [31:0] 	   dwblat;
    wire 	   dwb_we_o;
    reg [DSIZ-1:2]  dadr,iadr;
    wire [3:0] 	   dwb_sel_o; 
    wire [31:0] 	   dwb_dat_o;
    wire [DSIZ-1:0] dwb_adr_o;
    wire [31:0] 	   dwb_dat_t;   
    
    assign 	   {dwb_dat_i[7:0],dwb_dat_i[15:8],dwb_dat_i[23:16],dwb_dat_i[31:24]} = ram[dadr];
    assign 	   {iwb_dat_i[7:0],iwb_dat_i[15:8],iwb_dat_i[23:16],iwb_dat_i[31:24]} = ram[iadr];
    assign 	   {dwb_dat_t} = ram[dwb_adr_o[DSIZ-1:2]];
    
    always @(posedge sys_clk_i) begin
        iwb_ack_i <= #1 iwb_stb_o;
        dwb_ack_i <= #1 dwb_stb_o;
        iadr <= #1 iwb_adr_o[ISIZ-1:2];
        dadr <= dwb_adr_o[DSIZ-1:2];
        
        if (dwb_we_o & dwb_stb_o) begin
	        case (dwb_sel_o)
	            4'h1: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_o[7:0],dwb_dat_t[23:0]};
	            4'h2: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_t[31:24],dwb_dat_o[15:8],dwb_dat_t[15:0]};	   
	            4'h4: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_t[31:16],dwb_dat_o[23:16],dwb_dat_t[7:0]};	   
	            4'h8: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_t[31:8],dwb_dat_o[31:24]};	   
	            4'h3: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_o[7:0],dwb_dat_o[15:8],dwb_dat_t[15:0]};	   
	            4'hC: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_t[31:16],dwb_dat_o[23:16],dwb_dat_o[31:24]};	   	  
	            4'hF: ram[dwb_adr_o[DSIZ-1:2]] <= {dwb_dat_o[7:0],dwb_dat_o[15:8],dwb_dat_o[23:16],dwb_dat_o[31:24]};	   
	        endcase // case (dwb_sel_o)	 
        end
    end

    integer i;   
    initial begin
        for (i=0;i<65535;i=i+1) begin
	        ram[i] <= $random;
        end      
        #1 $readmemh("aeMB.rom",ram);
    end

    // DISPLAY OUTPUTS ///////////////////////////////////////////////////

    always @(negedge sys_clk_i) begin

        // Time
        $write("\nT: ",($stime / 10));
        
        // Data Monitors
        if (iwb_stb_o & iwb_ack_i)
	        $writeh("\t @",iwb_adr_o,":",iwb_dat_i);      
        if (dwb_stb_o & dwb_we_o & dwb_ack_i) 
	        $writeh("\t @",dwb_adr_o,"<-",dwb_dat_o,"#",dwb_sel_o);     
        if (dwb_stb_o & ~dwb_we_o & dwb_ack_i)
	        $writeh("\t @",dwb_adr_o,"->",dwb_dat_i,"#",dwb_sel_o);
        if (dut.regfile.wDWE)
	        $writeh("\t R",dut.regfile.rRD_,"=",dut.regfile.wDDAT,";");

        // Interrupt Monitors
        if ($stime > inttime) begin
	        sys_int_i = 1;
	        svc = 0;	 
        end      
        if (($stime > inttime+500) && !svc) begin
	        $display("\n\t*** INTERRUPT TIMEOUT ***", inttime);	 
	        $finish;	 
        end    
        if (dwb_we_o & (dwb_dat_o == "RTNI")) begin
	        sys_int_i = 0;	 
        end      
        if (dut.control.rFSM == 2'o1) begin
	        $writeh("\tINTR: ",(($stime-inttime)/10), " cycles");
	        inttime = ($random % 181 * 11) + $stime + 5000;	 
	        svc = 1;
        end

        // Pass/Fail Monitors
        if (dwb_we_o & (dwb_dat_o == "FAIL")) begin
	        $display("\n\tFAIL");	 
	        $finish;
        end      
        if (iwb_dat_i == 32'hb8000000) begin
	        $display("\n\t*** PASSED ALL TESTS ***");
	        $finish;	 
        end
    end // always @ (posedge sys_clk_i)

    // INTERNAL WIRING ////////////////////////////////////////////////////
    
    aeMB_core #(ISIZ,DSIZ)
    dut (
	     .sys_int_i(sys_int_i),.sys_exc_i(sys_exc_i),
	     .dwb_ack_i(dwb_ack_i),.dwb_stb_o(dwb_stb_o),.dwb_adr_o(dwb_adr_o),
	     .dwb_dat_o(dwb_dat_o),.dwb_dat_i(dwb_dat_i),.dwb_we_o(dwb_we_o),
	     .dwb_sel_o(dwb_sel_o),
	     .iwb_adr_o(iwb_adr_o),.iwb_dat_i(iwb_dat_i),.iwb_stb_o(iwb_stb_o),
	     .iwb_ack_i(iwb_ack_i),
	     .sys_clk_i(sys_clk_i), .sys_rst_i(sys_rst_i)
	     );


    `ifdef GOLDEN
    // Produce the reference rom file
    integer ref_file;
    initial begin
        ref_file=$fopen("ref.rom", "w");
    end
    always @(negedge sys_clk_i) begin
        $fdisplay(ref_file, "%h%h%h", iwb_adr_o, dwb_adr_o, dwb_dat_o);
    end
    `else
    // Checkers
    reg [63:0] 	ref_ram[0:65535];    
    initial begin
        $readmemh("ref.rom",ref_ram);
    end
    integer ref_adr=0;
    wire [15:0] ref_iwb_adr_o=ref_ram[ref_adr][63:48];
    wire [15:0] ref_dwb_adr_o=ref_ram[ref_adr][47:32];
    wire [31:0] ref_dwb_dat_o=ref_ram[ref_adr][31:0];
    
    parameter MAX_ERROR=3;
    integer error_cnt=0;
    always@(negedge sys_clk_i) begin
        ref_adr <= ref_adr + 1;
        if (ref_iwb_adr_o != iwb_adr_o) begin
            $display("%t: ERROR: iwb_adr_o exp: %h, got %h", $time, ref_iwb_adr_o, iwb_adr_o);
            error_cnt = error_cnt + 1;
        end
        if (ref_dwb_adr_o != dwb_adr_o) begin
            $display("%t: ERROR: dwb_adr_o exp: %h, got %h", $time, ref_dwb_adr_o, dwb_adr_o);
            error_cnt = error_cnt + 1;
        end
        if (ref_dwb_dat_o != dwb_dat_o) begin
            $display("%t: ERROR: dwb_dat_o exp: %h, got %h", $time, ref_dwb_dat_o, dwb_dat_o);
            error_cnt = error_cnt + 1;
        end

        if(error_cnt >= MAX_ERROR) begin
            $display("%t: Caught %d errros", $time, error_cnt);
            #1;
            $finish;
        end
    end
    `endif
        
endmodule // testbench
