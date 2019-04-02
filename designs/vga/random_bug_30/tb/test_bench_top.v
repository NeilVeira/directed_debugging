/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Top Level Test Bench                                       ////
////                                                             ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////                                                             ////
////  Downloaded from: http://www.opencores.org/cores/vga_lcd/   ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2001 Rudolf Usselmann                         ////
////                    rudi@asics.ws                            ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

//  CVS Log
//
//  $Id: test_bench_top.v,v 1.10 2003/09/23 13:09:25 markom Exp $
//
//  $Date: 2003/09/23 13:09:25 $
//  $Revision: 1.10 $
//  $Author: markom $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: test_bench_top.v,v $
//               Revision 1.10  2003/09/23 13:09:25  markom
//               all WB outputs are registered, but just when we dont use cursors
//
//               Revision 1.9  2003/08/22 07:12:31  rherveille
//               Enabled Fifo Underrun test
//
//               Revision 1.8  2003/05/07 14:39:19  rherveille
//               Added DVI tests
//
//               Revision 1.7  2003/05/07 09:45:28  rherveille
//               Numerous updates and added checks
//
//               Revision 1.6  2003/03/19 17:22:19  rherveille
//               Added WISHBONE revB.3 sanity checks
//
//               Revision 1.5  2003/03/19 12:20:53  rherveille
//               Changed timing section in VGA core, changed testbench accordingly.
//               Fixed bug in 'timing check' test.
//
//               Revision 1.4  2002/02/07 05:38:32  rherveille
//               Added wb_ack delay section to testbench
//
//
//
//
//

`timescale 1ns/10ps

module test;

reg		signal_DebuggerClk;
reg		rst;

parameter	LINE_FIFO_AWIDTH = 7;

wire		int_verilog;
wire	[31:0]	wb_addr_o;
wire	[31:0]	wb_data_i;
wire	[31:0]	wb_data_o;
wire	[3:0]	wb_sel_o;
wire		wb_we_o;
wire		wb_stb_o;
wire		wb_cyc_o;
wire	[2:0]	wb_cti_o;
wire	[1:0]	wb_bte_o;
wire		wb_ack_i;
wire		wb_err_i;
wire	[31:0]	wb_addr_i;
wire	[31:0]	wbm_data_i;
wire	[3:0]	wb_sel_i;
wire		wb_we_i;
wire		wb_stb_i;
wire		wb_cyc_i;
wire		wb_ack_o;
wire		wb_rty_o;
wire		wb_err_o;
reg		pclk_i;
wire		pclk;
wire    	hsync;
wire		vsync;
wire    	ihsync;
wire		ivsync;
wire		csync;
wire		blanc;
wire	[7:0]	red;
wire	[7:0]	green;
wire	[7:0]	blue;
wire		dvi_de_o;
`ifdef VGA_12BIT_DVI
wire	[11:0]	dvi_d_o;
`else
wire	[23:0]	dvi_d_o;
`endif

wire vga_stb_i;
wire clut_stb_i;

reg		scen;

// Test Bench Variables
integer		wd_cnt;
integer		error_cnt;

// Misc Variables
reg	[31:0]	data;
reg	[31:0]	pattern;
reg		int_warn;

integer		n;
integer		mode;

reg	[7:0]	thsync, thgdel;
reg	[15:0]	thgate, thlen;
reg	[7:0]	tvsync, tvgdel;
reg	[15:0]	tvgate, tvlen;
reg		hpol;
reg		vpol;
reg		cpol;
reg		bpol;
integer		p, l;
reg	[31:0]	pn;
reg	[31:0]	pra, paa, tmp;
reg	[23:0]	pd;
reg	[1:0]	cd;
reg		pc;
reg	[31:0]	vbase;
reg	[31:0]	cbase;
reg	[31:0]	vbara;
reg	[31:0]	vbarb;
reg	[7:0]	bank;

//Vennsa: END_SIM event
event    END_SIM;
   
/////////////////////////////////////////////////////////////////////
//
// Defines
//

`define	CTRL		32'h0000_0000
`define	STAT		32'h0000_0004
`define	HTIM		32'h0000_0008
`define	VTIM		32'h0000_000c
`define	HVLEN		32'h0000_0010
`define	VBARA		32'h0000_0014
`define	VBARB		32'h0000_0018

`define USE_VC		1

parameter	PCLK_C = 30;

/////////////////////////////////////////////////////////////////////
//
// Simulation Initialization and Start up Section
//

initial
   begin
	$timeformat (-9, 1, " ns", 12);
	$display("\n\n");
	$display("******************************************************");
	$display("* WISHBONE VGA/LCD Controller Simulation started ... *");
	$display("******************************************************");
	$display("\n");
`ifdef WAVES
  	$shm_open("waves");
	$shm_probe("AS",test,"AS");
	$display("INFO: Signal dump enabled ...\n\n");
`endif
	scen = 0;
	error_cnt = 0;
   	signal_DebuggerClk = 0;
	pclk_i = 0;
   	rst = 0;
	int_warn=1;

   	repeat(20)	@(posedge signal_DebuggerClk);
   	rst = 1;
   	repeat(20)	@(posedge signal_DebuggerClk);

	// HERE IS WHERE THE TEST CASES GO ...

if(0)	// Full Regression Run
   begin

   end
else
if(1)	// Quick Regression Run
  begin
     
	reg_test;
	tim_test(1);

`ifdef VGA_24BIT_DVI
	dvi_pd_test;
`endif
`ifdef VGA_12BIT_DVI
`else
     pd1_test(1,2,1);
	 pd2_test(1,2,1);
`endif

	ur_test;
   end
else
   begin

	//
	// TEST DEVELOPMENT AREA
	//
      $display("\n\n");
      $display("*****************************************************");
      $display("*** XXX Test                                 ***");
      $display("*****************************************************\n");
      
	s0.fill_mem(1);

	repeat(10) @(posedge signal_DebuggerClk);

	vbara = 32'h0000_0000;
	vbarb = 32'h0001_0000;

	m0.wb_wr1( `VBARA, 4'hf, vbara );
	m0.wb_wr1( `VBARB, 4'hf, vbarb );

	thsync = 0;
	thgdel = 0;
	thgate = 340;
	thlen = 345;

	tvsync = 0;
	tvgdel = 0;
	tvgate = 240;
	tvlen = 245;

/*
	thsync = 0;
	thgdel = 0;
	thgate = 63;
	thlen = 70;

	tvsync = 0;
	tvgdel = 0;
	tvgate = 32;
	tvlen = 36;
*/

	hpol = 0;
	vpol = 0;
	cpol = 0;
	bpol = 0;

	m0.wb_wr1( `HTIM,  4'hf, {thsync, thgdel, thgate} );
	m0.wb_wr1( `VTIM,  4'hf, {tvsync, tvgdel, tvgate} );
	m0.wb_wr1( `HVLEN, 4'hf, {thlen, tvlen} );

      mode = 2;

//for(mode=0;mode<1;mode=mode+1)
      for(bank=0;bank<3;bank=bank + 1)
	begin
	   case(mode)
	     0:
	       begin
		  cd = 2'h2;
		  pc = 1'b0;
	       end
	     1:
	       begin
		  cd = 2'h0;
		  pc = 1'b0;
	       end
	     2:
	       begin
		  cd = 2'h0;
		  pc = 1'b1;
	       end
	     3:
	       begin
		  cd = 2'h1;
		  pc = 1'b0;
	       end
	   endcase

	   m0.wb_wr1( `CTRL,  4'hf, {
				     16'h0,	// Reserved
				     bpol, cpol,
				     vpol, hpol,
				     pc,	// 1'b0,	// PC
				     cd,	// 2'h2,	// CD
				     2'h0,	// VBL
				     1'b0,	// Reserved
				     1'b1,	// CBSWE
				     1'b1,	// VBSWE
				     1'b0,	// BSIE
				     1'b0,	// HIE
				     1'b0,	// VIE
				     1'b1	// Video Enable
				     });
	   
	   $display("Mode: %0d Screen: %0d", mode, bank);
	   //repeat(2) @(posedge vsync);
	   @(posedge vsync);
	   
	   // For Each Line
	   for(l=0;l<tvgate+1;l=l+1)
	     // For each Pixel
	     for(p=0;p<thgate+1;p=p+1)
	       begin
		while(blanc)	@(posedge pclk);  // wait for viewable data
		  
		  //$display("pixel=%0d, line=%0d, (%0t)",p,l,$time);

		  if(bank[0])	vbase = vbarb[31:2];
		  else		vbase = vbara[31:2];
		  if(bank[0])	cbase = 32'h0000_0c00;
		  else		cbase = 32'h0000_0800;
		  
		  // Depending on Mode, determine pixel data
		  // pixel number = line * (thgate + 1) + p
		  pn = l * (thgate + 1) + p;
		  
		  case(mode)
		    0:	// 24 bit/pixel mode
		      begin
			 pra = pn[31:2] * 3;	// Pixel relative Address
			 paa = pra + vbase;		// Pixel Absolute Address
			 
			 // Pixel Data
			 case(pn[1:0])
			   0:
			     begin
				tmp = s0.mem[paa];
				pd = tmp[31:8];
			     end
			   1:
			     begin
				tmp = s0.mem[paa];
				pd[23:16] = tmp[7:0];
				tmp = s0.mem[paa+1];
				pd[15:0] = tmp[31:16];
			     end
			   2:
			     begin
				tmp = s0.mem[paa+1];
				pd[23:8] = tmp[15:0];
				tmp = s0.mem[paa+2];
				pd[7:0] = tmp[31:24];
			     end
			   3:
			     begin
				tmp = s0.mem[paa+2];
				pd = tmp[23:0];
			     end
			 endcase
		      end
		    
		    1:	// 8 bit/pixel grayscale mode
		      begin
			 pra = pn[31:2];		// Pixel relative Address
			 paa = pra + vbase;	// Pixel Absolute Address
			 case(pn[1:0])
			   0:
			     begin
				tmp = s0.mem[paa];
				pd = { tmp[31:24], tmp[31:24], tmp[31:24] };
			     end
			   1:
			     begin
				tmp = s0.mem[paa];
				pd = { tmp[23:16], tmp[23:16], tmp[23:16] };
			     end
			   2:
			     begin
				tmp = s0.mem[paa];
				pd = { tmp[15:8], tmp[15:8], tmp[15:8] };
			     end
			   3:
			     begin
				tmp = s0.mem[paa];
				pd = { tmp[7:0], tmp[7:0], tmp[7:0] };
			     end
			 endcase
		   end
		    
		    2:	// 8 bit/pixel Pseudo Color mode
		      begin
			 pra = pn[31:2];		// Pixel relative Address
			 paa = pra + vbase;	// Pixel Absolute Address
			 case(pn[1:0])
			   0:
			     begin
				tmp = s0.mem[paa];
				tmp = s0.mem[cbase[31:2] + tmp[31:24]];
				pd = tmp[23:0];
			     end
			   1:
			     begin
				tmp = s0.mem[paa];
				tmp = s0.mem[cbase[31:2] + tmp[23:16]];
				pd = tmp[23:0];
			     end
			   2:
			     begin
				tmp = s0.mem[paa];
				tmp = s0.mem[cbase[31:2] + tmp[15:8]];
				pd = tmp[23:0];
			     end
			   3:
			     begin
				tmp = s0.mem[paa];
				tmp = s0.mem[cbase[31:2] + tmp[7:0]];
				pd = tmp[23:0];
			     end
			 endcase
		      end
		    
		    3:	// 16 bit/pixel mode
		      begin
			 pra = pn[31:1];		// Pixel relative Address
			 paa = pra + vbase;	// Pixel Absolute Address
			 case(pn[0])
			   0:
			     begin
				tmp = s0.mem[paa];
				tmp[15:0] = tmp[31:16];
				pd = {tmp[15:11], 3'h0, tmp[10:5], 2'h0, tmp[4:0], 3'h0};
			     end
			   1:
			     begin
				tmp = s0.mem[paa];
				pd = {tmp[15:11], 3'h0, tmp[10:5], 2'h0, tmp[4:0], 3'h0};
			     end
			 endcase
		      end
		    
		  endcase
              
		  if(pd !== {red, green, blue} )
		    begin
		       $display("ERROR: Pixel Data Mismatch: Expected: %h, Got: %h %h %h",
				pd, red, green, blue);
		       $display("       pixel=%0d, line=%0d, (%0t)",p,l,$time);
		       error_cnt = error_cnt + 1;
		    end
		  
		  @(posedge pclk);
		  
	       end
	end
      
      show_errors;
      $display("*****************************************************");
      $display("*** Test DONE ...                                 ***");
      $display("*****************************************************\n\n");
      
      
   end
      
      repeat(10)	@(posedge signal_DebuggerClk);
      -> END_SIM;
      
      //$finish;
   end
   
   /////////////////////////////////////////////////////////////////////
   //
   // Sync Monitor
   //
   
//`ifdef VGA_12BIT_DVI
//   sync_check #(PCLK_C) ucheck(
//`else
   sync_check #(PCLK_C) ucheck(
//`endif
		.pclk(		pclk		),
		.rst(		rst		),
		.enable(	scen		),
		.hsync(		hsync		),
		.vsync(		vsync		),
		.csync(		csync		),
		.blanc(		blanc		),
		.hpol(		hpol		),
		.vpol(		vpol		),
		.cpol(		cpol		),
		.bpol(		bpol		),
		.thsync(	thsync		),
		.thgdel(	thgdel		),
		.thgate(	thgate		),
		.thlen(		thlen		),
		.tvsync(	tvsync		),
		.tvgdel(	tvgdel		),
		.tvgate(	tvgate		),
		.tvlen(		tvlen		) );

/////////////////////////////////////////////////////////////////////
//
// Video Data Monitor
//

/////////////////////////////////////////////////////////////////////
//
// WISHBONE revB.3 checker
//

wb_b3_check u_wb_check (
	.clk_i ( signal_DebuggerClk      ),
	.cyc_i ( wb_cyc_o ),
	.stb_i ( wb_stb_o ),
	.cti_i ( wb_cti_o ),
	.bte_i ( wb_bte_o ),
	.we_i  ( wb_we_o  ),
	.ack_i ( wb_ack_i ),
	.err_i ( wb_err_i ),
	.rty_i ( 1'b0     ) );
   

/////////////////////////////////////////////////////////////////////
//
// Watchdog Counter
//

always @(posedge signal_DebuggerClk)
	if(wb_cyc_i | wb_cyc_o | wb_ack_i | wb_ack_o | hsync)
	  wd_cnt <= #1 0;
	else
	  wd_cnt <= #1 wd_cnt + 1;


always @(wd_cnt)
	if(wd_cnt>9000)
	   begin
		$display("\n\n*************************************\n");
		$display("ERROR: Watch Dog Counter Expired\n");
		$display("*************************************\n\n\n");
		$finish;
	   end


always @(posedge int_verilog)
  if(int_warn)
   begin
	$display("\n\n*************************************\n");
	$display("WARNING: Recieved Interrupt (%0t)", $time);
	$display("*************************************\n\n\n");
   end

always #3 signal_DebuggerClk = ~signal_DebuggerClk;
always #(PCLK_C/2) pclk_i = ~pclk_i;

/////////////////////////////////////////////////////////////////////
//
// WISHBONE VGA/LCD IP Core
//


// Module Prototype
//default: else case
//`ifdef VGA_12BIT_DVI
//vga_dvi_top #(1'b0, LINE_FIFO_AWIDTH) dut (
//`else
vga #(1'b0, LINE_FIFO_AWIDTH) dut (
//`endif
		.wb_clk_i     ( signal_DebuggerClk             ),
		.wb_rst_i     ( 1'b0            ),
		.rst_i        ( rst             ),
		.wb_inta_o    ( int_verilog             ),

		//-- slave signals
		.wbs_adr_i    ( wb_addr_i[11:0] ),
		.wbs_dat_i    ( wb_data_i       ),
		.wbs_dat_o    ( wb_data_o       ),
		.wbs_sel_i    ( wb_sel_i        ),
		.wbs_we_i     ( wb_we_i         ),
		.wbs_stb_i    ( wb_stb_i        ),
		.wbs_cyc_i    ( wb_cyc_i        ),
		.wbs_ack_o    ( wb_ack_o        ),
		.wbs_rty_o    ( wb_rty_o        ),
		.wbs_err_o    ( wb_err_o        ),

		//-- master signals
		.wbm_adr_o    ( wb_addr_o[31:0] ),
		.wbm_dat_i    ( wbm_data_i      ),
		.wbm_sel_o    ( wb_sel_o        ),
		.wbm_we_o     ( wb_we_o         ),
		.wbm_stb_o    ( wb_stb_o        ),
		.wbm_cyc_o    ( wb_cyc_o        ),
		.wbm_cti_o    ( wb_cti_o        ),
		.wbm_bte_o    ( wb_bte_o        ),
		.wbm_ack_i    ( wb_ack_i        ),
		.wbm_err_i    ( wb_err_i        ),

		//-- VGA signals
		.clk_p_i      ( pclk_i          )
        
        `ifdef VGA_24BIT_DVI
	    ,.dvi_hsync_o  ( ihsync          ),
		.dvi_vsync_o  ( ivsync          ),
	    .dvi_de_o     ( dvi_de_o        ),
		.dvi_d_o      ( dvi_d_o         )
        `endif
        `ifdef VGA_12BIT_DVI
        `else
        ,.hsync_pad_o  ( hsync           ),
		.vsync_pad_o  ( vsync           ),
		.csync_pad_o  ( csync           ),
		.blank_pad_o  ( blanc           ),
		.r_pad_o      ( red             ),
		.g_pad_o      ( green           ),
		.b_pad_o      ( blue            )
        `endif

        `ifdef VGA_BIST
                /* BIST signals */
              , .scanb_rst(1'b1),
                .scanb_clk(1'b0),
                .scanb_si (1'b0),
                .scanb_en (1'b0),
                .scanb_so ()
        `endif
	);

assign pclk = pclk_i;

`ifdef VGA_12BIT_DVI
    assign hsync = !ihsync;
    assign vsync = !ivsync;
`endif

wb_mast	m0(	.clk(		signal_DebuggerClk		),
		.rst(		rst		),
		.adr(		wb_addr_i	),
		.din(		wb_data_o	),
		.dout(		wb_data_i	),
		.cyc(		wb_cyc_i	),
		.stb(		wb_stb_i	),
		.sel(		wb_sel_i	),
		.we(		wb_we_i		),
		.ack(		wb_ack_o	),
		.err(		wb_err_o	),
		.rty(		1'b0		)
		);

wb_slv #(24) s0(.clk(		signal_DebuggerClk		),
		.rst(		rst		),
		.adr(		{1'b0, wb_addr_o[30:0]}	),
		.din(		32'h0		),
		.dout(		wbm_data_i	),
		.cyc(		wb_cyc_o	),
		.stb(		wb_stb_o	),
		.sel(		wb_sel_o	),
		.we(		wb_we_o		),
		.ack(		wb_ack_i	),
		.err(		wb_err_i	),
		.rty(				)
		);
   

// VENNSA INSERTION BEGIN
reg signal_DebuggerBegin=0;
reg signal_DebuggerEnd=0;

parameter MAX_ERROR = 1;                                           
parameter VERBOSE = 0;
                                           
event START_CAPTURE;
event ERROR;

initial begin
   signal_DebuggerBegin = 0;
   signal_DebuggerEnd = 0;
end

   //start handler
   always@(posedge rst) begin
      repeat(20) @(posedge signal_DebuggerClk);
      -> START_CAPTURE;
   end
   
   always@(START_CAPTURE) begin
      @(posedge signal_DebuggerClk)
        #4 signal_DebuggerBegin = 1;
      
      $display("At time:%t, start capturing ... clock = %b",
		       $time,signal_DebuggerClk);
   end

   //error handler                                           
   always@(ERROR) begin
      if(signal_DebuggerBegin && !signal_DebuggerEnd) begin
         error_cnt = error_cnt + 1;
         
         if(error_cnt >= MAX_ERROR)
           -> END_SIM;
         
      end
   end // always@ (ERROR)

   always@(END_SIM)begin
      $display("Total Error: %d", error_cnt);
      
      @(posedge signal_DebuggerClk)
        signal_DebuggerEnd = 1;

      #1 $finish;
   end
     
                                           
`include "self_checking.v"

// VENNSA INSERTION END
                                           
`include "tests.v" 

reg debug_clk;
initial debug_clk = 1;
always #50 debug_clk = ~debug_clk;
`ifdef VGA_12BIT_DVI
reg  prev_dvi_pclk_p_o;
`endif
`ifdef VGA_12BIT_DVI
reg  prev_dvi_pclk_m_o;
`endif
`ifdef VGA_12BIT_DVI
reg  prev_dvi_hsync_o;
`endif
`ifdef VGA_12BIT_DVI
reg  prev_dvi_vsync_o;
`endif
`ifdef VGA_12BIT_DVI
reg  prev_dvi_de_o;
`endif
`ifdef VGA_12BIT_DVI
reg [11:0] prev_dvi_d_o;
`endif
reg  prev_wb_inta_o;
reg [31:0] prev_wbs_dat_o;
reg  prev_wbs_ack_o;
reg  prev_wbs_rty_o;
reg  prev_wbs_err_o;
reg [31:0] prev_wbm_adr_o;
reg [3:0] prev_wbm_sel_o;
reg  prev_wbm_we_o;
reg  prev_wbm_stb_o;
reg  prev_wbm_cyc_o;
reg [2:0] prev_wbm_cti_o;
reg [1:0] prev_wbm_bte_o;
reg  prev_clk_p_o;
reg  prev_hsync_pad_o;
reg  prev_vsync_pad_o;
reg  prev_csync_pad_o;
reg  prev_blank_pad_o;
reg [7:0] prev_r_pad_o;
reg [7:0] prev_g_pad_o;
reg [7:0] prev_b_pad_o;
always @(posedge debug_clk) begin
    if (
`ifdef VGA_12BIT_DVI
        dut.dvi_pclk_p_o != prev_dvi_pclk_p_o ||
`endif
`ifdef VGA_12BIT_DVI
        dut.dvi_pclk_m_o != prev_dvi_pclk_m_o ||
`endif
`ifdef VGA_12BIT_DVI
        dut.dvi_hsync_o != prev_dvi_hsync_o ||
`endif
`ifdef VGA_12BIT_DVI
        dut.dvi_vsync_o != prev_dvi_vsync_o ||
`endif
`ifdef VGA_12BIT_DVI
        dut.dvi_de_o != prev_dvi_de_o ||
`endif
`ifdef VGA_12BIT_DVI
        dut.dvi_d_o != prev_dvi_d_o ||
`endif
        dut.wb_inta_o != prev_wb_inta_o ||
        dut.wbs_dat_o != prev_wbs_dat_o ||
        dut.wbs_ack_o != prev_wbs_ack_o ||
        dut.wbs_rty_o != prev_wbs_rty_o ||
        dut.wbs_err_o != prev_wbs_err_o ||
        dut.wbm_adr_o != prev_wbm_adr_o ||
        dut.wbm_sel_o != prev_wbm_sel_o ||
        dut.wbm_we_o != prev_wbm_we_o ||
        dut.wbm_stb_o != prev_wbm_stb_o ||
        dut.wbm_cyc_o != prev_wbm_cyc_o ||
        dut.wbm_cti_o != prev_wbm_cti_o ||
        dut.wbm_bte_o != prev_wbm_bte_o ||
        dut.clk_p_o != prev_clk_p_o ||
        dut.hsync_pad_o != prev_hsync_pad_o ||
        dut.vsync_pad_o != prev_vsync_pad_o ||
        dut.csync_pad_o != prev_csync_pad_o ||
        dut.blank_pad_o != prev_blank_pad_o ||
        dut.r_pad_o != prev_r_pad_o ||
        dut.g_pad_o != prev_g_pad_o ||
        dut.b_pad_o != prev_b_pad_o )
        $display("Signals at %t",$time);
`ifdef VGA_12BIT_DVI
    if (dut.dvi_pclk_p_o != prev_dvi_pclk_p_o)
        $display("dvi_pclk_p_o = %h",dut.dvi_pclk_p_o);
    prev_dvi_pclk_p_o <= dut.dvi_pclk_p_o;
`endif
`ifdef VGA_12BIT_DVI
    if (dut.dvi_pclk_m_o != prev_dvi_pclk_m_o)
        $display("dvi_pclk_m_o = %h",dut.dvi_pclk_m_o);
    prev_dvi_pclk_m_o <= dut.dvi_pclk_m_o;
`endif
`ifdef VGA_12BIT_DVI
    if (dut.dvi_hsync_o != prev_dvi_hsync_o)
        $display("dvi_hsync_o = %h",dut.dvi_hsync_o);
    prev_dvi_hsync_o <= dut.dvi_hsync_o;
`endif
`ifdef VGA_12BIT_DVI
    if (dut.dvi_vsync_o != prev_dvi_vsync_o)
        $display("dvi_vsync_o = %h",dut.dvi_vsync_o);
    prev_dvi_vsync_o <= dut.dvi_vsync_o;
`endif
`ifdef VGA_12BIT_DVI
    if (dut.dvi_de_o != prev_dvi_de_o)
        $display("dvi_de_o = %h",dut.dvi_de_o);
    prev_dvi_de_o <= dut.dvi_de_o;
`endif
`ifdef VGA_12BIT_DVI
    if (dut.dvi_d_o != prev_dvi_d_o)
        $display("dvi_d_o[11:0] = %h",dut.dvi_d_o);
    prev_dvi_d_o <= dut.dvi_d_o;
`endif
    if (dut.wb_inta_o != prev_wb_inta_o)
        $display("wb_inta_o = %h",dut.wb_inta_o);
    prev_wb_inta_o <= dut.wb_inta_o;
    if (dut.wbs_dat_o != prev_wbs_dat_o)
        $display("wbs_dat_o[31:0] = %h",dut.wbs_dat_o);
    prev_wbs_dat_o <= dut.wbs_dat_o;
    if (dut.wbs_ack_o != prev_wbs_ack_o)
        $display("wbs_ack_o = %h",dut.wbs_ack_o);
    prev_wbs_ack_o <= dut.wbs_ack_o;
    if (dut.wbs_rty_o != prev_wbs_rty_o)
        $display("wbs_rty_o = %h",dut.wbs_rty_o);
    prev_wbs_rty_o <= dut.wbs_rty_o;
    if (dut.wbs_err_o != prev_wbs_err_o)
        $display("wbs_err_o = %h",dut.wbs_err_o);
    prev_wbs_err_o <= dut.wbs_err_o;
    if (dut.wbm_adr_o != prev_wbm_adr_o)
        $display("wbm_adr_o[31:0] = %h",dut.wbm_adr_o);
    prev_wbm_adr_o <= dut.wbm_adr_o;
    if (dut.wbm_sel_o != prev_wbm_sel_o)
        $display("wbm_sel_o[3:0] = %h",dut.wbm_sel_o);
    prev_wbm_sel_o <= dut.wbm_sel_o;
    if (dut.wbm_we_o != prev_wbm_we_o)
        $display("wbm_we_o = %h",dut.wbm_we_o);
    prev_wbm_we_o <= dut.wbm_we_o;
    if (dut.wbm_stb_o != prev_wbm_stb_o)
        $display("wbm_stb_o = %h",dut.wbm_stb_o);
    prev_wbm_stb_o <= dut.wbm_stb_o;
    if (dut.wbm_cyc_o != prev_wbm_cyc_o)
        $display("wbm_cyc_o = %h",dut.wbm_cyc_o);
    prev_wbm_cyc_o <= dut.wbm_cyc_o;
    if (dut.wbm_cti_o != prev_wbm_cti_o)
        $display("wbm_cti_o[2:0] = %h",dut.wbm_cti_o);
    prev_wbm_cti_o <= dut.wbm_cti_o;
    if (dut.wbm_bte_o != prev_wbm_bte_o)
        $display("wbm_bte_o[1:0] = %h",dut.wbm_bte_o);
    prev_wbm_bte_o <= dut.wbm_bte_o;
    if (dut.clk_p_o != prev_clk_p_o)
        $display("clk_p_o = %h",dut.clk_p_o);
    prev_clk_p_o <= dut.clk_p_o;
    if (dut.hsync_pad_o != prev_hsync_pad_o)
        $display("hsync_pad_o = %h",dut.hsync_pad_o);
    prev_hsync_pad_o <= dut.hsync_pad_o;
    if (dut.vsync_pad_o != prev_vsync_pad_o)
        $display("vsync_pad_o = %h",dut.vsync_pad_o);
    prev_vsync_pad_o <= dut.vsync_pad_o;
    if (dut.csync_pad_o != prev_csync_pad_o)
        $display("csync_pad_o = %h",dut.csync_pad_o);
    prev_csync_pad_o <= dut.csync_pad_o;
    if (dut.blank_pad_o != prev_blank_pad_o)
        $display("blank_pad_o = %h",dut.blank_pad_o);
    prev_blank_pad_o <= dut.blank_pad_o;
    if (dut.r_pad_o != prev_r_pad_o)
        $display("r_pad_o[7:0] = %h",dut.r_pad_o);
    prev_r_pad_o <= dut.r_pad_o;
    if (dut.g_pad_o != prev_g_pad_o)
        $display("g_pad_o[7:0] = %h",dut.g_pad_o);
    prev_g_pad_o <= dut.g_pad_o;
    if (dut.b_pad_o != prev_b_pad_o)
        $display("b_pad_o[7:0] = %h",dut.b_pad_o);
    prev_b_pad_o <= dut.b_pad_o;
end
				  
endmodule
