/////////////////////////////////////////////////////////////////////
////                                                             ////
////  SPI Slave Model                                            ////
////                                                             ////
////  Authors: Richard Herveille (richard@asics.ws) www.asics.ws ////
////                                                             ////
////  http://www.opencores.org/projects/simple_spi/              ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2004 Richard Herveille                        ////
////                         richard@asics.ws                    ////
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
//  $Id: spi_slave_model.v 22294 2009-07-10 19:54:10Z evean $
//
//  $Date: 2009-07-10 15:54:10 -0400 (Fri, 10 Jul 2009) $
//  $Revision: 22294 $
//  $Author: evean $
//  $Locker$
//  $State$
//
// Change History:
//               $Log$
//               Revision 1.1  2006/09/24 16:35:54  jackey
//               Initial revision
//
//               Revision 1.1.1.1  2006/07/03 05:23:44  jackey
//               SPI design from OpenCores
//
//               Revision 1.1  2004/02/28 16:01:47  rherveille
//               Initial testbench release added
//
//
//
//


// Requires: Verilog2001
//`begin_keywords "1364-2001"
  
`include "timescale.v"

module spi_slave_model (
   csn, sck, di, verilog_do
);
	input  csn;
	input  sck;
	input  di;
	output verilog_do;
	
	//
	// Variable declaration
	//
	wire debug = 1'b1;

	wire cpol = 1'b0;
	wire cpha  = 1'b0;

	reg [7:0] mem [7:0]; // initiate memory
	reg [2:0] mem_adr;   // memory address
	reg [7:0] mem_do;    // memory data output

	reg [7:0] sri, sro;  // 8bit shift register

	reg [2:0] bit_cnt;
	reg       ld;

	wire clk;

	//
	// module body
	//

	assign clk = cpol ^ cpha ^ sck;

	// generate shift registers
	always @(posedge clk)
	  sri <= #1 {sri[6:0],di};

	always @(posedge clk)
	  if (&bit_cnt)
	    sro <= #1 mem[mem_adr];
	  else
	    sro <= #1 {sro[6:0],1'bx};

	assign verilog_do = sro[7];

	//generate bit-counter
	always @(posedge clk, posedge csn)
	  if(csn)
	    bit_cnt <= #1 3'b111;
	  else
	    bit_cnt <= #1 bit_cnt - 3'h1;

	//generate access done signal
        always @(posedge clk)
	  ld <= #1 ~(|bit_cnt);

	always @(negedge clk)
          if (ld) begin
	    mem[mem_adr] <= #1 sri;
	    mem_adr      <= #1 mem_adr + 1'b1;
	  end

	initial
	begin
	  bit_cnt=3'b111;
	  mem_adr = 0;
	  sro = mem[mem_adr];
	end
endmodule

//`end_keywords
