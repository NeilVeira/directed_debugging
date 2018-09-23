/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Non-restoring signed by unsigned divider                   ////
////  Uses the non-restoring unsigned by unsigned divider        ////
////                                                             ////
////  Author: Richard Herveille                                  ////
////          richard@asics.ws                                   ////
////          www.asics.ws                                       ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2002 Richard Herveille                        ////
////                    richard@asics.ws                         ////
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
//  $Id: div_su.v 17378 2008-12-12 20:50:59Z evean $
//
//  $Date: 2008-12-12 15:50:59 -0500 (Fri, 12 Dec 2008) $
//  $Revision: 17378 $
//  $Author: evean $
//  $Locker$
//  $State$
//
// Change History:
//               $Log$
//               Revision 1.1  2006/09/24 16:35:51  jackey
//               Initial revision
//
//               Revision 1.1.1.1  2006/07/31 06:15:24  jackey
//               rtl in new structure for divider
//
//               Revision 1.1.1.1  2006/07/18 03:17:51  jackey
//               Buggy Divider #9
//
//               Revision 1.1.1.1  2006/06/26 04:58:01  jackey
//               dividers design from OpenCores.org
//
//               Revision 1.1  2006/05/10 03:24:13  jackey
//               - initial commit
//
//               Revision 1.2  2002/10/31 13:54:58  rherveille
//               Fixed a bug in the remainder output of div_su.v
//
//               Revision 1.1.1.1  2002/10/29 20:29:09  rherveille
//
//
//

//synopsys translate_off
`include "timescale.v"
//synopsys translate_on

module divider(clk, ena, z, d, q, s, div0, ovf);

	//
	// parameters
	//
	parameter z_width = 16;
	parameter d_width = z_width /2;
	
	//
	// inputs & outputs
	//
	input clk;              // system clock
	input ena;              // clock enable

	input  [z_width-1:0] z; // divident
	input  [d_width-1:0] d; // divisor
	output [d_width  :0] q; // quotient
	output [d_width  :0] s; // remainder
	output div0;
	output ovf;

	reg [d_width:0] q, s;
	reg div0;
	reg ovf;

	//
	// variables
	//
	reg [z_width -1:0] iz;
	reg [d_width -1:0] id;
	reg [d_width +1:0] spipe;

	wire [d_width -1:0] iq, is;
	wire                idiv0, iovf;

	//
	// module body
	//

	// delay d
	always @(posedge clk)
	  if (ena)
	    id <= #1 d;

	// check z, take abs value
	always @(posedge clk)
	  if (ena)
	    if (z[z_width-1])
	       iz <= #1 ~z +1'h1;
	    else
	       iz <= #1 z;

	// generate spipe (sign bit pipe)
	integer n;
	always @(posedge clk)
	  if(ena)
	  begin
	      spipe[0] <= #1 z[z_width-1];

	      for(n=1; n <= d_width+1; n=n+1)
	         spipe[n] <= #1 spipe[n-1];
	  end

	// hookup non-restoring divider
	div_uu #(z_width, d_width)
	div_uu (
		.clk(clk),
		.ena(ena),
		.z(iz),
		.d(id),
		.q(iq),
		.s(is),
		.div0(idiv0),
		.ovf(iovf)
	);

	// correct divider results if 'd' was negative
	always @(posedge clk)
	  if(ena)
	    if(spipe[d_width+1])
	    begin
	        q <= #1 (~iq) + 1'h1;
	        s <= #1 (~is) + 1'h1;
	    end
	    else
	    begin
	    	// buggy9: original
	        // q <= #1 {1'b0, iq};
            // s <= #1 {1'b0, is};
	        q <= #1 {1'b0, is};
	        s <= #1 {1'b0, iq};
	    end

	// delay flags same as results
	always @(posedge clk)
	  if(ena)
	  begin
	      div0 <= #1 idiv0;
	      ovf  <= #1 iovf;
	  end
endmodule
