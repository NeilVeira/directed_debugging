/////////////////////////////////////////////////////////////////////
////                                                             ////
////  Divider                   Testbench                        ////
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

`include "timescale.v"

module bench_div_top();

   parameter z_width = 16;
   parameter d_width = z_width /2;
   
   parameter pipeline = d_width +4;
   
   parameter show_div0 = 0;
   parameter show_ovf  = 0;
   
   //
   // internal wires
   //
   integer   z, d, n;
   integer   dz [pipeline:1];
   integer   dd [pipeline:1];
   reg [d_width:1] di;
   reg [z_width:1] zi;
   reg 		   signal_DebuggerClk;
   
   integer 	   sr, qr;
   integer 	   z_rand, d_rand;
   parameter 	   SEED1 = 100;
   parameter 	   SEED2 = 200;
   integer         seed1_int=SEED1+$stime;
   integer         seed2_int=SEED2+$stime;
      
   wire [d_width   :0] s;
   wire [d_width   :0] q;
   wire 	       div0, ovf;
   reg [d_width :0]    sc, qc;

   
   //VENNSA INSERTION BEGIN
   reg  signal_DebuggerBegin, signal_DebuggerEnd;
   integer err_cnt;
   parameter MAX_ERROR = 1;
   
   event   ERROR;
   event   START_CAPTURE;
   event   END_SIM;
   event   END_SIM_NOW;
   

   //initialize the control signals
   initial begin
      signal_DebuggerBegin = 0;
      signal_DebuggerEnd = 0;

      err_cnt = 0;
   end

   //start capturing
   initial begin
      #1 ->START_CAPTURE;
   end

   //setup the event items
   always@(START_CAPTURE) begin
      $display("At %t: start capturing, clock = %b", $time, signal_DebuggerClk);

      signal_DebuggerBegin = 1;
   end
      
   always@(ERROR) begin
      err_cnt = err_cnt + 1;
      if(err_cnt >= MAX_ERROR) begin
	 $display("Total Error Captured: %d", err_cnt);

	 -> END_SIM;
      end
   end

   always@(END_SIM) begin
      @(posedge signal_DebuggerClk) begin
	 $display("At %t: stop capturing...", $time);
	 #2 signal_DebuggerEnd = 1;

	 #1 $finish;
      end
   end

   always@(END_SIM_NOW) begin
       $display("At %t: stop capturing...", $time);
       #1 signal_DebuggerEnd = 1;

       #1 $finish;
   end

//include the vector capture file
   
   //VENNSA INSERTION END
   
   function integer twos;
      input [d_width:1] d;
      begin
	 if(d[d_width])
	   twos = -(~d[d_width:1] +1);
	 else
	   twos = d[d_width:1];
      end
   endfunction
   
   //
   // hookup division unit
   //
   divider #(z_width) dut (
			  .clk(signal_DebuggerClk),
			  .ena(1'b1),
			  .z(zi),
			  .d(di),
			  .q(q),
			  .s(s),
			  .div0(div0),
			  .ovf(ovf)
			  );
   
   always #3 signal_DebuggerClk <= ~signal_DebuggerClk;

   always @(posedge signal_DebuggerClk)
     for(n=2; n<=pipeline; n=n+1)
       begin
	      dz[n] <= #1 dz[n-1];
	      dd[n] <= #1 dd[n-1];
       end
   
   initial
     begin
	$display("*");
	$display("* Starting testbench");
	$display("*");
	
`ifdef WAVES
	$shm_open("waves");
	$shm_probe("AS",bench_div_top,"AS");
	$display("INFO: Signal dump enabled ...\n\n");
`endif
	
	signal_DebuggerClk = 0; // start with low-level clock
	
	// wait a while
	@(posedge signal_DebuggerClk);
	
	// present data
	for(z=50; z < 5000; z=z+123) 
	  begin
	     z_rand = {$random(seed1_int)} % z;
	     
	     for(d=10; d< 15; d=d+1) 
	       begin
		  d_rand = {$random(seed2_int)} % d;

          `ifdef USE_RANDOM_INPUT
		      zi <= #1 z_rand;
		      di <= #1 d_rand;
		      
		      dz[1] <= #1 z_rand;
		      dd[1] <= #1 d_rand;
          `else
		      zi <= #1 z;
		      di <= #1 d;
		      
		      dz[1] <= #1 z;
		      dd[1] <= #1 d;
          `endif
              
		  #4;
		  
		  qc = dz[pipeline] / dd[pipeline];
		  sc = dz[pipeline] - (dd[pipeline] * (dz[pipeline]/dd[pipeline]));

		  
		  $display("%t Result: div=%d; ovf=%d, (z/d=%0d/%0d). Received (q,s) = (%0d,%0d)",
			       $time, div0, ovf, dz[pipeline], dd[pipeline], twos(q), s);
		  
		  if(!ovf && !div0)
		    begin
		       if ( (qc !== q) || (sc !== s) )
			 begin
			    $display("Result error (z/d=%0d/%0d). Received (q,s) = (%0d,%0d), expected (%0d,%0d)",
				     dz[pipeline], dd[pipeline], twos(q), s, twos(qc), sc);
			    ->ERROR;
			 end
		    end // if (!ovf && !div0)
		  else
            begin
               qc = 9'hx;
               sc = 9'hx;
            end
		  
		  if(show_div0)
		    if(div0)
		      $display("Division by zero (z/d=%0d/%0d)", dz[pipeline], dd[pipeline]);
		  
		  if(show_ovf)
		    if(ovf)
		      $display("Overflow (z/d=%0d/%0d)", dz[pipeline], dd[pipeline]);
		  
		  @(posedge signal_DebuggerClk);
 	       end
	  end

	// wait a while
	//vennsa: comment this out, because the rest of results are not going to be checked at all
	//repeat(20) @(posedge signal_DebuggerClk);

	$display("*");
	$display("* Testbench ended. Total errors = %d", err_cnt);
	$display("*");

	//Vennsa: end the simulation
	-> END_SIM_NOW;
	     
     end
   
endmodule
