///*************************************************************///
///                                                             ///
///          Reed-Solomon Decoder (31,19,6)                     ///
///                                                             ///
///                                                             ///
///          Author : Rudy Dwi Putra                            ///
///                   rudy.dp@gmail.com                         ///
///                                                             ///
///*************************************************************///
///                                                             ///
/// Copyright (C) 2006  Rudy Dwi Putra                          ///
///                     rudy.dp@gmail.com                       ///
///                                                             ///
/// This source file may be used and distributed without        ///
/// restriction provided that this copyright statement is not   ///
/// removed from the file and that any derivative work contains ///
/// the original copyright notice and the associated disclaimer.///
///                                                             ///
///     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ///
/// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ///
/// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ///
/// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ///
/// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ///
/// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ///
/// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ///
/// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ///
/// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ///
/// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ///
/// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ///
/// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ///
/// POSSIBILITY OF SUCH DAMAGE.                                 ///
///                                                             ///
///*************************************************************///

//***************************************//
// Testbench for RS Decoder (31, 19, 6)  //
//***************************************//

module testbench_rsdecoder;
   
   reg [4:0] recword;
   reg 	     clock1, clock2;
   reg 	     start, reset;
   
   //******************************************************//
   // ready = if set to 1, decoder is ready to input or it //
   // is inputting new data    				   //
   // dataoutstart = flag the first symbol of outputted    //
   // received word.					   //
   // dataoutend = flag the last symbol of outputted	   //
   // received word.		   			   //
   // errfound = set to 1, if one of syndrome values 	   //
   // is not zero.					   //
   // decode_fail = set to 1, if decoder fails to correct  //
   // the received word.				   //
   //******************************************************//
   wire      ready, decode_fail, errfound, dataoutstart, dataoutend;
   wire [4:0] corr_recword;
   
   reg [4:0]  golden_cword [0:31];
   reg [4:0]  golden_cword_cmp;
   integer    j, err_cnt;

   parameter [5:0] clk_period = 40; 	

   //VENNSA INSERTION BEGIN
   reg             signal_DebuggerBegin;
   reg             signal_DebuggerEnd;

   wire [4:0]      signal_DebuggerGolden;
   
   integer         signal_DebuggerCmp;
   
   parameter       MAX_ERROR=1;

   parameter       START_CLOCK = 1; //For some of the cases which cannot find the bug, reduce this number
   // if the timeframe is too long, use larger number (eg. 34)
   
   event           ERROR;
   event           END_SIM;

   // Initialization
   initial begin
	  signal_DebuggerBegin = 0;
	  signal_DebuggerEnd = 0;
	  signal_DebuggerCmp = 0;   
   end
   
   //using the bench clock count to control the time frame number
   integer clkBenchCnt = 0;
   always @ (posedge clock2)
     begin
	    clkBenchCnt = clkBenchCnt + 1;
        
	    if ( clkBenchCnt == START_CLOCK) begin
	       #1	  signal_DebuggerBegin = 1;
	       $display("At time %t, start capturing ... clock = %b",
		            $time, clock2);
	    end
        
     end
   
   // Error Handler
   always @(ERROR) begin
      $display ("At time %t: Data compare error: Data[%d]: Expected %d, Received %d", $time, j, golden_cword_cmp, corr_recword);
      err_cnt = err_cnt + 1;
      if (err_cnt >= MAX_ERROR)
        ->END_SIM;
   end
   
   always@(END_SIM) begin
      $display("Total Error: %d", err_cnt);
      
      @(posedge clock1)
        signal_DebuggerEnd = 1;
      
      #1 $finish;
   end

   assign signal_DebuggerGolden = (signal_DebuggerCmp)? golden_cword_cmp : 5'hx;

   //VENNSA INSERTION END

   initial
     begin
	    recword = 5'b0;
	    start = 0;
	    reset = 0;
     end

   
   //**********//
   //  clock1  //
   //**********//
   initial
     begin
	    clock1 = 0;
	    forever #(clk_period/2) clock1 = ~clock1;
     end
   
   //**********//
   //  clock2  //
   //**********//
   initial
     begin
	    clock2 = 1;
	    forever #(clk_period/2) clock2 = ~clock2;
     end
   
   //***********************************************//
   // This section defines feeding of received word //
   // and start signal. Start signal is active 1    //
   // clock cycle before first symbol of received   //
   // word. All input and output synchronize with   //
   // clock2. First received word contains no error //
   // symbol. Thus, all syndrome values will be zero//
   // and decoder will pass the received word.      //
   // Second received word contains 6 error symbol. //
   // Decoder will determine its error locator      //
   // and error evaluator polynomial in KES block.  //
   // Then, it calculates error values in CSEE      //
   // block. Third received word contains 8 error   //
   // symbol. Decoder can't correct the error and   //
   // at the end of outputted received word, it will//
   // set decode_fail to 1.                         //
   //***********************************************//  
   initial
     begin
	    // Setup the inputs at non-edge of the clock
	    #35	  
	      #(clk_period) reset = 1;
	    //start has to be active 1 clock cycle before first recword, 
	    //otherwise decoder will output wrong recword.
	    #(clk_period) start = 1;
	    #(clk_period) start = 0;
	    //signal_DebuggerBegin = 1;
	    //First received word contains no error symbol.
	    //The decoder should give errfound = 0 at the end
	    //of syndrome calculation stage.
	    golden_cword_cmp = 5'h0;

        
         //Vennsa Comment
         //Comment in this set of input for testing buggy8 and buggy9
`ifdef TEST_5ERROR
 	     recword = 5'b01100; //it should be 5'b10100
	     #(clk_period) recword = 5'b00100;  
	     #(clk_period) recword = 5'b00101;
	     #(clk_period) recword = 5'b10001;
	     #(clk_period) recword = 5'b10110;
	     #(clk_period) recword = 5'b00001;
	     #(clk_period) recword = 5'b00110; //it should be 5'b00010
	     #(clk_period) recword = 5'b11100;
	     #(clk_period) recword = 5'b00011;
	     #(clk_period) recword = 5'b10001;
	     #(clk_period) recword = 5'b00110;
	     #(clk_period) recword = 5'b00101; //it should be 5'b00111
	     #(clk_period) recword = 5'b01010;
	     #(clk_period) recword = 5'b11111;
	     #(clk_period) recword = 5'b11111; //it should be 5'b01011
	     #(clk_period) recword = 5'b10100;
	     #(clk_period) recword = 5'b00100;
	     #(clk_period) recword = 5'b00101;
	     #(clk_period) recword = 5'b00001;
	     #(clk_period) recword = 5'b10111;
	     #(clk_period) recword = 5'b01101; //it should be 5'b10100
	     #(clk_period) recword = 5'b00010;
	     #(clk_period) recword = 5'b10110;
	     #(clk_period) recword = 5'b00100;
	     #(clk_period) recword = 5'b01011;
	     #(clk_period) recword = 5'b00110;
	     #(clk_period) recword = 5'b11110;
	     #(clk_period) recword = 5'b10100;
	     #(clk_period) recword = 5'b10101; //it should be 5'b11111
	     #(clk_period) recword = 5'b01010;
	     #(clk_period) recword = 5'b11110;
	     #(clk_period) recword = 5'b0;
`else
        //Vennsa Comment
        //Comment in this set of input for testing buggy1 to buggy7
	    recword = golden_cword[0];
	    #(clk_period) recword = golden_cword[1] ;
	    #(clk_period) recword = golden_cword[2] ;
	    #(clk_period) recword = golden_cword[3] ;
	    #(clk_period) recword = golden_cword[4] ;
	    #(clk_period) recword = golden_cword[5] ;
	    #(clk_period) recword = golden_cword[6] ;
	    #(clk_period) recword = golden_cword[7] ;
	    #(clk_period) recword = golden_cword[8] ;
	    #(clk_period) recword = golden_cword[9] ;
	    #(clk_period) recword = golden_cword[10];
	    #(clk_period) recword = golden_cword[11];
	    #(clk_period) recword = golden_cword[12];
	    #(clk_period) recword = golden_cword[13];
	    #(clk_period) recword = golden_cword[14];
	    #(clk_period) recword = golden_cword[15];
	    #(clk_period) recword = golden_cword[16];
	    #(clk_period) recword = golden_cword[17];
	    #(clk_period) recword = golden_cword[18];
	    #(clk_period) recword = golden_cword[19];
	    #(clk_period) recword = golden_cword[20];
	    #(clk_period) recword = golden_cword[21];
	    #(clk_period) recword = golden_cword[22];
	    #(clk_period) recword = golden_cword[23];
	    #(clk_period) recword = golden_cword[24];
	    #(clk_period) recword = golden_cword[25];
	    #(clk_period) recword = golden_cword[26];
	    #(clk_period) recword = golden_cword[27];
	    #(clk_period) recword = golden_cword[28];
	    #(clk_period) recword = golden_cword[29];
	    #(clk_period) recword = golden_cword[30];
	    #(clk_period) recword = golden_cword[31];
`endif	    
	    repeat(1) @(posedge clock1);
	    err_cnt = 0;
	    wait (dataoutstart && !dataoutend)	
	      if (dataoutstart && !dataoutend) begin
	         $display ("Checking starts.\n");
	         
             for(j=0;j<32;j=j+1) begin
		        
		        #5;
		        signal_DebuggerCmp=1;
		        golden_cword_cmp = golden_cword[j];
		        @(posedge clock2);

		        $display("Start checking data %d with %d", corr_recword, golden_cword[j] );
    		    if (corr_recword != golden_cword_cmp)
                  -> ERROR;
	         end // for (j=0;j<32;j=j+1)
	         
	         signal_DebuggerCmp = 0;
	         
	         @(posedge clock1);	         
             
	      end
        
`ifdef TEST_WITH_ERROR
	     #(18*clk_period) start = 1;
	     #(clk_period) start = 0;
	     
	     //Second received word contains 6 error symbols.
	     //The decoder sets errfound = 1, and activates
	     //KES block and then CSEE block. Because the
	     //number of errors is equal to correction capability
	     //of the decoder, decoder can correct the received
	     //word.
	     recword = 5'b01100; //it should be 5'b10100
	     #(clk_period) recword = 5'b00100; 
	     #(clk_period) recword = 5'b00101;
	     #(clk_period) recword = 5'b10001;
	     #(clk_period) recword = 5'b10110;
	     #(clk_period) recword = 5'b00001;
	     #(clk_period) recword = 5'b00110; //it should be 5'b00010
	     #(clk_period) recword = 5'b11100;
	     #(clk_period) recword = 5'b00011;
	     #(clk_period) recword = 5'b10001;
	     #(clk_period) recword = 5'b00110;
	     #(clk_period) recword = 5'b00101; //it should be 5'b00111
	     #(clk_period) recword = 5'b01010;
	     #(clk_period) recword = 5'b11111;
	     #(clk_period) recword = 5'b11111; //it should be 5'b01011
	     #(clk_period) recword = 5'b10100;
	     #(clk_period) recword = 5'b00100;
	     #(clk_period) recword = 5'b00101;
	     #(clk_period) recword = 5'b00001;
	     #(clk_period) recword = 5'b10111;
	     #(clk_period) recword = 5'b01101; //it should be 5'b10100
	     #(clk_period) recword = 5'b00010;
	     #(clk_period) recword = 5'b10110;
	     #(clk_period) recword = 5'b00100;
	     #(clk_period) recword = 5'b01011;
	     #(clk_period) recword = 5'b00110;
	     #(clk_period) recword = 5'b11110;
	     #(clk_period) recword = 5'b10100;
	     #(clk_period) recword = 5'b10101; //it should be 5'b11111
	     #(clk_period) recword = 5'b01010;
	     #(clk_period) recword = 5'b11110;
	     #(clk_period) recword = 5'b0;
	     
	     #(20*clk_period) start = 1;
	     #(clk_period) start = 0;
	     //Third received word contains 8 error symbols.
	     //Because the number of errors is greater than correction
	     //capability, decoder will resume decoding failure at the end of
	     //outputted received word.
	     recword = 5'b10100;
	     #(clk_period) recword = 5'b00100; 
	     #(clk_period) recword = 5'b00101;
	     #(clk_period) recword = 5'b10001;
	     #(clk_period) recword = 5'b10110;
	     #(clk_period) recword = 5'b00100; //it should be 5'b00001
	     #(clk_period) recword = 5'b00010; 
	     #(clk_period) recword = 5'b11100;
	     #(clk_period) recword = 5'b10010; //it should be 5'b00011
	     #(clk_period) recword = 5'b10101; //it should be 5'b10001
	     #(clk_period) recword = 5'b00110;
	     #(clk_period) recword = 5'b10011; //it should be 5'b00111
	     #(clk_period) recword = 5'b01010;
	     #(clk_period) recword = 5'b11111;
	     #(clk_period) recword = 5'b01011; 
	     #(clk_period) recword = 5'b10100;
	     #(clk_period) recword = 5'b00110; //it should be 5'b00100
	     #(clk_period) recword = 5'b00101;
	     #(clk_period) recword = 5'b00100; //it should be 5'b00001
	     #(clk_period) recword = 5'b10110; //it should be 5'b10111
	     #(clk_period) recword = 5'b10100;
	     #(clk_period) recword = 5'b00010;
	     #(clk_period) recword = 5'b10110;
	     #(clk_period) recword = 5'b00100;
	     #(clk_period) recword = 5'b01011;
	     #(clk_period) recword = 5'b00110;
	     #(clk_period) recword = 5'b11110;
	     #(clk_period) recword = 5'b10010; //it should be 5'b10100
	     #(clk_period) recword = 5'b11111; 
	     #(clk_period) recword = 5'b01010;
	     #(clk_period) recword = 5'b11110;
	     #(clk_period) recword = 5'b0;

         #(60*clk_period);
`endif

      	$display ("Checking done. Error: %d\n", err_cnt);
        -> END_SIM;
        
     end
   

   
   
   initial begin
      
      golden_cword[0]  = 5'b10100;
      golden_cword[1]  = 5'b00100;
      golden_cword[2]  = 5'b00101;
      golden_cword[3]  = 5'b10001;
      golden_cword[4]  = 5'b10110;
      golden_cword[5]  = 5'b00001;
      golden_cword[6]  = 5'b00010;
      golden_cword[7]  = 5'b11100;
      golden_cword[8]  = 5'b00011;
      golden_cword[9]  = 5'b10001;
      golden_cword[10] = 5'b00110;
      golden_cword[11] = 5'b00111;
      golden_cword[12] = 5'b01010;
      golden_cword[13] = 5'b11111;
      golden_cword[14] = 5'b01011;
      golden_cword[15] = 5'b10100;
      golden_cword[16] = 5'b00100;
      golden_cword[17] = 5'b00101;
      golden_cword[18] = 5'b00001;
      golden_cword[19] = 5'b10111;
      golden_cword[20] = 5'b10100;
      golden_cword[21] = 5'b00010;
      golden_cword[22] = 5'b10110;
      golden_cword[23] = 5'b00100;
      golden_cword[24] = 5'b01011;
      golden_cword[25] = 5'b00110;
      golden_cword[26] = 5'b11110;
      golden_cword[27] = 5'b10100;
      golden_cword[28] = 5'b11111;
      golden_cword[29] = 5'b01010;
      golden_cword[30] = 5'b11110;
      golden_cword[31] = 5'b00000;


   end

   rsdecoder dut(
		         .recword(recword), 
		         .clock1(clock1), 
		         .clock2(clock2), 
		         .start(start), 
		         .reset(reset), 
		         .ready(ready),
		         .decode_fail(decode_fail), 
		         .errfound(errfound), 
		         .dataoutstart(dataoutstart), 
		         .dataoutend(dataoutend),
		         .corr_recword(corr_recword)
		         );
   
endmodule
