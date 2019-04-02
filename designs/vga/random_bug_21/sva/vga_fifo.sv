module check_vga_fifo(input clk, aclr, sclr,
                      input frreq, fwreq, rreq, wreq,
                      input [4:1] rp, wp,             
                      input [4:0] nword
                      );

   initial
     $display("assert_vga_fifo binded");


   wire rst;
   assign rst = ~aclr || sclr;
   
   property rd_pt;
      @(posedge clk) 
        if(!rst)
          (frreq 
           |=> 
           rp == {$past(rp[3:1]),~($past(rp[4]) ^ $past(rp[3]))});
   endproperty

   property wr_pt;
      @(posedge clk) 
        if(!rst)
          (fwreq 
           |=> 
           wp == {$past(wp[3:1]),~($past(wp[4]) ^ $past(wp[3]))});
   endproperty

   //assert property
   _a_read_pointer: assert property(rd_pt) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end 
   
   _a_write_pointer: assert property(wr_pt) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end


// Property for simulation flow only
`ifdef VENNSA_DYNAMIC_SIMULATION

   property word_up_count;
      @(posedge clk) 
        disable iff(~aclr || sclr)
          ((wreq & !rreq)
          |=>
           nword == $past(nword) + 1);
   endproperty

   property word_down_count;
      @(posedge clk) 
        disable iff(~aclr || sclr)
        ((rreq & !wreq)
        |=>
        nword == ($past(nword) - 1));
   endproperty
   
   //assert property
   _a_word_up_counter: assert property(word_up_count) else begin
      $error;
      -> test.ERROR;
   end

   _a_word_down_counter: assert property (word_down_count) else begin
      $error;
      -> test.ERROR;
   end

`endif
      
endmodule

bind vga_fifo check_vga_fifo chk_fifo_i1(.*);
