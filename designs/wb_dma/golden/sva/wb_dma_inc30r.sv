module assert_wb_dma_inc30r(input clk,
                            input [29:0] in, out
                            );


   initial $display("%m binded");

   property inc_addr;
      @(posedge clk)
        (in != 30'h3fffffff) && (in == $past(in)) //need two cycle to stablize the sugnal
        |->
        (out == in + 1);
   endproperty
 
   a_inc_addr:    assert property(inc_addr);

endmodule // assert_wb_dma_inc30r

bind wb_dma_inc30r assert_wb_dma_inc30r check_wb_dma_inc30r(.*);
