module check_fifo4(input clk, rst, clr,
                   input [1:0] wp, rp,
                   input gb, empty, full, re, we);

   initial
     $display("assert_fifo4 binded");

   property fifo_clr;
      disable iff(!rst)
        @(posedge clk)
          clr 
          |=> 
          (wp == 2'b0 && rp ==2'b0 && gb == 1'b0);
   endproperty
   a_fifo_clr: assert property(fifo_clr) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      ->tst_bench_top.ERROR;
`endif
   end

   wire disable_cond = !rst || clr;

   property fifo_empty;
      disable iff(disable_cond)
        @(posedge clk)
          (re && (rp+2'h1)==wp)
          |=>
          empty;
   endproperty
   a_fifo_empty: assert property(fifo_empty) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      ->tst_bench_top.ERROR;
`endif
   end

   property fifo_full;
      disable iff(disable_cond)
        @(posedge clk)
          (we && (wp+2'h1)==rp)
          |=>
          full;
   endproperty
   a_fifo_full: assert property(fifo_full) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      ->tst_bench_top.ERROR;
`endif
   end
     
endmodule

bind fifo4 check_fifo4 assert_fifo4_i1(.*);

