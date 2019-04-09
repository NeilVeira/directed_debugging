module sigMap( input clk,
              input [11:0] dout
              );

assertion_dout: assert property (@(posedge clk)
  if(!$isunknown(bench_top.dout_golden  [11:0]))
    dout == bench_top.dout_golden [11:0])
  else begin
    if(!$isunknown($sampled({dout, bench_top.dout_golden})))
      $error;
  end

endmodule
bind fdct sigMap sigMap_i1(.*);
