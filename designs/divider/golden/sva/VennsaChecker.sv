`ifdef VENNSA_DYNAMIC_SIMULATION
 `ifdef VENNSA_END_CHECKER

module sigMap( input clk,
              input [8:0] s,
              input [8:0] q
              );

assertion_s: assert property (@(posedge clk)
  if(!$isunknown(bench_div_top.sc  [8:0]))
    s == bench_div_top.sc [8:0])
  else begin
    if(!$isunknown($sampled({s, bench_div_top.sc})))
      $error;
  end

assertion_q: assert property (@(posedge clk)
  if(!$isunknown(bench_div_top.qc  [8:0]))
    q == bench_div_top.qc [8:0])
  else begin
    if(!$isunknown($sampled({q, bench_div_top.qc})))
      $error;
  end

endmodule
bind divider sigMap sigMap_i1(.*);

 `endif
`endif
