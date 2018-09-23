module sigMap( input clock2,
              input [4:0] corr_recword
              );

assertion_corr_recword: assert property (@(posedge clock2)
  if(!$isunknown(testbench_rsdecoder.signal_DebuggerGolden  [4:0]))
    corr_recword == testbench_rsdecoder.signal_DebuggerGolden [4:0])
  else begin
    if(!$isunknown($sampled({corr_recword, testbench_rsdecoder.signal_DebuggerGolden})))
      $error;
  end

endmodule
bind rsdecoder sigMap sigMap_i1(.*);
