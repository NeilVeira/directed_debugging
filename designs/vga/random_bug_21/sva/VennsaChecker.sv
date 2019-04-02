`ifdef VENNSA_DYNAMIC_SIMULATION
 `ifdef VENNSA_END_CHECKER

module sigMap( input wb_clk_i,
              input [7:0] r_pad_o,
              input [7:0] g_pad_o,
              input [7:0] b_pad_o,
              input [31:0] wbs_dat_o,
              input [31:0] wbm_adr_o,
              input  hsync_pad_o,
              input  vsync_pad_o,
              input  csync_pad_o,
              input  blank_pad_o
              );

assertion_r_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.red_golden  [7:0]))
    r_pad_o == test.red_golden [7:0])
  else begin
    if(!$isunknown($sampled({r_pad_o, test.red_golden})))
      $error;
  end

assertion_g_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.green_golden  [7:0]))
    g_pad_o == test.green_golden [7:0])
  else begin
    if(!$isunknown($sampled({g_pad_o, test.green_golden})))
      $error;
  end

assertion_b_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.blue_golden  [7:0]))
    b_pad_o == test.blue_golden [7:0])
  else begin
    if(!$isunknown($sampled({b_pad_o, test.blue_golden})))
      $error;
  end

assertion_wbs_dat_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.wb_data_o_golden  [31:0]))
    wbs_dat_o == test.wb_data_o_golden [31:0])
  else begin
    if(!$isunknown($sampled({wbs_dat_o, test.wb_data_o_golden})))
      $error;
  end

assertion_wbm_adr_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.wb_addr_o_golden  [31:0]))
    wbm_adr_o == test.wb_addr_o_golden [31:0])
  else begin
    if(!$isunknown($sampled({wbm_adr_o, test.wb_addr_o_golden})))
      $error;
  end

assertion_hsync_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.hsync_golden  ))
    hsync_pad_o == test.hsync_golden )
  else begin
    if(!$isunknown($sampled({hsync_pad_o, test.hsync_golden})))
      $error;
  end

assertion_vsync_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.vsync_golden  ))
    vsync_pad_o == test.vsync_golden )
  else begin
    if(!$isunknown($sampled({vsync_pad_o, test.vsync_golden})))
      $error;
  end

assertion_csync_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.csync_golden  ))
    csync_pad_o == test.csync_golden )
  else begin
    if(!$isunknown($sampled({csync_pad_o, test.csync_golden})))
      $error;
  end

assertion_blank_pad_o : assert property (@(posedge wb_clk_i)
  if(!$isunknown(test.blanc_golden  ))
    blank_pad_o == test.blanc_golden )
  else begin
    if(!$isunknown($sampled({blank_pad_o, test.blanc_golden})))
      $error;
  end

endmodule
bind vga sigMap sigMap_i1(.*);

 `endif
`endif
