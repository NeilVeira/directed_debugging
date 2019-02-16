module assert_wb_dma_wb_if(input clk, rst,
                           input wb_ack_i,
                           input [31:0] mast_din, mast_dout,
                           input mast_go, mast_wait, mast_we,
                           input [31:0] wbs_data_i, wbs_data_o,
                           input wb_stb_o, wb_cyc_o, wb_we_o,
                           input pt_sel_i, pt_sel_o
                           );

   initial $display("%m binded");

   property mast_data;
      @(posedge clk) disable iff(!rst) if (!$isunknown(wbs_data_i))
        (wb_ack_i
        |=>
        mast_dout == $past(wbs_data_i));
   endproperty
   
   property wb_stb;
      @(posedge clk) disable iff(!rst)
        (!pt_sel_i)
        |->
        wb_stb_o == ($past(mast_go) && !$past(mast_wait));
   endproperty

   property wb_cyc;
      @(posedge clk) disable iff(!rst)
        (!pt_sel_i)
        |->
        wb_cyc_o == $past(mast_go);
   endproperty
   
   property wb_we;
      @(posedge clk) disable iff(!rst)
        (!pt_sel_i)
        |->
        wb_we_o == $past(mast_we);
   endproperty
   
   // Assertion
   a_mast_data: assert property(mast_data);
   a_wb_stb:    assert property(wb_stb);
   a_wb_cyc:    assert property(wb_cyc);
   a_wb_we:     assert property(wb_we);

   
endmodule // assert_wb_dma_wb_if

bind wb_dma_wb_if assert_wb_dma_wb_if check_wb_dma_wb_if(.*);

