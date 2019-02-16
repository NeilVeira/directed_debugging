`include "wb_dma_defines.v"

module assert_wb_dma_ch_pri_enc(input clk,
                                input [30:0]valid,				// Channel Valid bits
                                input [2:0]	pri0, pri1, pri2, pri3,		// Channel Priorities
                                input [2:0]	pri4, pri5, pri6, pri7,
                                input [2:0]	pri8, pri9, pri10, pri11,
                                input [2:0]	pri12, pri13, pri14, pri15,
                                input [2:0]	pri16, pri17, pri18, pri19,
                                input [2:0]	pri20, pri21, pri22, pri23,
                                input [2:0]	pri24, pri25, pri26, pri27,
                                input [2:0]	pri28, pri29, pri30,
                                input [2:0]	pri_out,			// Highest unserviced priority
                                input [7:0]	pri0_out, pri1_out, pri2_out, pri3_out,
                                input [7:0]	pri4_out, pri5_out, pri6_out, pri7_out,
                                input [7:0]	pri8_out, pri9_out, pri10_out, pri11_out,
                                input [7:0]	pri12_out, pri13_out, pri14_out, pri15_out,
                                input [7:0]	pri16_out, pri17_out, pri18_out, pri19_out,
                                input [7:0]	pri20_out, pri21_out, pri22_out, pri23_out,
                                input [7:0]	pri24_out, pri25_out, pri26_out, pri27_out,
                                input [7:0]	pri28_out, pri29_out, pri30_out,
                                input [7:0]	pri_out_tmp,
                                input [2:0]	pri_out2,
                                input [2:0]	pri_out1,
                                input [2:0]	pri_out0,
                                input [1:0]	pri_sel,
                                input [3:0]	ch0_conf,
                                input [3:0]	ch1_conf,
                                input [3:0]	ch2_conf,
                                input [3:0]	ch3_conf,
                                input [3:0]	ch4_conf,
                                input [3:0]	ch5_conf,
                                input [3:0]	ch6_conf,
                                input [3:0]	ch7_conf,
                                input [3:0]	ch8_conf,
                                input [3:0]	ch9_conf,
                                input [3:0]	ch10_conf,
                                input [3:0]	ch11_conf,
                                input [3:0]	ch12_conf,
                                input [3:0]	ch13_conf,
                                input [3:0]	ch14_conf,
                                input [3:0]	ch15_conf,
                                input [3:0]	ch16_conf,
                                input [3:0]	ch17_conf,
                                input [3:0]	ch18_conf,
                                input [3:0]	ch19_conf,
                                input [3:0]	ch20_conf,
                                input [3:0]	ch21_conf,
                                input [3:0]	ch22_conf,
                                input [3:0]	ch23_conf,
                                input [3:0]	ch24_conf,
                                input [3:0]	ch25_conf,
                                input [3:0]	ch26_conf,
                                input [3:0]	ch27_conf,
                                input [3:0]	ch28_conf,
                                input [3:0]	ch29_conf,
                                input [3:0]	ch30_conf
                                );


   initial $display("%m is binded");

   property one_hot(ch_conf, out);
      @(posedge clk)
      ch_conf[0] 
      |->
      $onehot(out);
   endproperty

   a_onehot_pri0_out: assert property(one_hot(ch1_conf, pri0_out));
   a_onehot_pri1_out: assert property(one_hot(ch1_conf, pri1_out));
   a_onehot_pri2_out: assert property(one_hot(ch2_conf, pri2_out));
   a_onehot_pri3_out: assert property(one_hot(ch3_conf, pri3_out));
   a_onehot_pri4_out: assert property(one_hot(ch4_conf, pri4_out));
   a_onehot_pri5_out: assert property(one_hot(ch5_conf, pri5_out));
   a_onehot_pri6_out: assert property(one_hot(ch6_conf, pri6_out));
   a_onehot_pri7_out: assert property(one_hot(ch7_conf, pri7_out));
   a_onehot_pri8_out: assert property(one_hot(ch8_conf, pri8_out));
   a_onehot_pri9_out: assert property(one_hot(ch9_conf, pri9_out));
   a_onehot_pri10_out: assert property(one_hot(ch10_conf, pri10_out));
   a_onehot_pri11_out: assert property(one_hot(ch11_conf, pri11_out));
   a_onehot_pri12_out: assert property(one_hot(ch12_conf, pri12_out));
   a_onehot_pri13_out: assert property(one_hot(ch13_conf, pri13_out));
   a_onehot_pri14_out: assert property(one_hot(ch14_conf, pri14_out));
   a_onehot_pri15_out: assert property(one_hot(ch15_conf, pri15_out));
   a_onehot_pri16_out: assert property(one_hot(ch16_conf, pri16_out));
   a_onehot_pri17_out: assert property(one_hot(ch17_conf, pri17_out));
   a_onehot_pri18_out: assert property(one_hot(ch18_conf, pri18_out));
   a_onehot_pri19_out: assert property(one_hot(ch19_conf, pri19_out));
   a_onehot_pri20_out: assert property(one_hot(ch20_conf, pri20_out));
   a_onehot_pri21_out: assert property(one_hot(ch21_conf, pri21_out));
   a_onehot_pri22_out: assert property(one_hot(ch22_conf, pri22_out));
   a_onehot_pri23_out: assert property(one_hot(ch23_conf, pri23_out));
   a_onehot_pri24_out: assert property(one_hot(ch24_conf, pri24_out));
   a_onehot_pri25_out: assert property(one_hot(ch25_conf, pri25_out));
   a_onehot_pri26_out: assert property(one_hot(ch26_conf, pri26_out));
   a_onehot_pri27_out: assert property(one_hot(ch27_conf, pri27_out));
   a_onehot_pri28_out: assert property(one_hot(ch28_conf, pri28_out));
   a_onehot_pri29_out: assert property(one_hot(ch29_conf, pri29_out));
   a_onehot_pri30_out: assert property(one_hot(ch30_conf, pri30_out));
endmodule

bind wb_dma_ch_pri_enc assert_wb_dma_ch_pri_enc check_wb_dma_ch_pri_enc(.*);
