`include "wb_dma_defines.v"

module assert_wb_dma_rf (
input		clk, rst,

// WISHBONE Access
input	[7:0]	wb_rf_adr,
input	[31:0]	wb_rf_din,
input	[31:0]	wb_rf_dout,
input		wb_rf_re,
input		wb_rf_we,

// WISHBONE Interrupt outputs
input		inta_o, intb_o,
input	[31:0]	pointer0, pointer0_s, ch0_csr, ch0_txsz, ch0_adr0, ch0_adr1, ch0_am0, ch0_am1,
input	[31:0]	pointer1, pointer1_s, ch1_csr, ch1_txsz, ch1_adr0, ch1_adr1, ch1_am0, ch1_am1,
input	[31:0]	pointer2, pointer2_s, ch2_csr, ch2_txsz, ch2_adr0, ch2_adr1, ch2_am0, ch2_am1,
input	[31:0]	pointer3, pointer3_s, ch3_csr, ch3_txsz, ch3_adr0, ch3_adr1, ch3_am0, ch3_am1,
input	[31:0]	pointer4, pointer4_s, ch4_csr, ch4_txsz, ch4_adr0, ch4_adr1, ch4_am0, ch4_am1,
input	[31:0]	pointer5, pointer5_s, ch5_csr, ch5_txsz, ch5_adr0, ch5_adr1, ch5_am0, ch5_am1,
input	[31:0]	pointer6, pointer6_s, ch6_csr, ch6_txsz, ch6_adr0, ch6_adr1, ch6_am0, ch6_am1,
input	[31:0]	pointer7, pointer7_s, ch7_csr, ch7_txsz, ch7_adr0, ch7_adr1, ch7_am0, ch7_am1,
input	[31:0]	pointer8, pointer8_s, ch8_csr, ch8_txsz, ch8_adr0, ch8_adr1, ch8_am0, ch8_am1,
input	[31:0]	pointer9, pointer9_s, ch9_csr, ch9_txsz, ch9_adr0, ch9_adr1, ch9_am0, ch9_am1,
input	[31:0]	pointer10, pointer10_s, ch10_csr, ch10_txsz, ch10_adr0, ch10_adr1, ch10_am0, ch10_am1,
input	[31:0]	pointer11, pointer11_s, ch11_csr, ch11_txsz, ch11_adr0, ch11_adr1, ch11_am0, ch11_am1,
input	[31:0]	pointer12, pointer12_s, ch12_csr, ch12_txsz, ch12_adr0, ch12_adr1, ch12_am0, ch12_am1,
input	[31:0]	pointer13, pointer13_s, ch13_csr, ch13_txsz, ch13_adr0, ch13_adr1, ch13_am0, ch13_am1,
input	[31:0]	pointer14, pointer14_s, ch14_csr, ch14_txsz, ch14_adr0, ch14_adr1, ch14_am0, ch14_am1,
input	[31:0]	pointer15, pointer15_s, ch15_csr, ch15_txsz, ch15_adr0, ch15_adr1, ch15_am0, ch15_am1,
input	[31:0]	pointer16, pointer16_s, ch16_csr, ch16_txsz, ch16_adr0, ch16_adr1, ch16_am0, ch16_am1,
input	[31:0]	pointer17, pointer17_s, ch17_csr, ch17_txsz, ch17_adr0, ch17_adr1, ch17_am0, ch17_am1,
input	[31:0]	pointer18, pointer18_s, ch18_csr, ch18_txsz, ch18_adr0, ch18_adr1, ch18_am0, ch18_am1,
input	[31:0]	pointer19, pointer19_s, ch19_csr, ch19_txsz, ch19_adr0, ch19_adr1, ch19_am0, ch19_am1,
input	[31:0]	pointer20, pointer20_s, ch20_csr, ch20_txsz, ch20_adr0, ch20_adr1, ch20_am0, ch20_am1,
input	[31:0]	pointer21, pointer21_s, ch21_csr, ch21_txsz, ch21_adr0, ch21_adr1, ch21_am0, ch21_am1,
input	[31:0]	pointer22, pointer22_s, ch22_csr, ch22_txsz, ch22_adr0, ch22_adr1, ch22_am0, ch22_am1,
input	[31:0]	pointer23, pointer23_s, ch23_csr, ch23_txsz, ch23_adr0, ch23_adr1, ch23_am0, ch23_am1,
input	[31:0]	pointer24, pointer24_s, ch24_csr, ch24_txsz, ch24_adr0, ch24_adr1, ch24_am0, ch24_am1,
input	[31:0]	pointer25, pointer25_s, ch25_csr, ch25_txsz, ch25_adr0, ch25_adr1, ch25_am0, ch25_am1,
input	[31:0]	pointer26, pointer26_s, ch26_csr, ch26_txsz, ch26_adr0, ch26_adr1, ch26_am0, ch26_am1,
input	[31:0]	pointer27, pointer27_s, ch27_csr, ch27_txsz, ch27_adr0, ch27_adr1, ch27_am0, ch27_am1,
input	[31:0]	pointer28, pointer28_s, ch28_csr, ch28_txsz, ch28_adr0, ch28_adr1, ch28_am0, ch28_am1,
input	[31:0]	pointer29, pointer29_s, ch29_csr, ch29_txsz, ch29_adr0, ch29_adr1, ch29_am0, ch29_am1,
input	[31:0]	pointer30, pointer30_s, ch30_csr, ch30_txsz, ch30_adr0, ch30_adr1, ch30_am0, ch30_am1,

input	[4:0]	ch_sel,		// Write Back Channel Select
input	[30:0]	ndnr,		// Next Descriptor No Request

// DMA Engine Abort
input		dma_abort,

// DMA Engine Status
input		pause_req,
input		paused,
input		dma_busy, dma_err, dma_done, dma_done_all,

// DMA Engine Reg File Update ctrl signals
input	[31:0]	de_csr,
input	[11:0]	de_txsz,
input	[31:0]	de_adr0,
input	[31:0]	de_adr1,
input		de_csr_we, de_txsz_we, de_adr0_we, de_adr1_we, ptr_set,
input		de_fetch_descr,
input	[30:0]	dma_rest,

////////////////////////////////////////////////////////////////////
//
// Local Wires and Registers
//
input    [30:0]	int_maska_r, int_maskb_r,
input	[31:0]	int_maska, int_maskb,
input	[31:0]	int_srca, int_srcb,
input		int_maska_we, int_maskb_we,
input	[30:0]	ch_int,
input		csr_we,
input	[31:0]	csr,
input    [7:0]	csr_r,
input	[30:0]	ch_stop,
input	[30:0]	ch_dis,

input	[31:0]	sw_pointer0, sw_pointer1, sw_pointer2, sw_pointer3,
input	[31:0]	sw_pointer4, sw_pointer5, sw_pointer6, sw_pointer7,
input	[31:0]	sw_pointer8, sw_pointer9, sw_pointer10, sw_pointer11,
input	[31:0]	sw_pointer12, sw_pointer13, sw_pointer14, sw_pointer15,
input	[31:0]	sw_pointer16, sw_pointer17, sw_pointer18, sw_pointer19,
input	[31:0]	sw_pointer20, sw_pointer21, sw_pointer22, sw_pointer23,
input	[31:0]	sw_pointer24, sw_pointer25, sw_pointer26, sw_pointer27,
input	[31:0]	sw_pointer28, sw_pointer29, sw_pointer30,

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

   property read_logic(value, in);
      @(posedge clk)
        disable iff(!rst) if(!$isunknown(in))
          wb_rf_adr == value 
          |=> 
          wb_rf_dout == $past(in);
   endproperty

   property read_logic_cond(value, cond, in);
      @(posedge clk)
        disable iff(!rst) if(!$isunknown({cond,in}))
          wb_rf_adr == value 
          |=> 
          (  ($past(cond) && wb_rf_dout == $past(in)) || 
            (~$past(cond) && wb_rf_dout == 32'h0));
   endproperty

   a_int_maska:
   assert property(
      @(posedge clk)
        disable iff(!rst)
          (|(int_maska_r & ch_int)) |=> inta_o
   );
   a_int_maskb:
   assert property(
      @(posedge clk)
        disable iff(!rst)
          (|(int_maskb_r & ch_int)) |=> intb_o
   );

   a_csr_we:
   assert property(
       @(posedge clk)
        disable iff(!rst)
          wb_rf_we & (wb_rf_adr == 8'h0) |-> csr_we
   );

   a_int_maska_we:
   assert property(
       @(posedge clk)
        disable iff(!rst)
          wb_rf_we & (wb_rf_adr == 8'h1) |-> int_maska_we
   );

   a_int_maskb_we:
   assert property(
       @(posedge clk)
        disable iff(!rst)
          wb_rf_we & (wb_rf_adr == 8'h2) |-> int_maskb_we
   );

   // Assumption
   
   // Assertion
   read_logic_h0: assert property (read_logic(8'h0, csr));
   read_logic_h1: assert property (read_logic(8'h1, int_maska));
   read_logic_h2: assert property (read_logic(8'h2, int_maskb));
   read_logic_h3: assert property (read_logic(8'h3, int_srca));
   read_logic_h4: assert property (read_logic(8'h4, int_srcb));
   read_logic_h8: assert property (read_logic(8'h8, ch0_csr));
   read_logic_h9: assert property (read_logic(8'h9, ch0_txsz));
   read_logic_ha: assert property (read_logic(8'ha, ch0_adr0));
   read_logic_hb: assert property (read_logic(8'hb, ch0_am0));
   read_logic_hc: assert property (read_logic(8'hc, ch0_adr1));
   read_logic_hd: assert property (read_logic(8'hd, ch0_am1));
   read_logic_he: assert property (read_logic(8'he, pointer0));
   read_logic_hf: assert property (read_logic(8'hf, sw_pointer0));
   read_logic_h10: assert property (read_logic_cond(8'h10, ch1_conf[0], ch1_csr  ));
   read_logic_h11: assert property (read_logic_cond(8'h11, ch1_conf[0], ch1_txsz ));
   read_logic_h12: assert property (read_logic_cond(8'h12, ch1_conf[0], ch1_adr0 ));
   read_logic_h13: assert property (read_logic_cond(8'h13, ch1_conf[0], ch1_am0  ));
   read_logic_h14: assert property (read_logic_cond(8'h14, ch1_conf[0], ch1_adr1 ));
   read_logic_h15: assert property (read_logic_cond(8'h15, ch1_conf[0], ch1_am1  ));
   read_logic_h16: assert property (read_logic_cond(8'h16, ch1_conf[0], pointer1 ));
   read_logic_h17: assert property (read_logic_cond(8'h17, ch1_conf[0], sw_pointer1 ));
   read_logic_h18: assert property (read_logic_cond(8'h18, ch2_conf[0], ch2_csr  ));
   read_logic_h19: assert property (read_logic_cond(8'h19, ch2_conf[0], ch2_txsz ));
   read_logic_h1a: assert property (read_logic_cond(8'h1a, ch2_conf[0], ch2_adr0 ));
   read_logic_h1b: assert property (read_logic_cond(8'h1b, ch2_conf[0], ch2_am0  ));
   read_logic_h1c: assert property (read_logic_cond(8'h1c, ch2_conf[0], ch2_adr1 ));
   read_logic_h1d: assert property (read_logic_cond(8'h1d, ch2_conf[0], ch2_am1  ));
   read_logic_h1e: assert property (read_logic_cond(8'h1e, ch2_conf[0], pointer2 ));
   read_logic_h1f: assert property (read_logic_cond(8'h1f, ch2_conf[0], sw_pointer2 ));
   read_logic_h20: assert property (read_logic_cond(8'h20, ch3_conf[0], ch3_csr  ));
   read_logic_h21: assert property (read_logic_cond(8'h21, ch3_conf[0], ch3_txsz ));
   read_logic_h22: assert property (read_logic_cond(8'h22, ch3_conf[0], ch3_adr0 ));
   read_logic_h23: assert property (read_logic_cond(8'h23, ch3_conf[0], ch3_am0  ));
   read_logic_h24: assert property (read_logic_cond(8'h24, ch3_conf[0], ch3_adr1 ));
   read_logic_h25: assert property (read_logic_cond(8'h25, ch3_conf[0], ch3_am1  ));
   read_logic_h26: assert property (read_logic_cond(8'h26, ch3_conf[0], pointer3 ));
   read_logic_h27: assert property (read_logic_cond(8'h27, ch3_conf[0], sw_pointer3 ));
   read_logic_h28: assert property (read_logic_cond(8'h28, ch4_conf[0], ch4_csr  ));
   read_logic_h29: assert property (read_logic_cond(8'h29, ch4_conf[0], ch4_txsz ));
   read_logic_h2a: assert property (read_logic_cond(8'h2a, ch4_conf[0], ch4_adr0 ));
   read_logic_h2b: assert property (read_logic_cond(8'h2b, ch4_conf[0], ch4_am0  ));
   read_logic_h2c: assert property (read_logic_cond(8'h2c, ch4_conf[0], ch4_adr1 ));
   read_logic_h2d: assert property (read_logic_cond(8'h2d, ch4_conf[0], ch4_am1  ));
   read_logic_h2e: assert property (read_logic_cond(8'h2e, ch4_conf[0], pointer4 ));
   read_logic_h2f: assert property (read_logic_cond(8'h2f, ch4_conf[0], sw_pointer4 ));
   read_logic_h30: assert property (read_logic_cond(8'h30, ch5_conf[0], ch5_csr  ));
   read_logic_h31: assert property (read_logic_cond(8'h31, ch5_conf[0], ch5_txsz ));
   read_logic_h32: assert property (read_logic_cond(8'h32, ch5_conf[0], ch5_adr0 ));
   read_logic_h33: assert property (read_logic_cond(8'h33, ch5_conf[0], ch5_am0  ));
   read_logic_h34: assert property (read_logic_cond(8'h34, ch5_conf[0], ch5_adr1 ));
   read_logic_h35: assert property (read_logic_cond(8'h35, ch5_conf[0], ch5_am1  ));
   read_logic_h36: assert property (read_logic_cond(8'h36, ch5_conf[0], pointer5 ));
   read_logic_h37: assert property (read_logic_cond(8'h37, ch5_conf[0], sw_pointer5 ));
   read_logic_h38: assert property (read_logic_cond(8'h38, ch6_conf[0], ch6_csr  ));
   read_logic_h39: assert property (read_logic_cond(8'h39, ch6_conf[0], ch6_txsz ));
   read_logic_h3a: assert property (read_logic_cond(8'h3a, ch6_conf[0], ch6_adr0 ));
   read_logic_h3b: assert property (read_logic_cond(8'h3b, ch6_conf[0], ch6_am0  ));
   read_logic_h3c: assert property (read_logic_cond(8'h3c, ch6_conf[0], ch6_adr1 ));
   read_logic_h3d: assert property (read_logic_cond(8'h3d, ch6_conf[0], ch6_am1  ));
   read_logic_h3e: assert property (read_logic_cond(8'h3e, ch6_conf[0], pointer6 ));
   read_logic_h3f: assert property (read_logic_cond(8'h3f, ch6_conf[0], sw_pointer6 ));
   read_logic_h40: assert property (read_logic_cond(8'h40, ch7_conf[0], ch7_csr  ));
   read_logic_h41: assert property (read_logic_cond(8'h41, ch7_conf[0], ch7_txsz ));
   read_logic_h42: assert property (read_logic_cond(8'h42, ch7_conf[0], ch7_adr0 ));
   read_logic_h43: assert property (read_logic_cond(8'h43, ch7_conf[0], ch7_am0  ));
   read_logic_h44: assert property (read_logic_cond(8'h44, ch7_conf[0], ch7_adr1 ));
   read_logic_h45: assert property (read_logic_cond(8'h45, ch7_conf[0], ch7_am1  ));
   read_logic_h46: assert property (read_logic_cond(8'h46, ch7_conf[0], pointer7 ));
   read_logic_h47: assert property (read_logic_cond(8'h47, ch7_conf[0], sw_pointer7 ));
   read_logic_h48: assert property (read_logic_cond(8'h48, ch8_conf[0], ch8_csr  ));
   read_logic_h49: assert property (read_logic_cond(8'h49, ch8_conf[0], ch8_txsz ));
   read_logic_h4a: assert property (read_logic_cond(8'h4a, ch8_conf[0], ch8_adr0 ));
   read_logic_h4b: assert property (read_logic_cond(8'h4b, ch8_conf[0], ch8_am0  ));
   read_logic_h4c: assert property (read_logic_cond(8'h4c, ch8_conf[0], ch8_adr1 ));
   read_logic_h4d: assert property (read_logic_cond(8'h4d, ch8_conf[0], ch8_am1  ));
   read_logic_h4e: assert property (read_logic_cond(8'h4e, ch8_conf[0], pointer8 ));
   read_logic_h4f: assert property (read_logic_cond(8'h4f, ch8_conf[0], sw_pointer8 ));
   read_logic_h50: assert property (read_logic_cond(8'h50, ch9_conf[0], ch9_csr  ));
   read_logic_h51: assert property (read_logic_cond(8'h51, ch9_conf[0], ch9_txsz ));
   read_logic_h52: assert property (read_logic_cond(8'h52, ch9_conf[0], ch9_adr0 ));
   read_logic_h53: assert property (read_logic_cond(8'h53, ch9_conf[0], ch9_am0  ));
   read_logic_h54: assert property (read_logic_cond(8'h54, ch9_conf[0], ch9_adr1 ));
   read_logic_h55: assert property (read_logic_cond(8'h55, ch9_conf[0], ch9_am1  ));
   read_logic_h56: assert property (read_logic_cond(8'h56, ch9_conf[0], pointer9 ));
   read_logic_h57: assert property (read_logic_cond(8'h57, ch9_conf[0], sw_pointer9 ));
   read_logic_h58: assert property (read_logic_cond(8'h58, ch10_conf[0], ch10_csr  ));
   read_logic_h59: assert property (read_logic_cond(8'h59, ch10_conf[0], ch10_txsz ));
   read_logic_h5a: assert property (read_logic_cond(8'h5a, ch10_conf[0], ch10_adr0 ));
   read_logic_h5b: assert property (read_logic_cond(8'h5b, ch10_conf[0], ch10_am0  ));
   read_logic_h5c: assert property (read_logic_cond(8'h5c, ch10_conf[0], ch10_adr1 ));
   read_logic_h5d: assert property (read_logic_cond(8'h5d, ch10_conf[0], ch10_am1  ));
   read_logic_h5e: assert property (read_logic_cond(8'h5e, ch10_conf[0], pointer10 ));
   read_logic_h5f: assert property (read_logic_cond(8'h5f, ch10_conf[0], sw_pointer10 ));
   read_logic_h60: assert property (read_logic_cond(8'h60, ch11_conf[0], ch11_csr  ));
   read_logic_h61: assert property (read_logic_cond(8'h61, ch11_conf[0], ch11_txsz ));
   read_logic_h62: assert property (read_logic_cond(8'h62, ch11_conf[0], ch11_adr0 ));
   read_logic_h63: assert property (read_logic_cond(8'h63, ch11_conf[0], ch11_am0  ));
   read_logic_h64: assert property (read_logic_cond(8'h64, ch11_conf[0], ch11_adr1 ));
   read_logic_h65: assert property (read_logic_cond(8'h65, ch11_conf[0], ch11_am1  ));
   read_logic_h66: assert property (read_logic_cond(8'h66, ch11_conf[0], pointer11 ));
   read_logic_h67: assert property (read_logic_cond(8'h67, ch11_conf[0], sw_pointer11 ));
   read_logic_h68: assert property (read_logic_cond(8'h68, ch12_conf[0], ch12_csr  ));
   read_logic_h69: assert property (read_logic_cond(8'h69, ch12_conf[0], ch12_txsz ));
   read_logic_h6a: assert property (read_logic_cond(8'h6a, ch12_conf[0], ch12_adr0 ));
   read_logic_h6b: assert property (read_logic_cond(8'h6b, ch12_conf[0], ch12_am0  ));
   read_logic_h6c: assert property (read_logic_cond(8'h6c, ch12_conf[0], ch12_adr1 ));
   read_logic_h6d: assert property (read_logic_cond(8'h6d, ch12_conf[0], ch12_am1  ));
   read_logic_h6e: assert property (read_logic_cond(8'h6e, ch12_conf[0], pointer12 ));
   read_logic_h6f: assert property (read_logic_cond(8'h6f, ch12_conf[0], sw_pointer12 ));
   read_logic_h70: assert property (read_logic_cond(8'h70, ch13_conf[0], ch13_csr  ));
   read_logic_h71: assert property (read_logic_cond(8'h71, ch13_conf[0], ch13_txsz ));
   read_logic_h72: assert property (read_logic_cond(8'h72, ch13_conf[0], ch13_adr0 ));
   read_logic_h73: assert property (read_logic_cond(8'h73, ch13_conf[0], ch13_am0  ));
   read_logic_h74: assert property (read_logic_cond(8'h74, ch13_conf[0], ch13_adr1 ));
   read_logic_h75: assert property (read_logic_cond(8'h75, ch13_conf[0], ch13_am1  ));
   read_logic_h76: assert property (read_logic_cond(8'h76, ch13_conf[0], pointer13 ));
   read_logic_h77: assert property (read_logic_cond(8'h77, ch13_conf[0], sw_pointer13 ));
   read_logic_h78: assert property (read_logic_cond(8'h78, ch14_conf[0], ch14_csr  ));
   read_logic_h79: assert property (read_logic_cond(8'h79, ch14_conf[0], ch14_txsz ));
   read_logic_h7a: assert property (read_logic_cond(8'h7a, ch14_conf[0], ch14_adr0 ));
   read_logic_h7b: assert property (read_logic_cond(8'h7b, ch14_conf[0], ch14_am0  ));
   read_logic_h7c: assert property (read_logic_cond(8'h7c, ch14_conf[0], ch14_adr1 ));
   read_logic_h7d: assert property (read_logic_cond(8'h7d, ch14_conf[0], ch14_am1  ));
   read_logic_h7e: assert property (read_logic_cond(8'h7e, ch14_conf[0], pointer14 ));
   read_logic_h7f: assert property (read_logic_cond(8'h7f, ch14_conf[0], sw_pointer14 ));
   read_logic_h80: assert property (read_logic_cond(8'h80, ch15_conf[0], ch15_csr  ));
   read_logic_h81: assert property (read_logic_cond(8'h81, ch15_conf[0], ch15_txsz ));
   read_logic_h82: assert property (read_logic_cond(8'h82, ch15_conf[0], ch15_adr0 ));
   read_logic_h83: assert property (read_logic_cond(8'h83, ch15_conf[0], ch15_am0  ));
   read_logic_h84: assert property (read_logic_cond(8'h84, ch15_conf[0], ch15_adr1 ));
   read_logic_h85: assert property (read_logic_cond(8'h85, ch15_conf[0], ch15_am1  ));
   read_logic_h86: assert property (read_logic_cond(8'h86, ch15_conf[0], pointer15 ));
   read_logic_h87: assert property (read_logic_cond(8'h87, ch15_conf[0], sw_pointer15 ));
   read_logic_h88: assert property (read_logic_cond(8'h88, ch16_conf[0], ch16_csr  ));
   read_logic_h89: assert property (read_logic_cond(8'h89, ch16_conf[0], ch16_txsz ));
   read_logic_h8a: assert property (read_logic_cond(8'h8a, ch16_conf[0], ch16_adr0 ));
   read_logic_h8b: assert property (read_logic_cond(8'h8b, ch16_conf[0], ch16_am0  ));
   read_logic_h8c: assert property (read_logic_cond(8'h8c, ch16_conf[0], ch16_adr1 ));
   read_logic_h8d: assert property (read_logic_cond(8'h8d, ch16_conf[0], ch16_am1  ));
   read_logic_h8e: assert property (read_logic_cond(8'h8e, ch16_conf[0], pointer16 ));
   read_logic_h8f: assert property (read_logic_cond(8'h8f, ch16_conf[0], sw_pointer16 ));
   read_logic_h90: assert property (read_logic_cond(8'h90, ch17_conf[0], ch17_csr  ));
   read_logic_h91: assert property (read_logic_cond(8'h91, ch17_conf[0], ch17_txsz ));
   read_logic_h92: assert property (read_logic_cond(8'h92, ch17_conf[0], ch17_adr0 ));
   read_logic_h93: assert property (read_logic_cond(8'h93, ch17_conf[0], ch17_am0  ));
   read_logic_h94: assert property (read_logic_cond(8'h94, ch17_conf[0], ch17_adr1 ));
   read_logic_h95: assert property (read_logic_cond(8'h95, ch17_conf[0], ch17_am1  ));
   read_logic_h96: assert property (read_logic_cond(8'h96, ch17_conf[0], pointer17 ));
   read_logic_h97: assert property (read_logic_cond(8'h97, ch17_conf[0], sw_pointer17 ));
   read_logic_h98: assert property (read_logic_cond(8'h98, ch18_conf[0], ch18_csr  ));
   read_logic_h99: assert property (read_logic_cond(8'h99, ch18_conf[0], ch18_txsz ));
   read_logic_h9a: assert property (read_logic_cond(8'h9a, ch18_conf[0], ch18_adr0 ));
   read_logic_h9b: assert property (read_logic_cond(8'h9b, ch18_conf[0], ch18_am0  ));
   read_logic_h9c: assert property (read_logic_cond(8'h9c, ch18_conf[0], ch18_adr1 ));
   read_logic_h9d: assert property (read_logic_cond(8'h9d, ch18_conf[0], ch18_am1  ));
   read_logic_h9e: assert property (read_logic_cond(8'h9e, ch18_conf[0], pointer18 ));
   read_logic_h9f: assert property (read_logic_cond(8'h9f, ch18_conf[0], sw_pointer18 ));
   read_logic_ha0: assert property (read_logic_cond(8'ha0, ch19_conf[0], ch19_csr  ));
   read_logic_ha1: assert property (read_logic_cond(8'ha1, ch19_conf[0], ch19_txsz ));
   read_logic_ha2: assert property (read_logic_cond(8'ha2, ch19_conf[0], ch19_adr0 ));
   read_logic_ha3: assert property (read_logic_cond(8'ha3, ch19_conf[0], ch19_am0  ));
   read_logic_ha4: assert property (read_logic_cond(8'ha4, ch19_conf[0], ch19_adr1 ));
   read_logic_ha5: assert property (read_logic_cond(8'ha5, ch19_conf[0], ch19_am1  ));
   read_logic_ha6: assert property (read_logic_cond(8'ha6, ch19_conf[0], pointer19 ));
   read_logic_ha7: assert property (read_logic_cond(8'ha7, ch19_conf[0], sw_pointer19 ));
   read_logic_ha8: assert property (read_logic_cond(8'ha8, ch20_conf[0], ch20_csr  ));
   read_logic_ha9: assert property (read_logic_cond(8'ha9, ch20_conf[0], ch20_txsz ));
   read_logic_haa: assert property (read_logic_cond(8'haa, ch20_conf[0], ch20_adr0 ));
   read_logic_hab: assert property (read_logic_cond(8'hab, ch20_conf[0], ch20_am0  ));
   read_logic_hac: assert property (read_logic_cond(8'hac, ch20_conf[0], ch20_adr1 ));
   read_logic_had: assert property (read_logic_cond(8'had, ch20_conf[0], ch20_am1  ));
   read_logic_hae: assert property (read_logic_cond(8'hae, ch20_conf[0], pointer20 ));
   read_logic_haf: assert property (read_logic_cond(8'haf, ch20_conf[0], sw_pointer20 ));
   read_logic_hb0: assert property (read_logic_cond(8'hb0, ch21_conf[0], ch21_csr  ));
   read_logic_hb1: assert property (read_logic_cond(8'hb1, ch21_conf[0], ch21_txsz ));
   read_logic_hb2: assert property (read_logic_cond(8'hb2, ch21_conf[0], ch21_adr0 ));
   read_logic_hb3: assert property (read_logic_cond(8'hb3, ch21_conf[0], ch21_am0  ));
   read_logic_hb4: assert property (read_logic_cond(8'hb4, ch21_conf[0], ch21_adr1 ));
   read_logic_hb5: assert property (read_logic_cond(8'hb5, ch21_conf[0], ch21_am1  ));
   read_logic_hb6: assert property (read_logic_cond(8'hb6, ch21_conf[0], pointer21 ));
   read_logic_hb7: assert property (read_logic_cond(8'hb7, ch21_conf[0], sw_pointer21 ));
   read_logic_hb8: assert property (read_logic_cond(8'hb8, ch22_conf[0], ch22_csr  ));
   read_logic_hb9: assert property (read_logic_cond(8'hb9, ch22_conf[0], ch22_txsz ));
   read_logic_hba: assert property (read_logic_cond(8'hba, ch22_conf[0], ch22_adr0 ));
   read_logic_hbb: assert property (read_logic_cond(8'hbb, ch22_conf[0], ch22_am0  ));
   read_logic_hbc: assert property (read_logic_cond(8'hbc, ch22_conf[0], ch22_adr1 ));
   read_logic_hbd: assert property (read_logic_cond(8'hbd, ch22_conf[0], ch22_am1  ));
   read_logic_hbe: assert property (read_logic_cond(8'hbe, ch22_conf[0], pointer22 ));
   read_logic_hbf: assert property (read_logic_cond(8'hbf, ch22_conf[0], sw_pointer22 ));
   read_logic_hc0: assert property (read_logic_cond(8'hc0, ch23_conf[0], ch23_csr  ));
   read_logic_hc1: assert property (read_logic_cond(8'hc1, ch23_conf[0], ch23_txsz ));
   read_logic_hc2: assert property (read_logic_cond(8'hc2, ch23_conf[0], ch23_adr0 ));
   read_logic_hc3: assert property (read_logic_cond(8'hc3, ch23_conf[0], ch23_am0  ));
   read_logic_hc4: assert property (read_logic_cond(8'hc4, ch23_conf[0], ch23_adr1 ));
   read_logic_hc5: assert property (read_logic_cond(8'hc5, ch23_conf[0], ch23_am1  ));
   read_logic_hc6: assert property (read_logic_cond(8'hc6, ch23_conf[0], pointer23 ));
   read_logic_hc7: assert property (read_logic_cond(8'hc7, ch23_conf[0], sw_pointer23 ));
   read_logic_hc8: assert property (read_logic_cond(8'hc8, ch24_conf[0], ch24_csr  ));
   read_logic_hc9: assert property (read_logic_cond(8'hc9, ch24_conf[0], ch24_txsz ));
   read_logic_hca: assert property (read_logic_cond(8'hca, ch24_conf[0], ch24_adr0 ));
   read_logic_hcb: assert property (read_logic_cond(8'hcb, ch24_conf[0], ch24_am0  ));
   read_logic_hcc: assert property (read_logic_cond(8'hcc, ch24_conf[0], ch24_adr1 ));
   read_logic_hcd: assert property (read_logic_cond(8'hcd, ch24_conf[0], ch24_am1  ));
   read_logic_hce: assert property (read_logic_cond(8'hce, ch24_conf[0], pointer24 ));
   read_logic_hcf: assert property (read_logic_cond(8'hcf, ch24_conf[0], sw_pointer24 ));
   read_logic_hd0: assert property (read_logic_cond(8'hd0, ch25_conf[0], ch25_csr  ));
   read_logic_hd1: assert property (read_logic_cond(8'hd1, ch25_conf[0], ch25_txsz ));
   read_logic_hd2: assert property (read_logic_cond(8'hd2, ch25_conf[0], ch25_adr0 ));
   read_logic_hd3: assert property (read_logic_cond(8'hd3, ch25_conf[0], ch25_am0  ));
   read_logic_hd4: assert property (read_logic_cond(8'hd4, ch25_conf[0], ch25_adr1 ));
   read_logic_hd5: assert property (read_logic_cond(8'hd5, ch25_conf[0], ch25_am1  ));
   read_logic_hd6: assert property (read_logic_cond(8'hd6, ch25_conf[0], pointer25 ));
   read_logic_hd7: assert property (read_logic_cond(8'hd7, ch25_conf[0], sw_pointer25 ));
   read_logic_hd8: assert property (read_logic_cond(8'hd8, ch26_conf[0], ch26_csr  ));
   read_logic_hd9: assert property (read_logic_cond(8'hd9, ch26_conf[0], ch26_txsz ));
   read_logic_hda: assert property (read_logic_cond(8'hda, ch26_conf[0], ch26_adr0 ));
   read_logic_hdb: assert property (read_logic_cond(8'hdb, ch26_conf[0], ch26_am0  ));
   read_logic_hdc: assert property (read_logic_cond(8'hdc, ch26_conf[0], ch26_adr1 ));
   read_logic_hdd: assert property (read_logic_cond(8'hdd, ch26_conf[0], ch26_am1  ));
   read_logic_hde: assert property (read_logic_cond(8'hde, ch26_conf[0], pointer26 ));
   read_logic_hdf: assert property (read_logic_cond(8'hdf, ch26_conf[0], sw_pointer26 ));
   read_logic_he0: assert property (read_logic_cond(8'he0, ch27_conf[0], ch27_csr  ));
   read_logic_he1: assert property (read_logic_cond(8'he1, ch27_conf[0], ch27_txsz ));
   read_logic_he2: assert property (read_logic_cond(8'he2, ch27_conf[0], ch27_adr0 ));
   read_logic_he3: assert property (read_logic_cond(8'he3, ch27_conf[0], ch27_am0  ));
   read_logic_he4: assert property (read_logic_cond(8'he4, ch27_conf[0], ch27_adr1 ));
   read_logic_he5: assert property (read_logic_cond(8'he5, ch27_conf[0], ch27_am1  ));
   read_logic_he6: assert property (read_logic_cond(8'he6, ch27_conf[0], pointer27 ));
   read_logic_he7: assert property (read_logic_cond(8'he7, ch27_conf[0], sw_pointer27 ));
   read_logic_he8: assert property (read_logic_cond(8'he8, ch28_conf[0], ch28_csr  ));
   read_logic_he9: assert property (read_logic_cond(8'he9, ch28_conf[0], ch28_txsz ));
   read_logic_hea: assert property (read_logic_cond(8'hea, ch28_conf[0], ch28_adr0 ));
   read_logic_heb: assert property (read_logic_cond(8'heb, ch28_conf[0], ch28_am0  ));
   read_logic_hec: assert property (read_logic_cond(8'hec, ch28_conf[0], ch28_adr1 ));
   read_logic_hed: assert property (read_logic_cond(8'hed, ch28_conf[0], ch28_am1  ));
   read_logic_hee: assert property (read_logic_cond(8'hee, ch28_conf[0], pointer28 ));
   read_logic_hef: assert property (read_logic_cond(8'hef, ch28_conf[0], sw_pointer28 ));
   read_logic_hf0: assert property (read_logic_cond(8'hf0, ch29_conf[0], ch29_csr  ));
   read_logic_hf1: assert property (read_logic_cond(8'hf1, ch29_conf[0], ch29_txsz ));
   read_logic_hf2: assert property (read_logic_cond(8'hf2, ch29_conf[0], ch29_adr0 ));
   read_logic_hf3: assert property (read_logic_cond(8'hf3, ch29_conf[0], ch29_am0  ));
   read_logic_hf4: assert property (read_logic_cond(8'hf4, ch29_conf[0], ch29_adr1 ));
   read_logic_hf5: assert property (read_logic_cond(8'hf5, ch29_conf[0], ch29_am1  ));
   read_logic_hf6: assert property (read_logic_cond(8'hf6, ch29_conf[0], pointer29 ));
   read_logic_hf7: assert property (read_logic_cond(8'hf7, ch29_conf[0], sw_pointer29 ));
   read_logic_hf8: assert property (read_logic_cond(8'hf8, ch30_conf[0], ch30_csr  ));
   read_logic_hf9: assert property (read_logic_cond(8'hf9, ch30_conf[0], ch30_txsz ));
   read_logic_hfa: assert property (read_logic_cond(8'hfa, ch30_conf[0], ch30_adr0 ));
   read_logic_hfb: assert property (read_logic_cond(8'hfb, ch30_conf[0], ch30_am0  ));
   read_logic_hfc: assert property (read_logic_cond(8'hfc, ch30_conf[0], ch30_adr1 ));
   read_logic_hfd: assert property (read_logic_cond(8'hfd, ch30_conf[0], ch30_am1  ));
   read_logic_hfe: assert property (read_logic_cond(8'hfe, ch30_conf[0], pointer30 ));
   read_logic_hff: assert property (read_logic_cond(8'hff, ch30_conf[0], sw_pointer30 ));


endmodule // assert_wb_dma_rf 

bind wb_dma_rf assert_wb_dma_rf  check_wb_dma_rf (.*);
