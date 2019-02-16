`include "wb_dma_defines.v"

module assert_wb_dma_ch_rf (
input		clk, rst,

input	[31:0]	pointer,
input	[31:0]	pointer_s,
input	[31:0]	ch_csr,
input	[31:0]	ch_txsz,
input	[31:0]	ch_adr0,
input	[31:0]	ch_adr1,
input	[31:0]	ch_am0,
input	[31:0]	ch_am1,
input	[31:0]	sw_pointer,
input		ch_stop,
input		ch_dis,
input		intt,

input	[31:0]	wb_rf_din,
input	[7:0]	wb_rf_adr,
input		wb_rf_we,
input		wb_rf_re,

input	[4:0]	ch_sel,
input		ndnr,

// DMA Engine Status
input		dma_busy, dma_err, dma_done, dma_done_all,

// DMA Engine Reg File Update ctrl signals
input	[31:0]	de_csr,
input	[11:0]	de_txsz,
input	[31:0]	de_adr0,
input	[31:0]	de_adr1,
input		de_csr_we, de_txsz_we, de_adr0_we, de_adr1_we, ptr_set,
input		de_fetch_descr,
input		dma_rest,

////////////////////////////////////////////////////////////////////
//
// Local Wires and Registers
//

input    [27:0]	pointer_sr,
input	ptr_valid,
input	ch_eol,
input    [8:0]	ch_csr_r,
input    [2:0]	ch_csr_r2,
input    [2:0]	ch_csr_r3,
input    [2:0]	int_src_r,
input	ch_err_r,
input	ch_busy,
input	ch_done,
input	ch_err,
input	rest_en,
input    [10:0]	ch_chk_sz_r,
input    [11:0]	ch_tot_sz_r,
input    [22:0]	ch_txsz_s,
input	ch_sz_inf,
input    [29:0]	ch_adr0_r, ch_adr1_r,
input    [27:0]	ch_am0_r, ch_am1_r,
input    [29:0]	ch_adr0_s, ch_adr1_s,
input    [29:0]	sw_pointer_r,
input		sw_pointer_we,
input	[28:0]	cmp_adr,
input		ch_enable,
input		pointer_we,
input		ch_csr_we, ch_csr_re, ch_txsz_we, ch_adr0_we, ch_adr1_we,
input		ch_am0_we, ch_am1_we,
input	ch_rl,
input		ch_done_we,
input		ch_err_we,
input		chunk_done_we,
input		ch_csr_dewe, ch_txsz_dewe, ch_adr0_dewe, ch_adr1_dewe,
input		this_ptr_set,
input		ptr_inv,
input       CH_EN,
input [4:0]	CH_ADR
);


   initial $display("%m is binded");

   property unclocked_disabled(in);
      @(posedge clk)
        disable iff(!rst)
          ~CH_EN |-> ~in;
   endproperty

unclocked_disabled_ch_adr0		: assert property(unclocked_disabled(ch_adr0));      
unclocked_disabled_ch_adr1		: assert property(unclocked_disabled(ch_adr1));      
unclocked_disabled_ch_am0		: assert property(unclocked_disabled(ch_am0));  
unclocked_disabled_ch_am1		: assert property(unclocked_disabled(ch_am1));  
unclocked_disabled_sw_pointer	: assert property(unclocked_disabled(sw_pointer));  
unclocked_disabled_pointer		: assert property(unclocked_disabled(pointer   ));      
unclocked_disabled_pointer_s	: assert property(unclocked_disabled(pointer_s ));  
unclocked_disabled_ch_csr		: assert property(unclocked_disabled(ch_csr	   ));  
unclocked_disabled_ch_txsz		: assert property(unclocked_disabled(ch_txsz   ));      
unclocked_disabled_ch_enable	: assert property(unclocked_disabled(ch_enable ));  
unclocked_disabled_ch_csr_we	: assert property(unclocked_disabled(ch_csr_we ));  
unclocked_disabled_ch_csr_re	: assert property(unclocked_disabled(ch_csr_re ));  
unclocked_disabled_ch_txsz_we	: assert property(unclocked_disabled(ch_txsz_we));  
unclocked_disabled_ch_adr0_we	: assert property(unclocked_disabled(ch_adr0_we));  
unclocked_disabled_ch_am0_we	: assert property(unclocked_disabled(ch_am0_we ));  
unclocked_disabled_ch_adr1_we	: assert property(unclocked_disabled(ch_adr1_we));  
unclocked_disabled_ch_am1_we	: assert property(unclocked_disabled(ch_am1_we ));  
unclocked_disabled_pointer_we	: assert property(unclocked_disabled(pointer_we));  
unclocked_disabled_sw_pointer_we: assert property(unclocked_disabled(sw_pointer_we));  
unclocked_disabled_ch_done_we	: assert property(unclocked_disabled(ch_done_we	  ));  
unclocked_disabled_chunk_done_we: assert property(unclocked_disabled(chunk_done_we));  
unclocked_disabled_ch_err_we	: assert property(unclocked_disabled(ch_err_we	  ));  
unclocked_disabled_ch_csr_dewe	: assert property(unclocked_disabled(ch_csr_dewe  ));      
unclocked_disabled_ch_txsz_dewe	: assert property(unclocked_disabled(ch_txsz_dewe ));  
unclocked_disabled_ch_adr0_dewe	: assert property(unclocked_disabled(ch_adr0_dewe ));  
unclocked_disabled_ch_adr1_dewe	: assert property(unclocked_disabled(ch_adr1_dewe ));  
unclocked_disabled_this_ptr_set : assert property(unclocked_disabled(this_ptr_set ));   
unclocked_disabled_intt : assert property(unclocked_disabled(intt ));   


   property clocked_disabled(in);
      @(posedge clk)
        disable iff(!rst)
          ~CH_EN |=> ~in;
   endproperty

clocked_disabled_ptr_valid : assert property(clocked_disabled(ptr_valid));
clocked_disabled_ch_eol    : assert property(clocked_disabled(ch_eol));
clocked_disabled_ch_stop   : assert property(clocked_disabled(ch_stop));
clocked_disabled_ch_busy   : assert property(clocked_disabled(ch_busy));
clocked_disabled_ch_done   : assert property(clocked_disabled(ch_done));
clocked_disabled_ch_err    : assert property(clocked_disabled(ch_err));
clocked_disabled_rest_en   : assert property(clocked_disabled(rest_en));
clocked_disabled_ch_rl     : assert property(clocked_disabled(ch_rl));


    a_we:
    assert property(
        @(posedge clk)
            disable iff(!rst)
            CH_EN & wb_rf_we & (wb_rf_adr[7:3] == CH_ADR)
            |->
            ch_csr_we  | ch_csr_re |  ch_txsz_we |  ch_adr0_we |  ch_am0_we |  
            ch_adr1_we |  ch_am1_we| pointer_we  |  sw_pointer_we);

    a_ch_rf_interrupt_output:
    assert property(
        @(posedge clk)
            disable iff(!rst)
            (|(ch_csr_r3 & {$past(chunk_done_we), $past(ch_done_we), $past(ch_err_we)})) & CH_EN
            |->
            intt
    );
endmodule

bind wb_dma_ch_rf assert_wb_dma_ch_rf check_wb_dma_ch_rf(.*);
