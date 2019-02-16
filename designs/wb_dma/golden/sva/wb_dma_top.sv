`include "wb_dma_defines.v"

module assert_wb_dma_top(input clk_i, rst_i,
                         input [31:0] wb0s_data_i, wb0s_data_o, wb0_addr_i, 
                         input [3:0] wb0_sel_i, 
                         input wb0_we_i, wb0_cyc_i,
                         input wb0_stb_i, wb0_ack_o, wb0_err_o, wb0_rty_o,
                         input [31:0] wb0m_data_i, wb0m_data_o, wb0_addr_o, 
                         input [3:0] wb0_sel_o, 
                         input wb0_we_o, wb0_cyc_o,	wb0_stb_o, wb0_ack_i, 
                         input wb0_err_i, wb0_rty_i,
                         input [31:0] wb1s_data_i, wb1s_data_o, wb1_addr_i, 
                         input [3:0] wb1_sel_i, 
                         input wb1_we_i, wb1_cyc_i,
                         input wb1_stb_i, wb1_ack_o, wb1_err_o, wb1_rty_o,
                         input [31:0] wb1m_data_i, wb1m_data_o, wb1_addr_o, 
                         input [3:0] wb1_sel_o, 
                         input wb1_we_o, wb1_cyc_o,	wb1_stb_o, wb1_ack_i, 
                         input wb1_err_i, wb1_rty_i,
                         input [30:0] dma_req_i, dma_ack_o, dma_nd_i, dma_rest_i,
                         input inta_o, intb_o,
                         input [31:0]txsz
                         );


   initial $display("%m is binded");

   // 3.2.2 HW Handshake Mode
   property single_trunk;
      @(posedge clk_i)
        disable iff(!rst_i)
          $rose(dma_req_i) ##0 $fell(dma_req_i)[->1]
          |->
          $fell(dma_ack_o);
   endproperty

   property dma_req_wb;
      @(posedge clk_i) disable iff(!rst_i)
        $rose(dma_req_i)
        |=>
        ($rose(wb0_cyc_o) || $rose(wb1_cyc_o));
   endproperty

   property wb_ack_dma;
      @(posedge clk_i) disable iff(!rst_i)
        $fell(wb0_ack_i) || $fell(wb1_ack_i)
        |=>
        $fell(dma_ack_o);
   endproperty

   // Assumption
   assume_wb0_ack_pulse:assume property(@(posedge clk_i) disable iff(!rst_i) $rose(wb0_ack_i) |=> $fell(wb0_ack_i));
   assume_wb1_ack_pulse:assume property(@(posedge clk_i) disable iff(!rst_i) $rose(wb1_ack_i) |=> $fell(wb1_ack_i));
   assume_dma_req_dma:  assume property(@(posedge clk_i) disable iff(!rst_i) dma_ack_o |-> dma_req_i);   
   `ifndef VENNSA_DYNAMIC_SIMULATION
   assume_dma_req_fall: assume property(@(posedge clk_i) disable iff(!rst_i) $fell(wb0_cyc_o) && $fell(wb1_cyc_o) |=> $fell(dma_req_i));
   assume_wb_ack_dma:   assume property (wb_ack_dma);
   `endif
   assume_dma_req_rise: assume property (dma_req_wb);
   assume_single_trunk: assume property (single_trunk);
   

endmodule // assert_wb_dma_top

bind wb_dma assert_wb_dma_top check_wb_dma_top(.*);
