`include "wb_dma_defines.v"

module assert_wb_dma_ch_arb(input clk,
                            input rst,
                            input [30:0]req,		// Req input
                            input [4:0]	gnt, 		// Grant output
                            input		advance,	// Next Target
                            input [4:0] grant0,
                                        grant1, grant2, grant3, grant4, grant5,
                                        grant6, grant7, grant8, grant9, grant10,
                                        grant11, grant12, grant13, grant14, grant15,
                                        grant16, grant17, grant18, grant19, grant20,
                                        grant21, grant22, grant23, grant24, grant25,
                                        grant26, grant27, grant28, grant29, grant30,
                            input [4:0]	state, next_state
                            );
   
   initial $display("%m is binded");

   property grant_req(req_state, request);
      @(posedge clk)
        disable iff(!rst)
        state == req_state && (~request) && (|(req))
        |=>
        state != req_state;
   endproperty

   a_grant_req0: assert property(grant_req(grant0, req[0]));
   a_grant_req1: assert property(grant_req(grant1, req[1]));
   a_grant_req2: assert property(grant_req(grant2, req[2]));
   a_grant_req3: assert property(grant_req(grant3, req[3]));
   a_grant_req4: assert property(grant_req(grant4, req[4]));
   a_grant_req5: assert property(grant_req(grant5, req[5]));
   a_grant_req6: assert property(grant_req(grant6, req[6]));
   a_grant_req7: assert property(grant_req(grant7, req[7]));
   a_grant_req8: assert property(grant_req(grant8, req[8]));
   a_grant_req9: assert property(grant_req(grant9, req[9]));
   a_grant_req10: assert property(grant_req(grant10, req[10]));
   a_grant_req11: assert property(grant_req(grant11, req[11]));
   a_grant_req12: assert property(grant_req(grant12, req[12]));
   a_grant_req13: assert property(grant_req(grant13, req[13]));
   a_grant_req14: assert property(grant_req(grant14, req[14]));
   a_grant_req15: assert property(grant_req(grant15, req[15]));
   a_grant_req16: assert property(grant_req(grant16, req[16]));
   a_grant_req17: assert property(grant_req(grant17, req[17]));
   a_grant_req18: assert property(grant_req(grant18, req[18]));
   a_grant_req19: assert property(grant_req(grant19, req[19]));
   a_grant_req20: assert property(grant_req(grant20, req[20]));
   a_grant_req21: assert property(grant_req(grant21, req[21]));
   a_grant_req22: assert property(grant_req(grant22, req[22]));
   a_grant_req23: assert property(grant_req(grant23, req[23]));
   a_grant_req24: assert property(grant_req(grant24, req[24]));
   a_grant_req25: assert property(grant_req(grant25, req[25]));
   a_grant_req26: assert property(grant_req(grant26, req[26]));
   a_grant_req27: assert property(grant_req(grant27, req[27]));
   a_grant_req28: assert property(grant_req(grant28, req[28]));
   a_grant_req29: assert property(grant_req(grant29, req[29]));
   a_grant_req30: assert property(grant_req(grant30, req[30]));
endmodule // assert_wb_dma_ch_arb

bind wb_dma_ch_arb assert_wb_dma_ch_arb check_wb_dma_ch_arb(.*);
