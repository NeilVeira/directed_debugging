`include "wb_dma_defines.v"

module assert_wb_dma_ch_sel(input clk, rst,
                            input de_start,dma_busy,
                            input [4:0] ch_sel,
                            input valid_sel,
                            input [30:0] valid,
                            input ndr,
                            input [30:0] nd_i, req_i, ack_o,
                            input [31:0] ch0_csr,
                            input [2:0] pri_out,
                            input [4:0] gnt_p0, gnt_p1, gnt_p2, gnt_p3,
                            input [4:0] gnt_p4, gnt_p5, gnt_p6, gnt_p7,
                            input [4:0] ch_sel_d
                            );


   initial $display("%m binded");
   
   property dma_start;
      @(posedge clk) disable iff(!rst)
        $rose(valid_sel)
        |->
        de_start;
   endproperty

   property valid_0;
      @(posedge clk) disable iff(!rst)
        (req_i[0] && !ack_o[0]) ##1 (ch0_csr[0] && !ack_o[0])
        |->
        valid[0];
   endproperty

   
   property ndr_0;
      @(posedge clk) disable iff(!rst)
        (ch_sel == 0)
        |->
        ndr == ($past(nd_i[0]) && $past(req_i[0]));
   endproperty
      
   property busy_ch_sel;
      @(posedge clk) disable iff(!rst) if(!$isunknown({ch_sel, $past(ch_sel_d)}))
        $rose(valid_sel) ##1 dma_busy
        |->
        ch_sel == $past(ch_sel_d);
   endproperty

   property ch_select;
      @(posedge clk) disable iff(!rst)
        if(pri_out==0) ch_sel_d == gnt_p0
        else if(pri_out==1) ch_sel_d == gnt_p1
        else if(pri_out==2) ch_sel_d == gnt_p2
        else if(pri_out==3) ch_sel_d == gnt_p3
        else if(pri_out==4) ch_sel_d == gnt_p4
        else if(pri_out==5) ch_sel_d == gnt_p5
        else if(pri_out==6) ch_sel_d == gnt_p6
        else  ch_sel_d == gnt_p7;
   endproperty
        
           
   // Property for for-loop
   property valid_n(i);
      @(posedge clk) disable iff(!rst)
        req_i[i] && !ack_o[i] ##1 !ack_o[i]
        |->
        valid[i];
   endproperty
   
   property valid_select(i);
      @(posedge clk) disable iff(!rst)
        (ch_sel == i)
        |->
        valid_sel == valid[i];
   endproperty
         
   property ndr_select(i);
      @(posedge clk) disable iff(!rst)
        (ch_sel == i)
        |->
        ndr == $past(nd_i[i]) && $past(req_i[i]);
   endproperty
   

   // Assertion
   a_dma_start: assert property(dma_start);
   a_valid_0:   assert property(valid_0);
   a_ndr_0:     assert property(ndr_0);
   a_busy_ch_sel: assert property(busy_ch_sel);
   a_ch_select: assert property(ch_select);
   
   //genvar i;
   //for (i=0;i<31;i++) begin
   //   assert property (valid_n(i));
   //   assert property (valid_select(i));
   //   assert property (ndr_select(i));   
   //end
  
   
endmodule


bind wb_dma_ch_sel assert_wb_dma_ch_sel check_wb_dma_ch_sel(.*);
