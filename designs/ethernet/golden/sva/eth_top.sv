module check_ethernet(input wb_clk_i, wb_rst_i,
                      input wb_stb_i, wb_cyc_i,
                      input wb_we_i,
                      input [3:0] wb_sel_i,
                      input [9:0] wb_adr_i,
                      input [31:0] wb_dat_i, wb_dat_o
                      );
   
   initial $display("check_ethernet is binded");


   sequence wb_write_enable;
      wb_stb_i && wb_cyc_i && wb_we_i;
   endsequence
   
   sequence carrier_sense_for_reg; 
      wb_adr_i[9:8] == 0; //ADDR == 0x3FF
   endsequence
   
   // Store the data for checking (OnPoint 1.4 doesn't support local variable in assertion)
   reg [31:0] wb_wr_dat;
   always@(posedge wb_clk_i)
     if(wb_rst_i) wb_wr_dat <= 0;
     else if (wb_stb_i && wb_cyc_i && wb_we_i) wb_wr_dat <= wb_dat_i;

   // wb data passing through the dut
   assert_full_data_pass:
     assert property (@(posedge wb_clk_i) disable iff(wb_rst_i)
                      wb_write_enable ##0 carrier_sense_for_reg ##0 wb_sel_i==4'hf ##1 !wb_we_i[->1]
                      |=> wb_dat_o == wb_wr_dat);
   
   
endmodule // check_ethernet

bind eth_top check_ethernet check_eth_top(.*);

                      
