module check_vga_top(input clk_p_i, wb_clk_i, rst_i,
                     input ctrl_ven,
                     input luint_pclk, luint, sluint, ctrl_ven_not,
                     input wbs_stb_i,
                     input wbs_ack_o,
                     input fb_data_fifo_rreq, fb_data_fifo_empty, 
                     input [31:0]fb_data_fifo_q,
                     input line_fifo_wreq, line_fifo_rreq, line_fifo_empty_rd, line_fifo_full_wr,
                     input blank_pad_o,
                     input [7:0] r_pad_o, g_pad_o, b_pad_o
                     );

   initial 
     $display("assert_vga_top binded");
      

   //glue circuit
   property a_luint_pclk;
      @(posedge clk_p_i)
        (line_fifo_rreq && line_fifo_empty_rd) |=> luint_pclk;
   endproperty
   assertion_a_luint_pclk: assert property (a_luint_pclk) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_initial;
      @(posedge wb_clk_i)
        (!ctrl_ven) |=> (~sluint && ~luint);
   endproperty
   assertion_a_initial: assert property (a_initial) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end
      
   property a_sluint;
      @(posedge wb_clk_i)
        ctrl_ven |=> (sluint == $past(luint_pclk));
   endproperty
   assertion_a_sluint: assert property (a_sluint) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_luint;
      @(posedge wb_clk_i)
        ctrl_ven |=> (luint == $past(sluint));
   endproperty
   assertion_a_luint: assert property (a_luint) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_ctrl_ven_not;
      @(posedge clk_p_i)
        !ctrl_ven |-> (ctrl_ven_not);
   endproperty
   assertion_a_ctrl_ven_not: assert property (a_ctrl_ven_not) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end


// Property for simulation flow only
`ifdef VENNSA_DYNAMIC_SIMULATION
   property a_stb_ack;
      @(posedge wb_clk_i)
        (!wbs_stb_i && $past(wbs_stb_i)) 
        |->
        $fell(wbs_ack_o);
   endproperty
   assertion_a_stb_ack: assert property(a_stb_ack) else begin
      $error;
      -> test.ERROR;
   end

   property a_fifo_rreq;
      @(posedge wb_clk_i)
        fb_data_fifo_empty |-> fb_data_fifo_empty throughout !fb_data_fifo_rreq;
   endproperty
   assertion_a_fifo_rreq: assert property (a_fifo_rreq) else begin
      $error;
      -> test.ERROR;
   end
      
   property a_line_fifo_full;
      @(posedge wb_clk_i)
        line_fifo_wreq && !line_fifo_full_wr && $past(line_fifo_full_wr) |=> line_fifo_full_wr;
   endproperty
   assertion_a_line_fifo_full: assert property(a_line_fifo_full) else begin
      $error;
      -> test.ERROR;
   end

   //Comment out for the external reference error Verific returns
   /*
   property a_rgb_end_checker;
      @(posedge clk_p_i)
        disable iff(rst_i)
          (!blank_pad_o) 
          |-> 
          ({r_pad_o,g_pad_o,b_pad_o} !== test.pd)
          ;
   endproperty
   assertion_a_rgb_end_checker: assert property (a_rgb_end_checker) else begin
      $error;
      -> test.ERROR;
   end
   */

`endif
   
endmodule

bind vga check_vga_top chk_top_i1(.*);
 
