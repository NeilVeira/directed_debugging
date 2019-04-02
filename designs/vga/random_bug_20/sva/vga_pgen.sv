module check_vga_pgen(input pclk_i, clk_i, ctrl_ven, pclk_ena,
                      input eol, eof,
                      input seol, dseol, seof, dseof,
                      input ihsync, ctrl_HSyncL, hsync_o,
                      input sclr, dImDoneFifoQ, clut_switch,
                      input stat_acmp, ctrl_cbsw,
                      input [7:0] r_o, g_o, b_o,
                      input [23:0] line_fifo_q,
                      input line_fifo_full, rgb_fifo_empty, rgb_fifo_rreq);

   initial
     $display("assert_vga_pgen binded");


   property a_initial;
      @(posedge clk_i)
        ~ctrl_ven |=> ((seol || dseol || seof || dseof)==0);
   endproperty
   assertion_a_initial: assert property (a_initial) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end
      
   property a_seol;
      @(posedge clk_i)
        ctrl_ven |=> (seol == $past(eol));
   endproperty
   assertion_a_seol: assert property(a_seol) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_dseol;
      @(posedge clk_i)
        ctrl_ven |=> (dseol == $past(seol));
   endproperty
   assertion_a_dseol: assert property(a_dseol) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_seof;
      @(posedge clk_i)
        ctrl_ven |=> (seof == $past(eof));
   endproperty
   assertion_a_seof: assert property(a_seof) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_dseof;
      @(posedge clk_i)
        ctrl_ven |=> (dseof == $past(seof));
   endproperty
   assertion_a_dseof: assert property(a_dseof) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_hsync_o;
      @(posedge pclk_i)
        (ihsync ^ ctrl_HSyncL) |=> ##1 hsync_o;
   endproperty
   assertion_a_hsync_o: assert property (a_hsync_o) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_stat_acmp;
      @(posedge clk_i)
        disable iff (sclr)
          (ctrl_cbsw && !stat_acmp && clut_switch) 
          or 
          (ctrl_cbsw && stat_acmp && !clut_switch)
          |=>
          stat_acmp
          ;
   endproperty
   assertion_a_stat_acmp: assert property (a_stat_acmp) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

   property a_rgb_o;
      @(posedge pclk_i)
        disable iff (!ctrl_ven)
          if(!$isunknown(line_fifo_q)) 
            (pclk_ena 
            |=> 
            ((r_o == $past(line_fifo_q[23:16]))
            and
            (g_o == $past(line_fifo_q[15: 8]))
            and
            (b_o == $past(line_fifo_q[ 7: 0]))));
   endproperty
   assertion_a_rgb_o: assert property (a_rgb_o) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      $display("%0t, %b, %b", $time,r_o,$past(line_fifo_q[23:16])); 
      -> test.ERROR;
`endif
   end 
   
   property a_rgb_fifo_rreq;
      @(posedge clk_i)
        !(line_fifo_full || rgb_fifo_empty)
        |->
        rgb_fifo_rreq
        ;
   endproperty
   assertion_a_rgb_fifo_rreq: assert property (a_rgb_fifo_rreq) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end

// Property for simulation flow only
`ifdef VENNSA_DYNAMIC_SIMULATION
   property a_clut_switch;
      @(posedge clk_i)
        disable iff(sclr)
          ($past(dImDoneFifoQ) && !dImDoneFifoQ) |-> clut_switch;
   endproperty
   assertion_a_clut_switch: assert property (a_clut_switch) else begin
      $error;
      -> test.ERROR;
   end   

`endif   

endmodule

bind vga_pgen check_vga_pgen assert_vga_i1(.*);

