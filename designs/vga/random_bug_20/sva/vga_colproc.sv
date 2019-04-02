module check_vga_colproc(input clk, srst,
                         input [6:0] c_state,
                         input rgb_fifo_full, vdat_buffer_empty,ivdat_buf_rreq,
                         input vdat_buffer_rreq, rgb_fifo_wreq,
                         input [1:0] ColorDepth,
                         input RGBbuf_wreq);

   initial
     $display("assert_vga_colproc binded");


     // Note: this assertion was originally commented out for simulation flow
   property a_vdat_buffer_rreq;
      @(posedge clk)
        if(!srst)
          if(c_state == 7'b0)
            ((!rgb_fifo_full && !vdat_buffer_empty)
             |->
            ivdat_buf_rreq)
            ;
   endproperty
   assertion_a_vdat_buffer_rreq: assert property (a_vdat_buffer_rreq) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      $display("%t: %b %b %b %b", $time, c_state, rgb_fifo_full, vdat_buffer_empty, ivdat_buf_rreq);
      -> test.ERROR;
`endif
   end

   property a_rgb_fifo_wreq_low;
      @(posedge clk)
        srst
        |=>
        (!rgb_fifo_wreq);
   endproperty
   assertion_a_rgb_fifo_wreq_low: assert property (a_rgb_fifo_wreq_low) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
   end
   

// Property for simulation only
`ifdef VENNSA_DYNAMIC_SIMULATION
   property a_rgb_fifo_wreq;
      @(posedge clk)
        if(!srst)
          if(c_state >= 7'd2 && c_state!=7'd4)
            (!rgb_fifo_full
             |=>
             rgb_fifo_wreq)
            ;
   endproperty
   assertion_a_rgb_fifo_wreq: assert property (a_rgb_fifo_wreq) else begin
      $error;
      -> test.ERROR;
   end

   property a_mux_mode;
      disable iff(srst)
        @(posedge clk)
          if(ColorDepth == 1)
            ($rose(c_state) |=> c_state==8)
          else if (ColorDepth == 2)
            ($rose(c_state) |=> c_state == 32)
          else if (ColorDepth == 3)
            ($rose(c_state) |=> c_state == 64)
          else
            ($rose(c_state) |=> c_state <= 4)
          ;
   endproperty
   assertion_a_mux_mode: assert property (a_mux_mode) else begin
      $error;
      -> test.ERROR;
   end
   
`endif
   
endmodule

bind vga_colproc check_vga_colproc a_vga_colproc_i1(.*);

      
            
