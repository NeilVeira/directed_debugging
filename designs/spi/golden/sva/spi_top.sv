module check_spi_top(input clk_i, rst_i, ena,
                     input [1:0] icnt, state, tcnt,
                     input spif, spe, wfempty, wfre, rfwe,
                     input [7:0] treg, wfdout,
                     input [2:0] bcnt,
                     input miso_i,
                     input [1:0] adr_i,
                     input [7:0] dat_o, spcr, spsr, rfdout, sper,
                     input [3:0] espr
                     );

   wire internal_reset = !rst_i || !spe;

   initial
     $display("assert_spi_top binded");

   // down counter
   property interrupt_count_cnt;
      disable iff(internal_reset)
        @(posedge clk_i)
        if (rfwe == 1) (
          (tcnt!=2'b0) 
          |=> 
          tcnt == ($past(tcnt) - 2'b1));
   endproperty
   a_interrupt_count_cnt: assert property(interrupt_count_cnt) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> tst_bench_top.ERROR;
`endif
   end

   
   //4.2.1 Transmitting data bytes
   property transmitting_data_bytes;
      disable iff(!rst_i)
        @(posedge clk_i)
          (($rose(spe) & !wfempty)
          |=>
          treg == $past(wfdout));
   endproperty
   a_transmitting_data_bytes: assert property(transmitting_data_bytes) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> tst_bench_top.ERROR;
`endif
   end

   //4.2.2 Receiving data bytes: R/W
   property receiving_data_bytes_rw;
      disable iff(internal_reset)
        @(posedge clk_i)
            (wfre 
             |-> 
             rfwe[->1] within ($rose(state==1) ##0 (state==0)[->1]));
   endproperty
   a_receiving_data_bytes_rw: assert property(receiving_data_bytes_rw) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      ->tst_bench_top.ERROR;
`endif
   end

   //4.2.2 Receiving data bytes: din
   property receiving_data_bytes_din;
      disable iff(internal_reset)
        @(posedge clk_i)
          ($rose(state[1] && state[0]) && ena
           |=> 
           (treg[0] === $past(miso_i)) and (bcnt == ($past(bcnt)-3'b1)));
   endproperty
   a_receiving_data_bytes_din: assert property(receiving_data_bytes_din) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      ->tst_bench_top.ERROR;
`endif
   end

   //data output mux
   property data_mux;
      disable iff (!rst_i)
        @(posedge clk_i)
          //if(!$isunknown(adr_i))
            (if(adr_i == 0)
              (1'b1 |=> dat_o === $past(spcr))
            else if (adr_i == 1)
              (1'b1 |=> dat_o === $past(spsr))
            else if (adr_i == 2)
              (1'b1 |=> dat_o === $past(rfdout))
            else if (adr_i == 3)
              (1'b1 |=> dat_o === $past(sper))
            else
              1'b1);
   endproperty
   a_data_mux: assert property (data_mux) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> tst_bench_top.ERROR;
`endif
   end

   //transfer counter: reset
   property transfer_counter_rst;
      disable iff (!rst_i)
        @(posedge clk_i)
          (!spe || (rfwe && (tcnt == 0))) 
          |=> 
          tcnt == $past(icnt);
   endproperty
   a_transfer_counter_rst: assert property (transfer_counter_rst) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> tst_bench_top.ERROR;
`endif
   end

   //transfer counter: down counter
   property transfer_counter_dc;
      disable iff (internal_reset)
        @(posedge clk_i)
          (rfwe && (tcnt != 0))
          |=>
          tcnt == $past(tcnt) - 1;
   endproperty
   a_transfer_counter_dc: assert property (transfer_counter_dc) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> tst_bench_top.ERROR;
`endif
   end
        

   //3.5.1 ICNT- Interrupt Count
   // initial set
`ifdef VENNSA_DYNAMIC_SIMULATION
   property interrupt_count_set;
      disable iff(!rst_i)
        @(posedge clk_i)
          if(icnt==2'b0)
            (rfwe |=> spif)
          else if (icnt == 2'b01)
            (rfwe [->2] |=> spif)
          else if (icnt == 2'b10)
            (rfwe [->3] |=> spif)
          else if (icnt == 2'b11)
            (rfwe [->4] |=> spif)
          else
            (1'b1);
   endproperty
   a_interrupt_count_set: assert property(interrupt_count_set) else begin
      $error;
      -> tst_bench_top.ERROR;
   end    
`endif
   
   
endmodule

bind spi check_spi_top assert_spi_top_i1(.*);
