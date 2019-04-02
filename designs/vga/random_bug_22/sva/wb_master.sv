module check_vga_master(input clk_i, sclr,
                        input busy, vmem_acc, cur_acc,
                        input burst_done, vmem_ack,
                        input ImDone, ld_cursor0, ld_cursor1, cur_done,
                        input vmem_req);

   initial
     $display("assert_vga_master binded");


   property chk_busy;
      @(posedge clk_i)
        if(!$isunknown(busy))
          (vmem_acc | cur_acc)
          ==
          busy;
   endproperty

   property chk_vmem_acc;
      @(posedge clk_i)
        if (!sclr)
          (1'b1
           |=>
           vmem_acc
           ==
           (($past(vmem_req) | ($past(vmem_acc) & !($past(burst_done) & $past(vmem_ack)))) & !$past(ImDone) & !$past(cur_acc)));
   endproperty

   //assert property
   _a_chk_busy: assert property (chk_busy) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end

   _a_chk_vmem_acc: assert property (chk_vmem_acc) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end
   
// Property of simulation flow only
`ifdef VENNSA_DYNAMIC_SIMULATION
   property chk_cur_acc;
      @(posedge clk_i) 
        if (!sclr)
          (1'b1 
           |=> 
           cur_acc 
           ==
           ($past(cur_acc) | $past(ImDone) & ($past(ld_cursor0) | $past(ld_cursor1))) & !$past(cur_done));
   endproperty

   //assert property
   // 0in cannot prove this assertion in short time. Use it for simulation flow only then
   _a_chk_cur_acc: assert property (chk_cur_acc) else begin
      $error;
      $display("%t %b %b %b", $time,sclr, cur_acc,$past(ImDone) & ($past(ld_cursor0) | $past(ld_cursor1)) & !$past(cur_done));
      -> test.ERROR;
   end   

`endif
   
endmodule

bind vga_wb_master check_vga_master chk_vga_master(.*);
