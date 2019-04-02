module check_wb_slave(input clk_i, rst_i,
                      input stb_i, cyc_i, we_i, 
                      input ack_o, err_o,
                      input [3:0] sel_i,
                      input [1:0] dvi_odf,
                      input cursor1_res,
                      input cursor1_en,
                      input cursor0_res,
                      input cursor0_en,
                      input bl,csl,vsl,hsl,pc,
                      input [1:0] cd,vbl,
                      input cbsw,vbsw,cbsie,
                      input vbsie,hie,vie,ven,
                      input [31:0] ctrl,
                      input acc, acc32, clut_acc, reg_acc, reg_wacc,
                      input CLUT_ADR,
                      input [7:0] REG_ADR,
                      input [11:2] adr_i
                      );

   initial
     $display("assert_wb_slave binded");

   property slave_error;
      @(posedge clk_i) disable iff (rst_i)
        (cyc_i & stb_i) & (sel_i !== 4'hf) & (!err_o)
        |=>
        $rose(err_o)
        ;
   endproperty

   property ctrl_bus;
      @(posedge clk_i)
        disable iff(rst_i)
        //if(!$isunknown(ctrl))
	      ((dvi_odf == ctrl[29:28]) &&
	       (cursor1_res == ctrl[25]) &&
	       (cursor1_en  == ctrl[24]) &&
	       (cursor0_res == ctrl[23]) &&
	       (cursor0_en  == ctrl[20]) &&
	       (bl == ctrl[15]) &&
	       (csl == ctrl[14]) &&
	       (vsl == ctrl[13]) &&
	       (hsl == ctrl[12]) &&
	       (pc  == ctrl[11]) &&
	       (cd  == ctrl[10:9]) &&
	       (vbl == ctrl[8:7]) &&
	       (cbsw == ctrl[6]) &&
	       (vbsw == ctrl[5]) &&
	       (cbsie == ctrl[4]) &&
	       (vbsie == ctrl[3]) &&
	       (hie == ctrl[2]) &&
	       (vie == ctrl[1]) &&
	       (ven == ctrl[0]));
   endproperty

   property chk_adr_i_bus;
      @(posedge clk_i)
        disable iff(rst_i)
          if(!$isunknown({REG_ADR, CLUT_ADR}))
          (REG_ADR == adr_i[7:2]) && (CLUT_ADR == adr_i[11]);
   endproperty
   
   property chk_acc;
      @(posedge clk_i)
        //if(!$isunknown(acc))
          (cyc_i & stb_i)
          ==
          acc;
   endproperty

   property chk_acc32;
       @(posedge clk_i)
         disable iff(rst_i)
           if(!$isunknown(acc32))
           (sel_i == 4'hf)
           ==
           acc32;
   endproperty

   property chk_reg_wacc;
      @(posedge clk_i)
        disable iff(rst_i)
        //if(!$isunknown(reg_wacc))
          reg_wacc == (reg_acc & we_i);
   endproperty
   
   _slave_error: assert property(slave_error)else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end

   _ctrl_bus: assert property (ctrl_bus)else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      $display("%t: ctrl %b", $time, ctrl);
      -> test.ERROR;
`endif
   end

   _chk_adr_i_bus: assert property (chk_adr_i_bus)else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end
   
   _chk_acc: assert property (chk_acc)else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end

   _chk_acc32: assert property (chk_acc32)else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end
   
   _chk_reg_wacc: assert property (chk_reg_wacc)else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end


// Property for simulation flow only
`ifdef VENNSA_DYNAMIC_SIMULATION
   property slave_response;
      @(posedge clk_i) disable iff (rst_i)
        $rose(cyc_i && stb_i)
        |->
        $rose(ack_o ) within ($rose(cyc_i & stb_i) ##0 $fell(cyc_i)[->1])
        ;
   endproperty
   //assert the property
   _slave_response: assert property(slave_response)else begin
      $error;
      -> test.ERROR;
   end

`endif   

endmodule

bind vga_wb_slave check_wb_slave a_wb_slv(.*);
