module check_post_norm_simulation(input clk,
                                  input ovf0,
                                  input [22:0] fract_out_final, fract_out_rnd,
                                  input [1:0] exp_ovf,
                                  input output_zero, rmode_00, 
                                  input inf_out, f2i_max, max_num, 
                                  input [7:0] exp_out_rnd, exp_out_final,
                                  input g,r,s,exp_in_ff, exp_out_ff,
                                  input [7:0] exp_fix_div, 
                                  input [8:0] exp_next_mi,
                                  input [7:0] exp_out_rnd1, exp_out, exp_in,
                                  input op_mul, op_div, op_i2f, op_f2i,
                                  input [2:0] fpu_op);

   initial
     $display("assert_post_norm_simulation binded");

   wire [22:0] fract_out_final_golden = (inf_out | ovf0 | output_zero ) ? 23'h0 :
			   (max_num | (f2i_max & op_f2i) ) ? 23'h7fffff :
			   fract_out_rnd;

   wire [7:0] exp_out_final_golden = ((op_div & exp_ovf[1] & !exp_ovf[0]) | output_zero ) ? 8'h00 :
			   ((op_div & exp_ovf[1] &  exp_ovf[0] & rmode_00) | inf_out | (f2i_max & op_f2i) ) ? 8'hff :
			   max_num ? 8'hfe :
			   exp_out_rnd;

   wire [7:0] exp_out_rnd1_golden  = (g & r & s & exp_in_ff) ? (op_div ? exp_fix_div : exp_next_mi[7:0]) :
			(exp_out_ff & !op_f2i) ? exp_in : exp_out;

    // NOTE: In the simulation flow, the testbench causes both fracta_out
    //       and fractb_out be xxxx, which fires this assertion.
    // NOTE: 0in crashes when $isunknown is used outside the property
`ifdef VENNSA_DYNAMIC_SIMULATION                     
   wire check_fract_out_final_golden=$isunknown(fract_out_final_golden);
   wire check_exp_out_final_golden=$isunknown(exp_out_final_golden);
   wire check_exp_out_rnd1_golden=$isunknown(exp_out_rnd1_golden);
   wire check_op_bus=$isunknown({op_mul, op_div, op_i2f, op_f2i});
`else
   wire check_fract_out_final_golden;
   wire check_exp_out_final_golden;
   wire check_exp_out_rnd1_golden;
   wire check_op_bus;
   assign check_fract_out_final_golden=0;
   assign check_exp_out_final_golden=0;
   assign check_exp_out_rnd1_golden=0;
   assign check_op_bus=0;
`endif

   property chk_fract_out_final;
      @(posedge clk)
        disable iff(check_fract_out_final_golden)
          fract_out_final == fract_out_final_golden;
   endproperty
   
   property chk_exp_out_final;
      @(posedge clk)
        disable iff (check_exp_out_final_golden)
          exp_out_final == exp_out_final_golden;
   endproperty


   property chk_exp_out_rnd1;
      @(posedge clk)
        disable iff(check_exp_out_rnd1_golden)
          exp_out_rnd1 == exp_out_rnd1_golden;
   endproperty

   property chk_op;
      @(posedge clk)
        disable iff(check_op_bus)
          if(fpu_op[2:0] == 2)
            ({op_mul, op_div, op_i2f, op_f2i} == 4'b1000)
          else if (fpu_op[2:0] == 3)
            ({op_mul, op_div, op_i2f, op_f2i} == 4'b0100)          
          else if (fpu_op[2:0] == 4)
            ({op_mul, op_div, op_i2f, op_f2i} == 4'b0010)
          else if (fpu_op[2:0] == 5)
            ({op_mul, op_div, op_i2f, op_f2i} == 4'b0001)
          else
            1'b1;
   endproperty
   
   
   //assert the property
   a_fract_out_final: assert property(chk_fract_out_final) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end
   
   a_exp_out_final: assert property(chk_exp_out_final) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end
   
   a_exp_out_rnd1: assert property(chk_exp_out_rnd1) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end

   a_op: assert property(chk_op) else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
`endif
   end 
   
endmodule

bind post_norm check_post_norm_simulation chk_post_norm_simulation(.*);
