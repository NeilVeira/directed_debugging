// Assumption for formal flow only
`ifndef VENNSA_DYNAMIC_SIMULATION

module assume_fpu(input clk, 
                  input [2:0] fpu_op
                  );

    op_assumption: assume property ( @(posedge clk) fpu_op[2] == 1'b0);
   
endmodule

bind fpu assume_fpu assume_fpu_inst(.*);

`endif
