`include "mips789_defs.v"

module assert_mips_core (
                         input pause,
                         input clk,
                         input irq_i,
                         input rst,
                         input [31:0] cop_dout,
                         input [31:0] irq_addr,
                         input [31:0] zz_din,
                         input [31:0] zz_ins_i,
                         input [31:0] zz_addr_o,
                         input [31:0] zz_dout,
                         input [31:0] zz_pc_o,
                         input [3:0] zz_wr_en_o,
                         input iack_o,
                         input [31:0] cop_addr_o,
                         input [31:0] cop_data_o,
                         input [3:0] cop_mem_ctl_o
                         );

   initial $display("%m is binded");
   parameter SYSCALL  = 6'b001100;
   
   wire [5:0] inst_op,inst_func;
   assign inst_op   = zz_ins_i[31:26];
   assign inst_func = zz_ins_i[5:0];


   inst_SYSCALL: assert property (@(posedge clk) disable iff(!rst)
                                 $rose(rst) ##0 ((inst_op==0 && inst_func==6'b001100)[*2])
                                 |=> 
                                 zz_pc_o == ($past(zz_pc_o)+4));

   inst_NOOP: assert property (@(posedge clk) disable iff(!rst)
                               $rose(rst) ##0 (zz_ins_i == 0)[*2]
                               |=>
                               zz_pc_o == ($past(zz_pc_o)+4));
   
endmodule // mips_core

bind mips_core assert_mips_core check_mips_core(.*);

