module assert_mips_sys(
                       input pause,   
                       input key1,
                       input key2,
                       
                       input clk,
                       input rst,
                       
                       input [6:0] seg7led1,
                       input [6:0] seg7led2,
                       
                       input [7:0]lcd_data,
                       input lcd_rs,
                       input lcd_rw,
                       input lcd_en,
                       input led1,
                       input led2,
                       
                       input [31:0] zz_din,
                       input [31:0] zz_ins_i,
                       input [31:0] zz_addr_o,
                       input [31:0] zz_dout,
                       input [31:0] zz_pc_o,
                       input [3:0] zz_wr_en_o,
                       
                       input ser_rxd,
                       input ser_txd,
                       input w_irq
                       );
   
   parameter MULT  = 24,
             MULTU = 25,
             DIV   = 26,
             DIVU  = 27;
   
   wire [5:0] inst_op,inst_func;
   assign inst_op   = zz_ins_i[31:26];
   assign inst_func = zz_ins_i[5:0];

   
   sequence INST_MUL;
      (inst_op==0) && (inst_func==MULT||inst_func==MULTU||inst_func==DIV||inst_func==DIVU);
   endsequence

   assume property (@(posedge clk) disable iff(!rst) INST_MUL |-> ~pause[*35]);
                                        
endmodule // assert_mips_sys
bind mips_sys assert_mips_sys chk_mips_sys(.*);
