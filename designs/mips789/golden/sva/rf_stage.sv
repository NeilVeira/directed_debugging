`include "mips789_defs.v"

module assert_rf_stage(//ports
                       input pause,
                       input clk,
                       input irq_i,
                       input rst_i,
                       input wb_we_i,
                       input [2:0] cmp_ctl_i,
                       input [2:0] ext_ctl_i,
                       input [31:0] fw_alu_i,
                       input [2:0] fw_cmp_rs,
                       input [2:0] fw_cmp_rt,
                       input [31:0] fw_mem_i,
                       input [2:0] id_cmd,
                       input [31:0] ins_i,
                       input [31:0] irq_addr_i,
                       input [2:0] pc_gen_ctl,
                       input [31:0] pc_i,
                       input [1:0] rd_sel_i,
                       input [4:0] wb_addr_i,
                       input [31:0] wb_din_i,
                       input [31:0] zz_spc_i,
                       input iack_o,
                       input id2ra_ctl_clr_o,
                       input id2ra_ctl_cls_o,
                       input ra2ex_ctl_clr_o,
                       input [31:0] ext_o,
                       input [31:0] pc_next,
                       input [4:0] rd_index_o,
                       input [4:0] rs_n_o,
                       input [31:0] rs_o,
                       input [4:0] rt_n_o,
                       input [31:0] rt_o,

                       //wires
                       input NET6609,
                       input NET6658,
                       input NET7774,
                       input NET904,
                       
                       input [3:0] BUS1013,
                       input [31:0] BUS2085,
                       input [4:0] BUS3236,
                       input [4:0] BUS3237,
                       input [4:0] BUS5421,
                       input [31:0] BUS6061,
                       input [31:0] BUS6095,
                       
                       input [100:0] CLK_NO,
                       input [100:0] INS_NO
                       
                       );


   initial $display("%m is binded");


   cal_cpi_clk_count: assert property(@(posedge clk) disable iff(!rst_i) if(!$isunknown(CLK_NO)) (1'b1 |=> CLK_NO==($past(CLK_NO) + 1)));
   
   cal_cpi_ins_count: assert property(@(posedge clk) disable iff(!rst_i) if(!$isunknown(INS_NO)) ((NET7774==0) |=> INS_NO==($past(INS_NO) + 1)));

   ext_sign: assert property (@(posedge clk) disable iff(!rst_i) (ext_ctl_i==`EXT_SIGN) |-> ext_o=={{16{BUS2085[15]}}, BUS2085[15:0]});
   ext_zeroext: assert property (@(posedge clk) disable iff(!rst_i) ext_ctl_i==`EXT_UNSIGN |-> ext_o=={16'b0, BUS2085[15:0]});
   ext_jmp: assert property (@(posedge clk) disable iff(!rst_i) ext_ctl_i==`EXT_J |-> ext_o=={4'b0, BUS2085[25:0],2'b0});
   ext_branch: assert property (@(posedge clk) disable iff(!rst_i) ext_ctl_i==`EXT_B |-> ext_o=={{14{BUS2085[15]}}, BUS2085[15:0], 2'b0}); 
   ext_sl: assert property (@(posedge clk) disable iff(!rst_i) ext_ctl_i==`EXT_SA |-> ext_o=={27'b0, BUS2085[10:6]});
   ext_shift2high: assert property (@(posedge clk) disable iff(!rst_i) ext_ctl_i==`EXT_S2H |-> ext_o=={BUS2085[15:0],16'b0});

   property pc_ign_cmd(_ctrl, _next);
      @(posedge clk) disable iff(!rst_i)
        (BUS1013==`PC_IGN) && (pc_gen_ctl==_ctrl)
        |->
        (pc_next==_next);
   endproperty
   
   pc_ret: assert property (pc_ign_cmd(`PC_RET, zz_spc_i));
   pc_jump: assert property (pc_ign_cmd(`PC_J, {pc_i[31:28],ext_o[27:0]}));
   pc_jumpret: assert property (pc_ign_cmd(`PC_JR, rs_o));

   pc_branch_chk: assert property (@(posedge clk) disable iff(!rst_i) (BUS1013==`PC_IGN) && (pc_gen_ctl==`PC_BC) && (NET904) |-> (pc_next==(pc_i+ext_o)));
   pc_branch: assert property (@(posedge clk) disable iff(!rst_i) (BUS1013==`PC_IGN) && (pc_gen_ctl==`PC_BC) && (!NET904) |-> (pc_next==(pc_i+4)));
   pc_ign_default: assert property (@(posedge clk) disable iff(!rst_i) (BUS1013==`PC_IGN) && (pc_gen_ctl!=`PC_RET) && (pc_gen_ctl!=`PC_J) 
                                && (pc_gen_ctl!=`PC_JR) && (!NET904) |-> (pc_next==(pc_i+4)));

   //pc_ign: assert property (@(posedge clk) disable iff(!rst_i) if(BUS1013==`PC_IGN)
   //                         if(pc_gen_ctl==`PC_RET) (pc_next==zz_spc_i) else
   //                         if(pc_gen_ctl==`PC_J) (pc_next=={pc_i[31:28],ext_o[27:0]}) else
   //                         if(pc_gen_ctl==`PC_JR) (pc_next==rs_o) else
   //                         if(pc_gen_ctl==`PC_BC) (NET904) |-> (pc_next==(pc_i+ext_o)[32:0]) else
   //                         1'b1 |=> pc_next==(pc_i + 4));
   
   pc_kep: assert property (@(posedge clk) disable iff(!rst_i) (BUS1013==`PC_KEP) |-> (pc_next==pc_i));
   pc_irq: assert property (@(posedge clk) disable iff(!rst_i) (BUS1013==`PC_IRQ) |-> (pc_next==irq_addr_i));
   pc_default: assert property (@(posedge clk) disable iff(!rst_i) (BUS1013!=`PC_IGN)&&(BUS1013!=`PC_KEP)&&(BUS1013!=`PC_IRQ) |-> pc_next==0);
   

   
endmodule // assert_rf_stage

bind rf_stage assert_rf_stage chk_rf_stage(.*);
