`include "mips789_defs.v"

module assert_exec_stage(input pause,
                         input clk,
                         input rst,
                         input spc_cls_i,
                         input [4:0] alu_func,
                         input [2:0] dmem_fw_ctl,
                         input [31:0] ext_i,
                         input [31:0] fw_alu,
                         input [31:0] fw_dmem,
                         input [1:0] muxa_ctl_i,
                         input [2:0] muxa_fw_ctl,
                         input [1:0] muxb_ctl_i,
                         input [31:0] pc_i,
                         input [31:0] rs_i,
                         input [31:0] rt_i,
                         input [31:0] alu_ur_o,
                         input [31:0] dmem_data_ur_o,
                         input [31:0]  zz_spc_o,
                         input [31:0] BUS2332,
                         input [31:0] BUS2446,
                         input [31:0] BUS468,
                         input [31:0] BUS476
                                    );


   initial $display("%m is binded");

   property muxa_ctl(_ctrl, _out);
      disable iff(!rst) @(posedge clk) if(!$isunknown({BUS476,_out}))
        (muxa_ctl_i==_ctrl |-> (BUS476==_out));
   endproperty

   assert_muxa_pc: assert property(muxa_ctl(`MUXA_PC, BUS2332));
   assert_muxa_ext: assert property(muxa_ctl(`MUXA_EXT, ext_i));
   assert_muxa_spc: assert property(muxa_ctl(`MUXA_SPC, zz_spc_o));

   assert_muxa_rs: assert property(@(posedge clk) disable iff(!rst || $isunknown({BUS476,rs_i}) ) if(!$isunknown({BUS476,rs_i}))
                                   ((muxa_ctl_i==`MUXA_RS)&&(muxa_fw_ctl!=`FW_ALU)&&(muxa_fw_ctl!=`FW_MEM)
                                   |->
                                   (BUS476==rs_i)));
   assert_muxa_fw_alu: assert property(@(posedge clk) disable iff(!rst)
                                       (muxa_ctl_i==`MUXA_RS)&&(muxa_fw_ctl==`FW_ALU)
                                       |->
                                       (BUS476==fw_alu));
   assert_muxa_fw_mem: assert property(@(posedge clk) disable iff(!rst) if(!$isunknown({BUS476,fw_dmem}))
                                       ((muxa_ctl_i==`MUXA_RS)&&(muxa_fw_ctl==`FW_MEM)
                                       |->
                                       (BUS476==fw_dmem)));  
   assert_muxa_default: assert property (@(posedge clk) disable iff(!rst)
                                         (muxa_ctl_i!=`MUXA_RS)&&(muxa_ctl_i!=`MUXA_PC)&&(muxa_ctl_i!=`MUXA_EXT)&&(muxa_ctl_i!=`MUXA_SPC)
                                         |->
                                         BUS476==rs_i);
      
   assert_muxb_ext: assert property (@(posedge clk) disable iff(!rst) if(!$isunknown({BUS468,ext_i}))
                                     if (muxb_ctl_i==`MUXB_EXT && !$isunknown({BUS468,ext_i})) (BUS468==ext_i)
                                     else (BUS468==dmem_data_ur_o));
   


endmodule
                    
bind exec_stage assert_exec_stage chk_exec_stage(.*);
