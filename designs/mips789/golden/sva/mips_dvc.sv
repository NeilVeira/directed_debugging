`include "mips789_defs.v"

module assert_mips_dvc(input [31:0] din,
                       input clk,
                       input rst,
                       input [31:0] addr,
                       input [3:0] mem_ctl,
                       
                       input [31:0] dout ,
                       
                       input [7:0] lcd_data,
                       input lcd_rs,
                       input lcd_rw,
                       input lcd_en,
                       
                       input led1,
                       input led2,
                       input key1,
                       input key2 ,
                       
                       input [31:0] irq_addr_o,
                       input irq_req_o,

                       input [31:0] key1_addr,
                       input [31:0] key2_addr,

                       input key1_req_do, key2_req_do, tmr_req_do
                       
                       );

   initial $display("%m is binded");


   
   assert_key1_req: assert property(@(posedge clk) disable iff(!rst) key1 ##1 ((addr==`CMD_ADDR) && (mem_ctl==`DMEM_SW) && din[30]) |=> key1_req_do);
   assert_key2_req: assert property(@(posedge clk) disable iff(!rst) key2 ##1 ((addr==`CMD_ADDR) && (mem_ctl==`DMEM_SW) && din[29]) |=> key2_req_do);

   assert_key1_addr: assert property(@(posedge clk) disable iff(!rst) (mem_ctl==`DMEM_SW) && (addr==`KEY1_IRQ_ADDR) |=> (key1_addr == $past(din)));
   assert_key2_addr: assert property(@(posedge clk) disable iff(!rst) (mem_ctl==`DMEM_SW) && (addr==`KEY2_IRQ_ADDR) |=> (key2_addr == $past(din)));

   assert_irq_req: assert property(@(posedge clk) disable iff(!rst) ((addr==`CMD_ADDR) && (mem_ctl==`DMEM_SW) && din[0]) ##1 (key1_req_do | key2_req_do) |=> irq_req_o);
   assert_irq1_addr: assert property(@(posedge clk) disable iff(!rst) (key1_req_do && !tmr_req_do) |=> (irq_addr_o == $past(key1_addr)));
   assert_irq2_addr: assert property(@(posedge clk) disable iff(!rst) (key2_req_do && !key1_req_do && !tmr_req_do) |=> (irq_addr_o == $past(key2_addr)));
   
   assert_lcd_data: assert property(@(posedge clk) disable iff(!rst) (addr==`LCD_DATA_ADDR) && (mem_ctl==`DMEM_SB) |=> (lcd_data==$past(din[7:0])));
   assert_lcd_cmd: assert property(@(posedge clk) disable iff(!rst) (addr==`CMD_ADDR) && (mem_ctl==`DMEM_SW) |=> {led2, led1, lcd_en, lcd_rw, lcd_rs}==$past(din[6:2]));

   assert_status_out: assert property(@(posedge clk) disable iff (!rst) (addr==`STATUS_ADDR) && (mem_ctl==`DMEM_LW) |=> dout[1:0]=={$past(key1,3), $past(key2,3)});
   assert_cmd_out: assert property(@(posedge clk) disable iff (!rst) ((addr==`CMD_ADDR) && (mem_ctl==`DMEM_SW)) ##1 ((addr==`CMD_ADDR) && (mem_ctl==`DMEM_LW)) |=> dout==$past(din,2));


endmodule // assert_mips_dvc

bind mips_dvc assert_mips_dvc chk_mips_dvc(.*);
