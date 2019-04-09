
`timescale 10ns / 1ns
module AA_mips_top_tb;


//Internal signals declarations:
reg clk;
reg rst;
reg ser_rxd;
wire ser_txd;
wire [6:0]seg7led1;
wire [6:0]seg7led2;
wire [7:0]lcd_data;
wire lcd_rs;
wire lcd_rw;
wire lcd_en;
wire led1;
wire led2;
reg key1;
reg key2;

reg pause;

	mips_top mips789_tb (
        .pause(pause),
		.clk(clk),
		.rst(rst),
		.ser_rxd(ser_rxd),
		.ser_txd(ser_txd),
		.seg7led1(seg7led1),
		.seg7led2(seg7led2),
		.lcd_data(lcd_data),
		.lcd_rs(lcd_rs),
		.lcd_rw(lcd_rw),
		.lcd_en(lcd_en),
		.led1(led1),
		.led2(led2),
		.key1(key1),
		.key2(key2));

always #5 clk = ~clk;

initial
	begin
clk = 0; 
rst = 1;
key1= 0;
key2= 0;

pause = 1;
#10 pause = 0;
       
ser_rxd = 1;
#10 rst = 0;
#10 rst = 1;
#100000 key1=1;
#10000 key1=0;

#10000;
$display("%t: finished", $time);
$finish;
       
end

reg debug_clk;
initial debug_clk = 1;
always #10 debug_clk = ~debug_clk;
reg [6:0] prev_seg7led1;
reg [6:0] prev_seg7led2;
reg [7:0] prev_lcd_data;
reg  prev_lcd_rs;
reg  prev_lcd_rw;
reg  prev_lcd_en;
reg  prev_led1;
reg  prev_led2;
reg [31:0] prev_zz_addr_o;
reg [31:0] prev_zz_dout;
reg [31:0] prev_zz_pc_o;
reg [3:0] prev_zz_wr_en_o;
reg [31:0] prev_cop_addr;
reg [3:0] prev_cop_mem_ctl;
reg [31:0] prev_data2cop;
reg [31:0] prev_cop_data;
reg [31:0] prev_irq_addr;
reg  prev_w_irq;
always @(posedge debug_clk) begin
    if (
        mips789_tb.isys.seg7led1 != prev_seg7led1 ||
        mips789_tb.isys.seg7led2 != prev_seg7led2 ||
        mips789_tb.isys.lcd_data != prev_lcd_data ||
        mips789_tb.isys.lcd_rs != prev_lcd_rs ||
        mips789_tb.isys.lcd_rw != prev_lcd_rw ||
        mips789_tb.isys.lcd_en != prev_lcd_en ||
        mips789_tb.isys.led1 != prev_led1 ||
        mips789_tb.isys.led2 != prev_led2 ||
        mips789_tb.isys.zz_addr_o != prev_zz_addr_o ||
        mips789_tb.isys.zz_dout != prev_zz_dout ||
        mips789_tb.isys.zz_pc_o != prev_zz_pc_o ||
        mips789_tb.isys.zz_wr_en_o != prev_zz_wr_en_o ||
        mips789_tb.isys.cop_addr != prev_cop_addr ||
        mips789_tb.isys.cop_mem_ctl != prev_cop_mem_ctl ||
        mips789_tb.isys.data2cop != prev_data2cop ||
        mips789_tb.isys.cop_data != prev_cop_data ||
        mips789_tb.isys.irq_addr != prev_irq_addr ||
        mips789_tb.isys.w_irq != prev_w_irq )
        $display("Signals at %t",$time);
    if (mips789_tb.isys.seg7led1 != prev_seg7led1)
        $display("seg7led1[6:0] = %h",mips789_tb.isys.seg7led1);
    prev_seg7led1 <= mips789_tb.isys.seg7led1;
    if (mips789_tb.isys.seg7led2 != prev_seg7led2)
        $display("seg7led2[6:0] = %h",mips789_tb.isys.seg7led2);
    prev_seg7led2 <= mips789_tb.isys.seg7led2;
    if (mips789_tb.isys.lcd_data != prev_lcd_data)
        $display("lcd_data[7:0] = %h",mips789_tb.isys.lcd_data);
    prev_lcd_data <= mips789_tb.isys.lcd_data;
    if (mips789_tb.isys.lcd_rs != prev_lcd_rs)
        $display("lcd_rs = %h",mips789_tb.isys.lcd_rs);
    prev_lcd_rs <= mips789_tb.isys.lcd_rs;
    if (mips789_tb.isys.lcd_rw != prev_lcd_rw)
        $display("lcd_rw = %h",mips789_tb.isys.lcd_rw);
    prev_lcd_rw <= mips789_tb.isys.lcd_rw;
    if (mips789_tb.isys.lcd_en != prev_lcd_en)
        $display("lcd_en = %h",mips789_tb.isys.lcd_en);
    prev_lcd_en <= mips789_tb.isys.lcd_en;
    if (mips789_tb.isys.led1 != prev_led1)
        $display("led1 = %h",mips789_tb.isys.led1);
    prev_led1 <= mips789_tb.isys.led1;
    if (mips789_tb.isys.led2 != prev_led2)
        $display("led2 = %h",mips789_tb.isys.led2);
    prev_led2 <= mips789_tb.isys.led2;
    if (mips789_tb.isys.zz_addr_o != prev_zz_addr_o)
        $display("zz_addr_o[31:0] = %h",mips789_tb.isys.zz_addr_o);
    prev_zz_addr_o <= mips789_tb.isys.zz_addr_o;
    if (mips789_tb.isys.zz_dout != prev_zz_dout)
        $display("zz_dout[31:0] = %h",mips789_tb.isys.zz_dout);
    prev_zz_dout <= mips789_tb.isys.zz_dout;
    if (mips789_tb.isys.zz_pc_o != prev_zz_pc_o)
        $display("zz_pc_o[31:0] = %h",mips789_tb.isys.zz_pc_o);
    prev_zz_pc_o <= mips789_tb.isys.zz_pc_o;
    if (mips789_tb.isys.zz_wr_en_o != prev_zz_wr_en_o)
        $display("zz_wr_en_o[3:0] = %h",mips789_tb.isys.zz_wr_en_o);
    prev_zz_wr_en_o <= mips789_tb.isys.zz_wr_en_o;
    if (mips789_tb.isys.cop_addr != prev_cop_addr)
        $display("cop_addr[31:0] = %h",mips789_tb.isys.cop_addr);
    prev_cop_addr <= mips789_tb.isys.cop_addr;
    if (mips789_tb.isys.cop_mem_ctl != prev_cop_mem_ctl)
        $display("cop_mem_ctl[3:0] = %h",mips789_tb.isys.cop_mem_ctl);
    prev_cop_mem_ctl <= mips789_tb.isys.cop_mem_ctl;
    if (mips789_tb.isys.data2cop != prev_data2cop)
        $display("data2cop[31:0] = %h",mips789_tb.isys.data2cop);
    prev_data2cop <= mips789_tb.isys.data2cop;
    if (mips789_tb.isys.cop_data != prev_cop_data)
        $display("cop_data[31:0] = %h",mips789_tb.isys.cop_data);
    prev_cop_data <= mips789_tb.isys.cop_data;
    if (mips789_tb.isys.irq_addr != prev_irq_addr)
        $display("irq_addr[31:0] = %h",mips789_tb.isys.irq_addr);
    prev_irq_addr <= mips789_tb.isys.irq_addr;
    if (mips789_tb.isys.w_irq != prev_w_irq)
        $display("w_irq = %h",mips789_tb.isys.w_irq);
    prev_w_irq <= mips789_tb.isys.w_irq;
end

endmodule
