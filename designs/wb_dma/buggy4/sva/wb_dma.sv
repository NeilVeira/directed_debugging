`include "wb_dma_defines.v"

module wb_dma_checker(input clk, pause_req, de_start, use_ed, ptr_valid, rst, input [31:0] csr, input [10:0] state );

   parameter	[10:0]	// synopsys enum state
		IDLE		= 11'b000_0000_0001,
		READ		= 11'b000_0000_0010,
		WRITE		= 11'b000_0000_0100,
		UPDATE		= 11'b000_0000_1000,
		LD_DESC1	= 11'b000_0001_0000,
		LD_DESC2	= 11'b000_0010_0000,
		LD_DESC3	= 11'b000_0100_0000,
		LD_DESC4	= 11'b000_1000_0000,
		LD_DESC5	= 11'b001_0000_0000,
		WB		= 11'b010_0000_0000,
		PAUSE		= 11'b100_0000_0000;

   assume property(@(posedge clk)  pause_req |-> ##[0:10] ~pause_req );
   //assume property(@(posedge clk)  ~pause_req |-> ##[0:10] pause_req );
   //assume property( @(posedge clk) ~pause_req);
   
   assume property(@(posedge clk) de_start |-> !use_ed || ptr_valid);
     
   wire myrst = !rst;
   a_state: assert property( @(posedge clk)  
                    disable iff(myrst) 
                    (state == IDLE) && de_start && !csr[`WDMA_ERR]
                    |=> ##[0:20]   (state == READ) );
   
     

endmodule // wb_dma_checker

//bind wb_dma wb_dma_checker checker(.*);
bind wb_dma_de wb_dma_checker ch1(.*);

module wb_dma_ch_sel_checker( input clk, dma_busy, input [4:0] ch_sel, ch_sel_d, ch_sel_r);

   a_ch_sel: assert property( @(posedge clk) if(!$isunknown({ch_sel_d,ch_sel_r}))
                    if (dma_busy) (ch_sel == ch_sel_d)
                    else
                    ch_sel == ch_sel_r );
   
   
endmodule // wb_dma_ch_sel

bind wb_dma_ch_sel wb_dma_ch_sel_checker ch2(.*);
