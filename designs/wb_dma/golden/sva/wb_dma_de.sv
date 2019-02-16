module assert_wb_dma_de(input clk, rst,
                        input de_start,	// Start DMA Engine Indicator
						input nd,		// Next Descriptor Indicator
						input [31:0]	csr,		// Selected Channel CSR
						input [31:0]	pointer,	// Linked List Descriptor pointer
						input [31:0]	pointer_s,	// Previous Pointer
						input [31:0]	txsz,		// Selected Channel Transfer Size
						input [31:0]	adr0, adr1,	// Selected Channel Addresses
						input [31:0]	am0, am1,	// Selected Channel Address Masks
                        input [10:0] state,
                        input pause_req, paused, done,
                        input dma_abort, dma_abort_r,
                        input read, write, rd_ack, wr_ack,
                        input dma_done_d, de_txsz_we, de_adr0_we, de_adr1_we,
                        input mast0_drdy, mast0_go, m0_go,
                        input read_hold, write_hold,
                        input [31:0] mast0_dout                        
                        );

   parameter [10:0]           // synopsys enum state
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

   initial $display("%m binded");

   property pause_state;
      @(posedge clk) disable iff(!rst)
        (state == IDLE && pause_req)
        |->
        ~paused ##1 ((paused && (state==PAUSE)) throughout $fell(pause_req)[->1]);
   endproperty

   property abort_state;
      @(posedge clk) disable iff(!rst)
        ((state == READ || state == WRITE) && $past(dma_abort))
        |=>
        ##1 (state == WB || state == IDLE);
   endproperty

   property read_state;
      @(posedge clk) disable iff(!rst)
        (!dma_abort_r && state == READ && !rd_ack)
        |->
        read throughout (!rd_ack ##0 $rose(rd_ack)[->1]);   
   endproperty

   property write_state;
      @(posedge clk) disable iff(!rst)
        (!dma_abort_r && state == WRITE && !wr_ack)
        |->
        write throughout (!wr_ack ##0 $rose(wr_ack)[->1]);   
   endproperty

   property read_next;
      @(posedge clk) disable iff(!rst)
        (!dma_abort_r && state == WRITE && wr_ack && !done)
        |->
        read;
   endproperty

   property write_done;
      @(posedge clk) disable iff(!rst)
        (!dma_abort_r && state == WRITE && wr_ack && done)
        |=>
        (dma_done_d && de_txsz_we && de_adr0_we && de_adr1_we);
   endproperty

   property load_desc;
      @(posedge clk) disable iff(!rst)
        (state == LD_DESC1) ##0 (mast0_drdy)[->4]
        |=>
        ##1 (state == READ);
   endproperty
  
   // Assertions
   a_pause_state: assert property(pause_state);
   a_abort_state: assert property(abort_state);
   a_read_next:   assert property(read_next);
   a_write_done:  assert property(write_done);
   a_load_desc:   assert property(load_desc);
   
   a_mast0_go: assert property(@(posedge clk) disable iff(!rst)
                               (state==WB && !mast0_drdy)
                               |->
                               mast0_go);
   
endmodule

bind wb_dma_de assert_wb_dma_de check_wb_dma_de(.*);
