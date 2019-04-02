wire		int_golden;
wire	[31:0]	wb_addr_o_golden;
wire	[31:0]	wb_data_o_golden;
wire	[3:0]	wb_sel_o_golden;
wire		wb_we_o_golden;
wire		wb_stb_o_golden;
wire		wb_cyc_o_golden;
wire	[2:0]	wb_cti_o_golden;
wire	[1:0]	wb_bte_o_golden;
wire		wb_ack_o_golden;
wire		wb_rty_o_golden;
wire		wb_err_o_golden;
wire    	hsync_golden;
wire		vsync_golden;
wire		csync_golden;
wire		blanc_golden;
wire	[7:0]	red_golden;
wire	[7:0]	green_golden;
wire	[7:0]	blue_golden;

vga_enh_top_golden #(1'b0, LINE_FIFO_AWIDTH) 
  golden (
		  .wb_clk_i     ( signal_DebuggerClk     ),
		  .wb_rst_i     ( 1'b0            ),
		  .rst_i        ( rst             ),
		  .wb_inta_o    ( int_golden      ),
          
		  //-- slave signals
		  .wbs_adr_i    ( wb_addr_i[11:0] ),
		  .wbs_dat_i    ( wb_data_i       ),
		  .wbs_dat_o    ( wb_data_o_golden),
		  .wbs_sel_i    ( wb_sel_i        ),
		  .wbs_we_i     ( wb_we_i         ),
		  .wbs_stb_i    ( wb_stb_i        ),
		  .wbs_cyc_i    ( wb_cyc_i        ),
		  .wbs_ack_o    ( wb_ack_o_golden ),
		  .wbs_rty_o    ( wb_rty_o_golden ),
		  .wbs_err_o    ( wb_err_o_golden ),

		  //-- master signals
		  .wbm_adr_o    ( wb_addr_o_golden[31:0] ),
		  .wbm_dat_i    ( wbm_data_i      ),
		  .wbm_sel_o    ( wb_sel_o_golden ),
		  .wbm_we_o     ( wb_we_o_golden  ),
		  .wbm_stb_o    ( wb_stb_o_golden ),
		  .wbm_cyc_o    ( wb_cyc_o_golden ),
		  .wbm_cti_o    ( wb_cti_o_golden ),
		  .wbm_bte_o    ( wb_bte_o_golden ),
		  .wbm_ack_i    ( wb_ack_i        ),
		  .wbm_err_i    ( wb_err_i        ),
          
		  //-- VGA signals
		  .clk_p_i      ( pclk_i          ),
          
          
          .hsync_pad_o  ( hsync_golden    ),
		  .vsync_pad_o  ( vsync_golden    ),
		  .csync_pad_o  ( csync_golden    ),
		  .blank_pad_o  ( blanc_golden    ),
		  .r_pad_o      ( red_golden      ),
		  .g_pad_o      ( green_golden    ),
		  .b_pad_o      ( blue_golden     )
		  
       	  );


always@(posedge signal_DebuggerClk) begin
   if(signal_DebuggerBegin) begin
	  if(VERBOSE)
	    $display("INFO: At time: %t, golden=%h %h %b, actual=%h %h %b", 
	             $time, 
	             {wb_data_o_golden, wb_addr_o_golden},
	             {hsync_golden, vsync_golden, csync_golden, blanc_golden},
	             {red_golden, green_golden, blue_golden}, 
	             {wb_data_o, wb_addr_o},
	             {hsync, vsync, csync, blanc},
	             {red, green, blue}
	             );
      
	  if(^{red_golden,green_golden,blue_golden} !== 1'bx) begin
	     
	     if( {red_golden,green_golden,blue_golden} != {red, green, blue})
	       begin
	          $display("At time %t: ERROR in RBG: golden=%h, actual=%h",
			           $time,
			           {red_golden, green_golden, blue_golden},
			           {red, green, blue}
			           );
              
	          -> ERROR;
              
	       end
	  end
	  
      if(^{wb_data_o_golden, wb_addr_o_golden} !== 1'bx)
        if({wb_data_o_golden, wb_addr_o_golden} != {wb_data_o, wb_addr_o})
	      begin
	         $display("At time %t: ERROR in wishbone: golden=%h, actual=%h",
			        $time,
			          {wb_data_o_golden, wb_addr_o_golden},
			          {wb_data_o, wb_addr_o}
			          );
	         -> ERROR;
	      end

      if(^{hsync_golden, vsync_golden, csync_golden, blanc_golden} !==1'bx)
	    if({hsync_golden, vsync_golden, csync_golden, blanc_golden} !=
	       {hsync, vsync, csync, blanc})
	      begin
	       $display("At time %t: ERROR in sync: golden=%h, actual=%h",
			        $time,
			        {hsync_golden, vsync_golden, csync_golden, blanc_golden},
			        {hsync, vsync, csync, blanc}
			        );
	         ->ERROR;
             
	    end
      
   end 
end // always@ (posedge signal_DebuggerClk)
