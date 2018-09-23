module spi_top_assumption(input clk_i, rst_i, ena,
                          input [1:0] icnt, state, tcnt,
                          input spif, spe, wfempty, wfre, rfwe,
                          input [7:0] treg, wfdout,
                          input [2:0] bcnt,
                          input miso_i,
                          input [1:0] adr_i,
                          input [7:0] dat_o, spcr, spsr, rfdout, sper,
                          input [3:0] espr
                          );
   
   espr_assume : assume property (@(posedge clk_i) (espr[3:2] != 2'b11));
   
endmodule
bind spi spi_top_assumption spi_top_assumption_inst(.*);


module fifo4_assumption(input clk, rst, clr,
                        input [1:0] wp, rp,
                        input gb, empty, full, re, we
                        );
   
   no_read_empty: assume property (disable iff(!rst) @(posedge clk) (empty |-> !re));
   no_read_write: assume property (disable iff(!rst) @(posedge clk) ( (re |-> !we) and (we |-> !re)));
   
`ifndef VENNSA_DYNAMIC_SIMULATION
   no_write_full: assume property (disable iff(!rst) @(posedge clk) (full |-> !we));
`endif
   
endmodule
bind fifo4 fifo4_assumption fifo4_assumption_inst(.*);
