`timescale 1 ps / 1 ps

module sudoku_check_bench ();

reg clk,rst;

initial begin
   clk = 0; 
   rst = 0;
   #10 rst = 1;
   #10 rst = 0;
   #200000000 $finish; 
end

always begin
   #10000 clk = ~clk;
end

wire [9:0] correct;
wire [9:0] wrong;
wire [31:0] cycles;
wire [9*9*4-1:0] extra_out; 

sudoku_check st	(
  .clk(clk),
  .rst(rst),
  .num_correct(correct),
  .num_wrong(wrong),
  .cycles(cycles),
  .extra_out(extra_out)
);

always @(posedge clk) begin
	if (&correct || &wrong || &cycles) begin
		$display ("Num Correct: %d", correct);
		$display ("Num Wrong: %d", wrong);
		$display ("Num Cycles: %d", cycles);
        if (wrong > 0) begin 
            $display ("Error: wrong = %d", wrong);
        end 
        else begin 
            $display("Success!");
        end 
        $finish;
	end
end

reg debug_clk;
initial debug_clk = 1;
always #100 debug_clk = ~debug_clk;
reg [9:0] prev_num_correct;
reg [9:0] prev_num_wrong;
reg [31:0] prev_cycles;
reg [7:0] prev_show_index;
reg [7:0] prev_check_index;
reg [7:0] prev_index;
reg  prev_working;
reg [323:0] prev_puz_io;
reg  prev_oe;
reg  prev_next_p;
reg  prev_solution;
reg  prev_give_up;
reg  prev_match;
reg [323:0] prev_masked;
reg  prev_match_cooking;
reg [9*9*4-1:0] prev_extra_out; 
always @(posedge debug_clk) begin
    if (
        st.num_correct != prev_num_correct ||
        st.num_wrong != prev_num_wrong ||
        st.cycles != prev_cycles ||
        st.show_index != prev_show_index ||
        st.check_index != prev_check_index ||
        st.index != prev_index ||
        st.working != prev_working ||
        st.puz_io != prev_puz_io ||
        st.oe != prev_oe ||
        st.next_p != prev_next_p ||
        st.solution != prev_solution ||
        st.give_up != prev_give_up ||
        st.match != prev_match ||
        st.masked != prev_masked ||
        st.match_cooking != prev_match_cooking || 
        st.extra_out != prev_extra_out)
        $display("Signals at %t",$time);
    if (st.num_correct != prev_num_correct)
        $display("num_correct[9:0] = %h",st.num_correct);
    prev_num_correct <= st.num_correct;
    if (st.num_wrong != prev_num_wrong)
        $display("num_wrong[9:0] = %h",st.num_wrong);
    prev_num_wrong <= st.num_wrong;
    if (st.cycles != prev_cycles)
        $display("cycles[31:0] = %h",st.cycles);
    prev_cycles <= st.cycles;
    if (st.show_index != prev_show_index)
        $display("show_index[7:0] = %h",st.show_index);
    prev_show_index <= st.show_index;
    if (st.check_index != prev_check_index)
        $display("check_index[7:0] = %h",st.check_index);
    prev_check_index <= st.check_index;
    if (st.index != prev_index)
        $display("index[7:0] = %h",st.index);
    prev_index <= st.index;
    if (st.working != prev_working)
        $display("working = %h",st.working);
    prev_working <= st.working;
    if (st.puz_io != prev_puz_io)
        $display("puz_io[323:0] = %h",st.puz_io);
    prev_puz_io <= st.puz_io;
    if (st.oe != prev_oe)
        $display("oe = %h",st.oe);
    prev_oe <= st.oe;
    if (st.next_p != prev_next_p)
        $display("next_p = %h",st.next_p);
    prev_next_p <= st.next_p;
    if (st.solution != prev_solution)
        $display("solution = %h",st.solution);
    prev_solution <= st.solution;
    if (st.give_up != prev_give_up)
        $display("give_up = %h",st.give_up);
    prev_give_up <= st.give_up;
    if (st.match != prev_match)
        $display("match = %h",st.match);
    prev_match <= st.match;
    if (st.masked != prev_masked)
        $display("masked[323:0] = %h",st.masked);
    prev_masked <= st.masked;
    if (st.match_cooking != prev_match_cooking)
        $display("match_cooking = %h",st.match_cooking);
    prev_match_cooking <= st.match_cooking;
    if (st.extra_out != prev_extra_out)
        $display("extra_out = %h",st.extra_out);
    prev_exra_out <= st.extra_out; 
end

endmodule
