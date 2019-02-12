module sudoku_check (clk,rst,num_correct,num_wrong,cycles, extra_out);

input clk,rst;

output [9:0] num_correct;
output [9:0] num_wrong;
output [31:0] cycles;
output [9*9*4-1:0] extra_out; 

reg [9:0] num_correct;
reg [9:0] num_wrong;
reg [31:0] cycles;

reg [7:0] show_index;
reg [7:0] check_index;
wire [7:0] index;

reg working;

tri [323:0] puz_io;
wire oe,next_p,solution,give_up;
wire match;
wire [323:0] masked;

puz_bank3 p (.clk(clk),.index(index[7:0]),.masked(masked),.to_check(puz_io),.match(match));

sudoku s (
	.clk(clk),.rst(rst),
	.puzzle_io(puz_io),
	.puzzle_oe(oe),
	.next_puzzle(next_p),
	.solution(solution),
	.give_up(give_up),
	.extra_out(extra_out)
);

assign index = (oe ? check_index : show_index);
assign puz_io = (oe ? 324'bz : masked);
reg match_cooking;

always @(posedge clk or posedge rst) begin
	if (rst) begin
		num_correct <= 0;
		num_wrong <= 0;
		cycles <= 0;
		working <= 0;
		show_index <= 0;
		check_index <= 0;
		match_cooking <= 0;
	end
	else begin
		if (next_p)	show_index <= show_index + 1;
		if (solution || give_up) check_index <= check_index + 1;
		if (solution) match_cooking <= 1'b1;
		else match_cooking <= 1'b0;
		if (next_p || solution) working <= 1;
		if (working) cycles <= cycles + 1;

		if (match_cooking) begin
			if (match) num_correct <= num_correct + 1;
			else num_wrong <= num_wrong + 1;
		end
	end
end

endmodule

