`timescale 1 ps / 1 ps

module sudoku_check_bench ();

reg clk,rst;

initial begin
   clk = 0; 
   rst = 0;
   #10 rst = 1;
   #10 rst = 0;
end

always begin
   #10000 clk = ~clk;
end

wire [9:0] correct;
wire [9:0] wrong;
wire [31:0] cycles;

sudoku_check st	(.clk(clk),.rst(rst),
	 .num_correct(correct),.num_wrong(wrong),.cycles(cycles));

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

endmodule
