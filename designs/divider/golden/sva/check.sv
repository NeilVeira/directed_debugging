module check_divider(clk, ena, z, d, q, s, div0, ovf);

    parameter z_width = 16;
    parameter d_width = z_width /2;
    parameter pipe_width = d_width+3;

    input clk, ena;
    input [z_width-1:0] z;
    input [d_width-1:0] d;
    input [d_width:0] q, s;
    input div0, ovf;

    initial begin
        $display("Checker is loaded\n");
    end

    // quotient * divisor + remainder should equal to the divident
    // Note: 0in will timeout on this property on the good case.
//    property reverse_check;
//        reg [z_width-1:0] past_z;
//        reg [d_width-1:0] past_d;
//        @(posedge clk)
//            disable iff(!ena)
//            (!$isunknown(z) && !$isunknown(d) && !isOverflow(z, d), past_z = z, past_d = d) |-> 
//            ##pipe_width (getDivident(past_d, q, s, past_z));
//    endproperty

    property reverse_check;
        @(posedge clk)
            disable iff(!ena)
            (!$isunknown(z) && !$isunknown(d) && !isOverflow(z, d)) |-> 
            ##pipe_width (getDivident($past(d, pipe_width), q, s, 
            $past(z, pipe_width)));
    endproperty

    // the sign of the divident should be the same as the sign of the quotient
//    property sign_quotient;
//        reg sign;
//        @(posedge clk)
//            disable iff(!ena)
//            (|d, sign = z[z_width-1]) |-> ##pipe_width ( !(|q) || 
//            sign == q[d_width]);
//    endproperty

    property sign_quotient;
        @(posedge clk)
            disable iff(!ena)
            (|d) |-> ##pipe_width ( !(|q) || 
            $past(z[z_width-1], pipe_width) == q[d_width]);
    endproperty

//    property sign_remainder;
//        reg sign;
//        @(posedge clk)
//            disable iff(!ena)
//            (|d, sign = z[z_width-1])|-> ##pipe_width ( !(|s) || 
//            sign == s[d_width]);
//    endproperty

    property sign_remainder;
        @(posedge clk)
            disable iff(!ena)
            (|d)|-> ##pipe_width ( !(|s) || 
            $past(z[z_width-1], pipe_width) == s[d_width]);
    endproperty

    // div0 should be assert when d is zero
//    property div_0;
//        reg zero;
//        @(posedge clk)
//        disable iff(!ena)
//        if (!$isunknown(d))
//            (1'b1, zero = !(|d)) |-> ##pipe_width (div0 == zero);
//    endproperty

    property div_0;
        @(posedge clk)
        disable iff(!ena)
        if (!$isunknown(d))
            (1'b1 |-> ##pipe_width (div0 == ($past(d, pipe_width) == {d_width{1'b0}})));
    endproperty

    // ovf should be assert when the result is overflow
//    property overflow;
//        reg isOver;
//        @(posedge clk)
//        disable iff(!ena)
//        (!$isunknown(z) && !$isunknown(d), isOver = (z[z_width-1]?isOverflow(~z+1, d):isOverflow(z, d))) 
//        |-> ##pipe_width (isOver == ovf);
//    endproperty

    property overflow;
        @(posedge clk)
        disable iff(!ena)
        (!$isunknown(z) && !$isunknown(d) && 
        (z[z_width-1]?isOverflow(~z+1, d):isOverflow(z, d))) 
        |-> ##pipe_width ovf;
    endproperty

    // calculate and return the divident by reverse engineering (z = d * q + s)
    function [0:0] getDivident;
        input [d_width-1:0] d;
        input [d_width:0] q;
        input [d_width:0] s;
        input [z_width-1:0] z;


        if(!z[z_width-1]) begin  // z is positive
            getDivident = (z == q * d + s);
        end
        else begin
            if (~|q) begin // q is zero
                getDivident = ((~z+16'b1) == ({8'b0, d} + (~{7'hFF, s} + 16'b1)));
            end
            else begin
                if (~|s) begin // s is zero
                    getDivident = ((~z+16'b1) == ({8'b0, d} * (~{7'hFF, q} + 16'b1)));
                end
                else begin
                    getDivident = ((~z+16'b1) == ({8'b0, d} * (~{7'hFF, q} + 16'b1) + (~{7'hFF, s} + 16'b1)));
                end
            end
        end

    endfunction

    // calculate and return if z can cause the result overflow
    function [0:0] isOverflow;
        input [z_width-1:0] z;
        input [d_width-1:0] d;

        isOverflow = !(z[z_width-1:d_width] < d);
    endfunction

    // Note: for golden, this assertion will timeout.
    check_result: assert property(reverse_check) else begin
        $error("check_result fails @ ", $time);
`ifdef VENNSA_DYNAMIC_SIMULATION              
        -> bench_div_top.ERROR;
`endif
    end

    check_quotient_sign: assert property(sign_quotient) else begin
        $error("check_sign fails @ ", $time);
`ifdef VENNSA_DYNAMIC_SIMULATION              
        -> bench_div_top.ERROR;
`endif
    end

    check_remainder_sign: assert property(sign_remainder) else begin
        $error("check_sign fails @ ", $time);
`ifdef VENNSA_DYNAMIC_SIMULATION              
        -> bench_div_top.ERROR;
`endif
    end

    check_zero: assert property(div_0) else begin
        $error("check_zero fails @ ", $time);
`ifdef VENNSA_DYNAMIC_SIMULATION              
        -> bench_div_top.ERROR;
`endif
    end

    check_overflow: assert property(overflow) else begin
        $error("check_overflow fails @ ", $time);
`ifdef VENNSA_DYNAMIC_SIMULATION              
        -> bench_div_top.ERROR;
`endif
    end

endmodule

bind divider check_divider check1 (.*);
