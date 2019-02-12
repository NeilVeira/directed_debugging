module check_pre_norm (input clk,
                       input [1:0] rmode, 
                       input add, 
                       input [31:0] opa, opb, 
                       input opa_nan, opb_nan,
                       input [26:0] fracta_out, fractb_out,
                       input [7:0] exp_dn_out,
                       input sign, nan_sign, result_zero_sign, fasu_op
                       );

`include "func.sv"

    function [1:0] opa_lt_opb;
        input [31:0] opa, opb;
        opa_lt_opb = (exponent(opa)>exponent(opb))? 2'b00: ((exponent(opa) < exponent(opb))? 2'b01: ((fraction(opa) > fraction(opb))? 2'b00 : ((fraction(opa) < fraction(opb))? 2'b01: 2'b10)));
    endfunction

    // fracta_out should be the fraction of the larger operand
    property larger_opa;
        @(posedge clk)
        valid_op(opa) && valid_op(opb) && (opa_lt_opb(opa, opb) == 2'b00) |=> fracta_out == {~dn_op($past(opa)), fraction($past(opa)), 3'b0};
    endproperty

    property larger_opb;
        @(posedge clk)
        valid_op(opa) && valid_op(opb) && (opa_lt_opb(opa, opb) == 2'b01) |=> fracta_out == {~dn_op($past(opb)), fraction($past(opb)), 3'b0};
    endproperty

    // exp_dn_out should be all zero if the the result of add/sub will be zero (e.g. the same number subtract)
    property zero_dn_out;
        @(posedge clk)
        !(opa[31] ^ opb[31] ^ add) && (exponent(opa) == exponent(opb)) && (fraction(opa) == fraction(opb)) |=> !(|exp_dn_out);
    endproperty

    // the truth table of the value of sign
    // opba[31] (opb[31]^add)  sign
    //   1           0          1
    //   1           1         opa>opb? 1:0
    //   0           0         opa>opb? 0:1
    //   0           1          0
    property pos_sign;
        @(posedge clk)
        valid_op(opa) && valid_op(opb) && ((!opa[31] && (add ^ opb[31])) || (!opa[31] && !(add ^ opb[31]) && (opa_lt_opb(opa, opb) == 2'b00)) || (opa[31] && (add ^ opb[31]) && (opa_lt_opb(opa, opb) == 2'b01))) |=> !sign;
    endproperty

    property neg_sign;
        @(posedge clk)
        valid_op(opa) && valid_op(opb) && ((opa[31] && !(add ^ opb[31])) || (!opa[31] && !(add ^ opb[31]) && (opa_lt_opb(opa, opb) == 2'b01)) || (opa[31] && (add ^ opb[31]) && (opa_lt_opb(opa, opb) == 2'b00))) |=> sign;
    endproperty
        
    a_check_larger_opa: assert property(larger_opa)
    else begin
        $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
`endif
    end
    a_check_larger_opb: assert property(larger_opb)
    else begin
        $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
`endif
    end
    a_check_zero_dn_out: assert property(zero_dn_out)
    else begin
        $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
`endif
    end
    a_check_pos_sign: assert property(pos_sign)
    else begin
        $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
`endif
    end
    a_check_neg_sign: assert property(neg_sign)
    else begin
        $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
`endif
    end

    // NOTE: In the simulation flow, the testbench causes both fracta_out
    //       and fractb_out be xxxx, which fires this assertion.
    // NOTE: 0in crashes when $isunknown is used outside the property
`ifdef VENNSA_DYNAMIC_SIMULATION      
    wire unknown_values=$isunknown(fracta_out) || $isunknown(fractb_out);
`else
    wire unknonw_values;
    assign unknown_values=0;
`endif
    // fracta_out should be always larger than fractb_out
    property sorted_fraction;
        disable iff(unknown_values)
        @(posedge clk)
        1'b1 |-> ##1 fracta_out >= fractb_out;
    endproperty

    a_check_sorted_fraction: assert property(sorted_fraction)
    else begin
        $error;
`ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
`endif
    end

endmodule                        

bind pre_norm check_pre_norm chk_pre_norm(.*);
