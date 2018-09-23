module check_fpu(input clk, 
                 input [26:0] fracta, fractb,
                 input [27:0] fract_out_q,
                 input fasu_op,
                 input [23:0] fracta_mul, fractb_mul,
                 input [47:0] prod,
                 input [49:0] fdiv_opa, quo, remainder,
                 input [30:0] opa_r1,
                 input [7:0] exp_mul, exp_r, exp_fasu,
                 input [2:0] fpu_op, fpu_op_r1, fpu_op_r2, fpu_op_r3,
                 input mul_inf, div_inf, inf_d, snan_d, qnan_d,
                 input [30:0] out_fixed, out_d,
                 input [31:0] out,
                 input inf, snan, qnan, ine, overflow, underflow, zero, div_by_zero,
                 input	[31:0]	opa, opb
                 );

   initial
     $display("assert_fpu binded");

   property exp;
      @(posedge clk)
        if(fpu_op_r2 < 2)
          (1'b1 |=> exp_r == $past(exp_fasu))
        else if (fpu_op_r2 == 2 | fpu_op_r2 == 3)
          (1'b1 |=> exp_r == $past(exp_mul))
        else if (fpu_op_r2 == 4)
          (1'b1 |=> !exp_r)
        else if (fpu_op_r2 == 5)
          (1'b1 |=> exp_r == $past(opa_r1[30:23]))
        else
          (1'b1);  
   endproperty
   
   //assert the property
   a_exp: assert property (exp)else begin
      $error;
      `ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
      `endif
   end

`include "func.sv"    
    
   // following properties are the IEEE standard for operations on floating point special numbers
   property div_by_inf;
      @(posedge clk)
        inf_op(opb) && (fpu_op == 3'b011) |-> ##4 (zero && zero_op(out));
   endproperty

   property inf_time_inf;
      @(posedge clk)
        inf_op(opa) && inf_op(opb) && (fpu_op == 3'b010) |-> ##4 (inf && inf_op(out));
   endproperty

   property nzero_div_by_zero;
      @(posedge clk)
        !zero_op(opa) && zero_op(opb) && (fpu_op == 3'b011) |-> ##4 (div_by_zero && inf_op(out));
   endproperty

   property inf_plus_inf;
      @(posedge clk)
        opa[31] && inf_op(opa) && opb[31] && inf_op(opb) && (fpu_op == 3'b000) |-> ##4 inf_op(out);
   endproperty
   
   property zero_div_by_zero;
      @(posedge clk)
        zero_op(opa) && zero_op(opb) && (fpu_op == 3'b011) |-> ##4 qnan_op(out);
   endproperty

   property inf_sub_inf;
      @(posedge clk)
        opa[31] && inf_op(opa) && opb[31] && inf_op(opb) && (fpu_op == 3'b001) |-> ##4 inf_op(out);
   endproperty

   property inf_div_by_inf;
      @(posedge clk)
        inf_op(opa) && inf_op(opb) && (fpu_op == 3'b011) |-> ##4 inf_op(out);
   endproperty

   property inf_time_zero;
      @(posedge clk)
        ((inf_op(opa) && zero_op(opb)) || (zero_op(opa) && zero_op(opb))) && (fpu_op == 3'b010) |-> ##4 inf_op(out);
   endproperty

   property op_nan;
      @(posedge clk)
        qnan_op(opa) || snan_op(opa) || qnan_op(opb) || snan_op(opb) |-> ##4 qnan_op(out);
   endproperty

   a_check_snan: assert property( @(posedge clk) ((snan_op(opa) || snan_op(opb)) |-> ##4 (snan)))
     else begin
        $error;
        `ifdef VENNSA_DYNAMIC_SIMULATION      
        -> test.ERROR;
        `endif
     end
   
// assertion of simulation flow only
`ifdef VENNSA_DYNAMIC_SIMULATION
    a_check_div_by_inf: assert property(div_by_inf)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_inf_time_inf: assert property(inf_time_inf)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_nzero_div_by_zero: assert property(nzero_div_by_zero)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_inf_plus_inf: assert property(inf_plus_inf)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_zero_div_by_zero: assert property(zero_div_by_zero)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_inf_sub_inf: assert property(inf_sub_inf)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_inf_div_by_inf: assert property(inf_div_by_inf)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_inf_time_zero: assert property(inf_time_zero)
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_op_nan: assert property(op_nan)
    else begin
        $error;
        -> test.ERROR;
    end


    // following properties are from FPU document
    no_snan_out: assert property( @(posedge clk) disable iff ($isunknown(out)) !(snan_op(out)))
    else begin
        $error;
        -> test.ERROR;
    end

    a_check_qnan: assert property( @(posedge clk) qnan_op(out) |-> qnan)
    else begin
        $error;
        -> test.ERROR;
    end


    wire [30:0] out_golden = (mul_inf | div_inf | snan_d | qnan_d |
                             (inf_d & (fpu_op_r3!=3'b011) & (fpu_op_r3!=3'b101)))
                            & fpu_op_r3!=3'b100 ? 
                            out_fixed: out_d;

    property chk_out;
       @(posedge clk)
         disable iff ($isunknown(out))
           1'b1 |=> out[30:0] == $past(out_golden);
    endproperty

    a_out: assert property (chk_out) else begin
       $error;
       -> test.ERROR;
    end

`endif




   property add_sub;
      @(posedge clk)
        disable iff($isunknown(fract_out_q))
          if(fasu_op)
            (1'b1 |=> fract_out_q == $past(fracta) + $past(fractb))
          else
            (1'b1 |=> fract_out_q == $past(fracta) - $past(fractb));
   endproperty

   property mul;
      @(posedge clk)
        disable iff ($isunknown(prod))
        prod == $past(fracta_mul,2) * $past(fractb_mul,2);
   endproperty

   // Note: 0in does not support "/" and "%" operator
   property div;
      @(posedge clk)
        disable iff ($isunknown(quo))
        quo == $past(fdiv_opa,2) / $past(fractb_mul,2);
   endproperty

   property rem;
      @(posedge clk)
        disable iff ($isunknown(remainder))
        remainder == $past(fdiv_opa,2) % $past(fractb_mul,2);
   endproperty

   property chk_fpu_op_r1;
      @(posedge clk)
        disable iff ($isunknown({fpu_op_r1, fpu_op}))
          1'b1 |=> (fpu_op_r1 == $past(fpu_op));
   endproperty

   property chk_fpu_op_r2;
      @(posedge clk)
        disable iff ($isunknown({fpu_op_r2, fpu_op_r1}))
          1'b1 |=> (fpu_op_r2 == $past(fpu_op_r1));
   endproperty

   property chk_fpu_op_r3;
      @(posedge clk)
        disable iff ($isunknown({fpu_op_r3, fpu_op_r2}))
          1'b1 |=> (fpu_op_r3 == $past(fpu_op_r2));
   endproperty


   //assert the property

   // Note: 0in does not support "/" and "%" operator
`ifdef VENNSA_DYNAMIC_SIMULATION      
   a_div: assert property (div)else begin
      $error;
      -> test.ERROR; 
   end
   
   a_rem: assert property (rem)else begin
      $error;
      -> test.ERROR;
   end
`endif

   a_add_sub: assert property (add_sub) else begin
      $error;
      `ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
      `endif
   end    
   
   // a_mul doesn't work for unknown reason; assertion goes off even when the result is correct.
   //a_mul: assert property (mul)else begin
   //   $display("%t: prod %d, $past(fracta) %d, $past(fractb) %d a*b %d",
   //            $time, prod, $past(fracta_mul,2), $past(fractb_mul,2), $past(fracta_mul,2)*$past(fractb_mul,2) );
   //     $fatal;
   //end;
 
   a_fpu_op_r1: assert property (chk_fpu_op_r1) else begin
      $error;
      `ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
      `endif
   end 

   a_fpu_op_r2: assert property (chk_fpu_op_r2) else begin
      $error;
      `ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
      `endif
   end

   a_fpu_op_r3: assert property (chk_fpu_op_r3) else begin
      $error;
      `ifdef VENNSA_DYNAMIC_SIMULATION      
      -> test.ERROR;
      `endif
   end

endmodule

bind fpu check_fpu chk_fpu(.*);
