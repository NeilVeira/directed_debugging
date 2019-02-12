module check_except(input clk,
                    input [31:0] opa, opb,
                    input expa_ff, expb_ff,
                    input inf, ind,
                    input qnan, snan,
                    input opa_nan, opb_nan,
                    input opa_00, opb_00, opa_inf, opb_inf, opa_dn, opb_dn);

   initial
     $display("assert_except binided");

//   wire check_qnan=$isunknown(qnan);
//   property chk_qnan;
//      @(posedge clk)
//        disable iff(check_qnan)
//          1'b1 |=> (qnan == (($past(expa_ff) & $past(opa[22],2)) | ($past(expb_ff) & $past(opb[22],2))));
//   endproperty
//
//   wire check_snan=$isunknown(snan);
//   property chk_snan;
//      @(posedge clk)
//        disable iff (check_snan)
//          1'b1 |=> (snan == (($past(expa_ff)& (!$past(opa[22],2)) & ($past(opa[21:0],2)>0)) | 
//                    ($past(expb_ff)& (!$past(opb[22],2)) & ($past(opb[21:0],2)>0))));
//   endproperty
//
//   a_chk_quan: assert property (chk_qnan) else begin
//      $error;
//`ifdef VENNSA_DYNAMIC_SIMULATION
//      -> test.ERROR;
//`endif
//   end
//   
//   a_chk_snan: assert property (chk_snan) else begin
//      $error;
//`ifdef VENNSA_DYNAMIC_SIMULATION
//      -> test.ERROR;
//`endif
//   end
   
`include "func.sv"

    property check_inf;
        @(posedge clk)
        (inf_op(opa) || inf_op(opb)) |-> ##2 inf;
    endproperty

    property check_ind;
        @(posedge clk)
        (inf_op(opa) && inf_op(opb)) |-> ##2 ind;
    endproperty

    property check_qnan;
        @(posedge clk)
        ((qnan_op(opa) || qnan_op(opb)) |-> ##2 qnan) and (!(qnan_op(opa) || qnan_op(opb)) |-> ##2 !qnan);
    endproperty

    property check_snan;
        @(posedge clk) if (!$isunknown(snan))
        ((snan_op(opa) || snan_op(opb)) |-> ##2 ($isunknown(snan) || snan)) and (!(snan_op(opa) || snan_op(opb)) |-> ##2 ($isunknown(snan) || !snan));
    endproperty

    property check_op_nan(op, sig);
        @(posedge clk)
        (qnan_op(op) || snan_op(op)) |-> ##1 sig;
    endproperty

    property check_op_zero(op, sig);
        @(posedge clk)
        (!(|exponent(op)) && !(|fraction(op))) |-> ##2 sig;
    endproperty

    property check_op_inf(op, sig);
        @(posedge clk)
        (&exponent(op) && !(|fraction(op))) |-> ##2 sig;
    endproperty

    property check_op_dn(op, sig);
        @(posedge clk)
        !(|exponent(op)) |-> ##2 sig;
    endproperty

    a_check_inf: assert property (check_inf) 
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_ind: assert property (check_ind)
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_qnan: assert property (check_qnan)
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_snan: assert property (check_snan)
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opa_nan: assert property (check_op_nan(opa, opa_nan))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opb_nan: assert property (check_op_nan(opb, opb_nan))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opa_zero: assert property (check_op_zero(opa, opa_00))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opb_zero: assert property (check_op_zero(opb, opb_00))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opa_inf: assert property (check_op_inf(opa, opa_inf))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opb_inf: assert property (check_op_inf(opb, opb_inf))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opa_dn: assert property (check_op_dn(opa, opa_dn))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end

    a_check_opb_dn: assert property (check_op_dn(opb, opb_dn))
    else begin
      $error;
`ifdef VENNSA_DYNAMIC_SIMULATION
      -> test.ERROR;
`endif
    end


   
endmodule

bind except check_except chk_except(.*);
