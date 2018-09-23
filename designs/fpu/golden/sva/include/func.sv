    function [7:0] exponent;
        input [31:0] op;
        exponent = op[30:23];
    endfunction

    function [22:0] fraction;
        input [31:0] op;
        fraction = op[22:0];
    endfunction

    function [0:0] inf_op;
        input [31:0] op;
        inf_op = (&exponent(op)) && !(|fraction(op));
    endfunction

    function [0:0] most_sig_bit;
        input [22:0] fr;
        most_sig_bit = fr[22];
    endfunction

    function [0:0] qnan_op;
        input [31:0] op;
        qnan_op = (&exponent(op)) & most_sig_bit(fraction(op));
    endfunction

    function snan_op;
        input [31:0] op;
        snan_op = (&exponent(op)) && !most_sig_bit(fraction(op)) && |fraction(op);
    endfunction

    function zero_op;
        input [31:0] op;
        zero_op = !(|exponent(op)) && !(|fraction(op));
    endfunction
    
    function dn_op;
        input [31:0] op;
        dn_op = !(|exponent(op));
    endfunction

    function valid_op;
        input [31:0] op;
        valid_op = !(&exponent(op));
    endfunction
