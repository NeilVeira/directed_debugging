`timescale 1 ps / 1 ps

`define TRUE 1 
`define FALSE 0 
`define NULL 0
`define EOF -1
`define MAX_BUFFER_SZ   2048
`define MAX_NAME_SZ     256
`define MAX_WIDTH       256
`define COLON           ":"
`define DOT             "."
`define NEWLINE         "\n"
`define CARRIAGE_RETURN  8'h0D
`define SPACE           " "
`define TAB             "\t"
`define OPEN_BRACKET    "["
`define CLOSE_BRACKET   "]"
`define OFFSET          9
`define H10             8'h10
`define H10000          20'h10000
`define AWORD           8
`define MASK15          32'h000000FF
`define EXT_STR         "ver"
`define PERCENT         "%"
`define MINUS           "-"
`define SEMICOLON       ";"
`define EQUAL           "="

// MODULE DECLARATION
module ALTERA_MF_MEMORY_INITIALIZATION;

/****************************************************************/
/* convert uppercase character values to lowercase.             */
/****************************************************************/
function [8:1] tolower;
    input [8:1] given_character;
    reg [8:1] conv_char;

begin
    if ((given_character >= 65) && (given_character <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
    begin
        conv_char = given_character + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
        tolower = conv_char;
    end
    else
        tolower = given_character;    
end
endfunction
    
/****************************************************************/
/* Read in Altera-mif format data to verilog format data.       */
/****************************************************************/
task convert_mif2ver;
    input[`MAX_NAME_SZ*8 : 1] in_file;
    input width;
    output [`MAX_NAME_SZ*8 : 1] out_file;
    reg [`MAX_NAME_SZ*8 : 1] in_file;
    reg [`MAX_NAME_SZ*8 : 1] out_file;
    reg [`MAX_NAME_SZ*8 : 1] buffer;
    reg [`MAX_WIDTH : 0] memory_data1, memory_data2;
    reg [8 : 1] c;
    reg [3 : 0] hex, tmp_char;
    reg [24 : 1] address_radix, data_radix;
    reg get_width;
    reg get_depth;
    reg get_data_radix;
    reg get_address_radix;
    reg width_found;
    reg depth_found;
    reg data_radix_found;
    reg address_radix_found;
    reg get_address_data_pairs;
    reg get_address;
    reg get_data;
    reg display_address;
    reg invalid_address;
    reg get_start_address;
    reg get_end_address;
    reg done;
    reg error_status;
    reg first_rec;
    reg last_rec;

    integer width;
    integer memory_width, memory_depth;
    integer value;
    integer ifp, ofp, r, r2;
    integer i, j, k, m, n;
    
    integer off_addr, nn, address, tt, cc, aah, aal, dd, sum ;
    integer start_address, end_address;
    integer line_no;
    integer character_count;
    integer comment_with_percent_found;
    integer comment_with_double_minus_found;

begin
`ifdef NO_PLI
`else
    `ifdef USE_RIF
    `else
        done = `FALSE;
        error_status = `FALSE;
        first_rec = `FALSE;
        last_rec = `FALSE;
        comment_with_percent_found = `FALSE;
        comment_with_double_minus_found = `FALSE;

        off_addr= 0;
        nn= 0;
        address = 0;
        start_address = 0;
        end_address = 0;
        tt= 0;
        cc= 0;
        aah= 0;
        aal= 0;
        dd= 0;
        sum = 0;
        line_no = 1;
        c = 0;
        hex = 0;
        value = 0;
        buffer = "";
        character_count = 0;
        memory_width = 0;
        memory_depth = 0;
        memory_data1 = {(`MAX_WIDTH+1) {1'b0}};
        memory_data2 = {(`MAX_WIDTH+1) {1'b0}};
        address_radix = "hex";
        data_radix = "hex";
        get_width = `FALSE;
        get_depth = `FALSE;
        get_data_radix = `FALSE;
        get_address_radix = `FALSE;
        width_found = `FALSE;
        depth_found = `FALSE;
        data_radix_found = `FALSE;
        address_radix_found = `FALSE;
        get_address_data_pairs = `FALSE;
        display_address = `FALSE;
        invalid_address = `FALSE;
        get_start_address = `FALSE;
        get_end_address = `FALSE;

        if((in_file[4*8 : 1] == ".dat") || (in_file[4*8 : 1] == ".DAT"))
            out_file = in_file;
        else
        begin
            ifp = $fopen(in_file, "r");

            if (ifp == `NULL)
            begin
                $display("ERROR: cannot read %0s.", in_file);
                done = `TRUE;
            end
        
            out_file = in_file;
            
            if((out_file[4*8 : 1] == ".mif") || (out_file[4*8 : 1] == ".MIF"))
                out_file[3*8 : 1] = `EXT_STR;
            else
            begin
                $display("ERROR: Invalid input file name %0s. Expecting file with .mif extension and Altera-mif data format.", in_file);
                done = `TRUE;
            end

            if (!done)
            begin            
                ofp = $fopen(out_file, "w");

                if (ofp == `NULL)
                begin
                    $display("ERROR : cannot write %0s.", out_file);
                    done = `TRUE;
                end
            end
            
            while((!done) && (!error_status))
            begin : READER
 
                r = $fgetc(ifp);

                if (r == `EOF)
                begin
                // to do : add more checking on whether a particular assigment(width, depth, memory/address) are mising
                    if(!first_rec)
                    begin
                        error_status = `TRUE;
                        $display("WARNING: %0s, Intel-hex data file is empty.", in_file);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else if (!get_address_data_pairs)
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Missing `content begin` statement.", in_file, line_no);
                    end
                    else if(!last_rec)
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Missing `end` statement.", in_file, line_no);
                    end
                    done = `TRUE;
                end
                else if ((r == `NEWLINE) || (r == `CARRIAGE_RETURN))
                begin                    
                    if ((buffer == "contentbegin") && (get_address_data_pairs == `FALSE))
                    begin
                        get_address_data_pairs = `TRUE;
                        get_address = `TRUE;
                        buffer = "";
                    end
                    else if (buffer == "content")
                    begin
                        // continue to next character
                    end
                    else
                    if (buffer != "")
                    begin
                        // found invalid syntax in the particular line.
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        disable READER;
                    end
                    line_no = line_no +1;
                    
                end
                else if ((r == `SPACE) || (r == `TAB))
                begin
                    // continue to next character;
                end
                else if (r == `PERCENT)
                begin
                    // Ignore all the characters which which is part of comment.
                    r = $fgetc(ifp);

                    while ((r != `PERCENT) && (r != `NEWLINE) && (r != `CARRIAGE_RETURN))
                    begin
                        r = $fgetc(ifp);                      
                    end

                    if ((r == `NEWLINE) || (r == `CARRIAGE_RETURN))
                    begin
                        line_no = line_no +1;

                        if ((buffer == "contentbegin") && (get_address_data_pairs == `FALSE))
                        begin
                            get_address_data_pairs = `TRUE;
                            get_address = `TRUE;
                            buffer = "";
                        end
                    end
                end
                else if (r == `MINUS)
                begin
                    r = $fgetc(ifp);
                    if (r == `MINUS)
                    begin
                        // Ignore all the characters which which is part of comment.
                        r = $fgetc(ifp);
    
                        while ((r != `NEWLINE) && (r != `CARRIAGE_RETURN))
                        begin
                            r = $fgetc(ifp);
                            
                        end
    
                        if ((r == `NEWLINE) || (r == `CARRIAGE_RETURN))
                        begin
                            line_no = line_no +1;

                            if ((buffer == "contentbegin") && (get_address_data_pairs == `FALSE))
                            begin
                                get_address_data_pairs = `TRUE;
                                get_address = `TRUE;
                                buffer = "";
                            end
                        end
                    end
                    else
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        done = `TRUE;
                        disable READER;
                    end
                end
                else if (r == `EQUAL)
                begin
                    if (buffer == "width")
                    begin
                        if (width_found == `FALSE)
                        begin
                            get_width = `TRUE;
                            buffer = "";
                        end
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Width has already been specified once.", in_file, line_no);
                        end
                    end
                    else if (buffer == "depth")
                    begin
                        get_depth = `TRUE;
                        buffer = ""; 
                    end
                    else if (buffer == "data_radix")
                    begin
                        get_data_radix = `TRUE;
                        buffer = "";
                    end
                    else if (buffer == "address_radix")
                    begin
                        get_address_radix = `TRUE;
                        buffer = "";
                    end
                    else
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Unknown setting (%0s).", in_file, line_no, buffer);
                    end
                end
                else if (r == `COLON)
                begin
                    if (!get_address_data_pairs)
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Missing `content begin` statement.", in_file, line_no);
                    end
                    else if (invalid_address == `TRUE)
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                    end
                    begin
                        get_address = `FALSE;
                        get_data = `TRUE;
                        display_address = `TRUE;
                    end
                end
                else if (r == `DOT)
                begin
                    r = $fgetc(ifp);
                    if (r == `DOT)
                    begin
                        if (get_start_address == `TRUE)
                        begin
                            start_address = address;
                            address = 0; 
                            get_start_address = `FALSE;
                            get_end_address = `TRUE;
                        end
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                    end
                    else
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        done = `TRUE;
                        disable READER;
                    end
                end
                else if (r == `OPEN_BRACKET)
                begin
                    get_start_address = `TRUE;
                end
                else if (r == `CLOSE_BRACKET)
                begin
                    if (get_end_address == `TRUE)
                    begin
                        end_address = address;
                        address = 0; 
                        get_end_address = `FALSE;
                    end
                    else
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid Altera-mif record.", in_file, line_no);
                        done = `TRUE;
                        disable READER;
                    end
                end                
                else if (r == `SEMICOLON)
                begin
                    if (get_width == `TRUE)
                    begin
                        width_found = `TRUE;
                        memory_width = value;
                        value = 0;
                        get_width = `FALSE;
                    end
                    else if (get_depth == `TRUE)
                    begin
                        depth_found = `TRUE;
                        memory_depth = value;
                        value = 0;
                        get_depth = `FALSE;
                    end
                    else if (get_data_radix == `TRUE)
                    begin
                        data_radix_found = `TRUE;
                        get_data_radix = `FALSE;

                        if ((buffer == "bin") || (buffer == "oct") || (buffer == "dec") || (buffer == "uns") ||
                            (buffer == "hex"))
                        begin
                            data_radix = buffer[24 : 1];
                        end
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid assignment (%0s) to data_radix.", in_file, line_no, buffer);
                        end
                        buffer = "";
                    end
                    else if (get_address_radix == `TRUE)
                    begin
                        address_radix_found = `TRUE;
                        get_address_radix = `FALSE;

                        if ((buffer == "bin") || (buffer == "oct") || (buffer == "dec") || (buffer == "uns") ||
                            (buffer == "hex"))
                        begin
                            address_radix = buffer[24 : 1];
                        end
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid assignment (%0s) to address radix.", in_file, line_no, buffer);
                        end
                        buffer = "";
                    end
                    else if (buffer == "end")
                    begin
                        if (get_address_data_pairs == `TRUE)
                        begin
                            last_rec = `TRUE;
                            buffer = "";
                        end
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Missing `content begin` statement.", in_file, line_no);
                        end
                    end
                    else if (get_data == `TRUE)
                    begin
                        get_address = `TRUE;
                        get_data = `FALSE;
                        buffer = "";
                        character_count = 0;
                        
                        if (start_address != end_address)
                        begin
                            for (address = start_address; address <= end_address; address = address+1)
                            begin
                                $fdisplay(ofp,"@%0h", address);
                                
                                for (i = memory_width -1; i >= 0; i = i-1 )
                                begin
                                    hex[(i % 4)] =  memory_data1[i];
                                    
                                    if ((i % 4) == 0)
                                    begin
                                        $fwrite(ofp, "%0h", hex);
                                        hex = 0;
                                    end
                                end
        
                                $fwrite(ofp, "\n");
                            end
                            start_address = 0;
                            end_address = 0;
                            address = 0;
                            hex = 0;
                            memory_data1 = {(`MAX_WIDTH+1) {1'b0}};
                        end
                        else
                        begin
                            if (display_address == `TRUE)
                            begin
                                $fdisplay(ofp,"@%0h", address);
                                display_address = `FALSE;
                            end
                            
                            for (i = memory_width -1; i >= 0; i = i-1 )
                            begin
                                hex[(i % 4)] =  memory_data1[i];
                                
                                if ((i % 4) == 0)
                                begin
                                    $fwrite(ofp, "%0h", hex);
                                    hex = 0;
                                end
                            end
    
                            $fwrite(ofp, "\n");                      
                            address = 0;
                            hex = 0;
                            memory_data1 = {(`MAX_WIDTH+1) {1'b0}};
                        end
                    end
                    else
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid assigment.", in_file, line_no);
                    end
                end
                else if ((get_width == `TRUE) || (get_depth == `TRUE))
                begin
                    if ((r >= "0") && (r <= "9"))
                        value = (value * 10) + (r - 'h30);
                    else
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid assignment to width/depth.", in_file, line_no);
                    end
                end
                else if (get_address == `TRUE)
                begin
                    if (address_radix == "hex")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            value = 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            value = 10 + (r - 'h61);
                        else
                        begin
                            invalid_address = `TRUE;
                        end
                            
                        address = (address * 16) + value;
                    end
                    else if ((address_radix == "dec"))
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `TRUE;
                        end
                            
                        address = (address * 10) + value;
                    end
                    else if (address_radix == "uns")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `TRUE;
                        end
                            
                        address = (address * 10) + value; 
                    end
                    else if (address_radix == "bin")
                    begin
                        if ((r >= "0") && (r <= "1"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `TRUE;
                        end
                            
                        address = (address * 2) + value;
                    end
                    else if (address_radix == "oct")
                    begin
                        if ((r >= "0") && (r <= "7"))
                            value = (r - 'h30);
                        else
                        begin
                            invalid_address = `TRUE;
                        end
                            
                        address = (address * 8) + value;
                    end
                    
                    if ((r >= 65) && (r <= 90))
                        c = tolower(r); 
                    else
                        c = r;

                    {tmp_char,buffer} = {buffer, c};                    
                end
                else if (get_data == `TRUE)
                begin                    
                    character_count = character_count +1;

                    if (data_radix == "hex")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            value = 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            value = 10 + (r - 'h61);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                            
                        memory_data1 = (memory_data1 * 16) + value;
                    end
                    else if ((data_radix == "dec"))
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                            
                        memory_data1 = (memory_data1 * 10) + value;
                    end
                    else if (data_radix == "uns")
                    begin
                        if ((r >= "0") && (r <= "9"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                            
                        memory_data1 = (memory_data1 * 10) + value; 
                    end
                    else if (data_radix == "bin")
                    begin
                        if ((r >= "0") && (r <= "1"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                            
                        memory_data1 = (memory_data1 * 2) + value;
                    end
                    else if (data_radix == "oct")
                    begin
                        if ((r >= "0") && (r <= "7"))
                            value = (r - 'h30);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                            
                        memory_data1 = (memory_data1 * 8) + value;
                    end
                end
                else
                begin
                    first_rec = `TRUE;
                    
                    if ((r >= 65) && (r <= 90))
                        c = tolower(r); 
                    else
                        c = r;

                    {tmp_char,buffer} = {buffer, c};                    
                end
            end
            $fclose(ifp);
            $fclose(ofp);
        end
    `endif 
`endif    
end
endtask // convert_mif2ver

/****************************************************************/
/* Read in Intel-hex format data to verilog format data.        */
/*  Intel-hex format    :nnaaaaattddddcc                        */
/****************************************************************/
task convert_hex2ver;
    input[`MAX_NAME_SZ*8 : 1] in_file;
    input width;
    output [`MAX_NAME_SZ*8 : 1] out_file;
    reg [`MAX_NAME_SZ*8 : 1] in_file;
    reg [`MAX_NAME_SZ*8 : 1] out_file;
    reg [8:1] c;
    reg [3:0] hex, tmp_char;
    reg done;
    reg error_status;
    reg first_rec;
    reg last_rec;
    reg first_normal_record;
    reg is_word_address_format;

    integer width;
    integer ifp, ofp, r, r2;
    integer i, j, k, m, n;
    
    integer off_addr, nn, aaaa, aaaa_pre, tt, cc, aah, aal, dd, sum ;
    integer line_no;
    integer divide_factor;

begin
`ifdef NO_PLI
`else
    `ifdef USE_RIF
    `else
        done = `FALSE;
        error_status = `FALSE;
        first_rec = `FALSE;
        last_rec = `FALSE;
        first_normal_record = `TRUE;
        is_word_address_format = `FALSE;
        off_addr= 0;
        nn= 0;
        aaaa= 0;
        aaaa_pre = 0;
        tt= 0;
        cc= 0;
        aah= 0;
        aal= 0;
        dd= 0;
        sum = 0;
        line_no = 1;
        c = 0;
        hex = 0;
        divide_factor = 1;

        if((in_file[4*8 : 1] == ".dat") || (in_file[4*8 : 1] == ".DAT"))
            out_file = in_file;
        else
        begin
            ifp = $fopen(in_file, "r");
            if (ifp == `NULL)
            begin
                $display("ERROR: cannot read %0s.", in_file);
                done = `TRUE;
            end
        
            out_file = in_file;
            
            if((out_file[4*8 : 1] == ".hex") || (out_file[4*8 : 1] == ".HEX"))
                out_file[3*8 : 1] = `EXT_STR;
            else
            begin
                $display("ERROR: Invalid input file name %0s. Expecting file with .hex extension and Intel-hex data format.", in_file);
                done = `TRUE;
            end
            
            if (!done)
            begin            
                ofp = $fopen(out_file, "w");
                if (ofp == `NULL)
                begin
                    $display("ERROR : cannot write %0s.", out_file);
                    done = `TRUE;
                end
            end
            
            while((!done) && (!error_status))
            begin : READER
        
                r = $fgetc(ifp);
        
                if (r == `EOF)
                begin
                    if(!first_rec)
                    begin
                        error_status = `TRUE;
                        $display("WARNING: %0s, Intel-hex data file is empty.", in_file);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else if(!last_rec)
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Missing the last record.", in_file, line_no);
                    end
                end
                else if (r == `COLON)
                begin
                    first_rec = `TRUE;
                    nn= 0;
                    aaaa_pre = aaaa;
                    aaaa= 0;
                    tt= 0;
                    cc= 0;
                    aah= 0;
                    aal= 0;
                    dd= 0;
                    sum = 0;
        
                    // get record length bytes
                    for (i = 0; i < 2; i = i+1)
                    begin
                        r = $fgetc(ifp);
                        
                        if ((r >= "0") && (r <= "9"))
                            nn = (nn * 16) + (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            nn = (nn * 16) + 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            nn = (nn * 16) + 10 + (r - 'h61);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                    end
        
                    // get address bytes
                    for (i = 0; i < 4; i = i+1)
                    begin
                        r = $fgetc(ifp);
                        
                        if ((r >= "0") && (r <= "9"))
                            hex = (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            hex = 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            hex = 10 + (r - 'h61);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                        
                        aaaa = (aaaa * 16) + hex;
                        
                        if (i < 2)
                            aal = (aal * 16) + hex;
                        else
                            aah = (aah * 16) + hex;
                    end
                    
                    // get record type bytes   
                    for (i = 0; i < 2; i = i+1)
                    begin
                        r = $fgetc(ifp);
                        
                        if ((r >= "0") && (r <= "9"))
                            tt = (tt * 16) + (r - 'h30);
                        else if ((r >= "A") && (r <= "F"))
                            tt = (tt * 16) + 10 + (r - 'h41);
                        else if ((r >= "a") && (r <= "f"))
                            tt = (tt * 16) + 10 + (r - 'h61);
                        else
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                            done = `TRUE;
                            disable READER;
                        end
                    end
        
                    if((tt == 2) && (nn != 2) )
                    begin
                        error_status = `TRUE;
                        $display("ERROR: %0s, line %0d, Invalid data record.", in_file, line_no);
                    end
                    else
                    begin
        
                        // get the sum of all the bytes for record length, address and record types
                        sum = nn + aah + aal + tt ; 
                   
                        // check the record type
                        case(tt)
                            // normal_record
                            8'h00 :
                            begin
                                first_rec = `TRUE;
                                i = 0;
                                k = width / `AWORD;
                                if ((width % `AWORD) != 0)
                                    k = k + 1; 
        
                                if ((first_normal_record == `FALSE) &&(aaaa != k))
                                    is_word_address_format = `TRUE;
                                
                                first_normal_record = `FALSE;

                                if ((aaaa == k) && (is_word_address_format == `FALSE))
                                    divide_factor = k;

                                // k = no. of bytes per entry.
                                while (i < nn)
                                begin
                                    $fdisplay(ofp,"@%0h", (aaaa + off_addr)/divide_factor);

                                    for (j = 1; j <= k; j = j +1)
                                    begin
                                        if ((k - j +1) > nn)
                                        begin
                                            for(m = 1; m <= 2; m= m+1)
                                            begin
                                                if((((k-j)*8) + ((3-m)*4) - width) < 4)
                                                    $fwrite(ofp, "0");
                                            end
                                        end
                                        else
                                        begin
                                            // get the data bytes
                                            for(m = 1; m <= 2; m= m+1)
                                            begin                    
                                                r = $fgetc(ifp);
                            
                                                if ((r >= "0") && (r <= "9"))
                                                    hex = (r - 'h30);
                                                else if ((r >= "A") && (r <= "F"))
                                                    hex = 10 + (r - 'h41);
                                                else if ((r >= "a") && (r <= "f"))
                                                    hex = 10 + (r - 'h61);
                                                else
                                                begin
                                                    error_status = `TRUE;
                                                    $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                                    done = `TRUE;
                                                    disable READER;
                                                end
            
                                                if((((k-j)*8) + ((3-m)*4) - width) < 4)
                                                    $fwrite(ofp, "%h", hex);
                                                dd = (dd * 16) + hex;
            
                                                if(m % 2 == 0)
                                                begin
                                                    sum = sum + dd;
                                                    dd = 0;
                                                end
                                            end
                                        end
                                    end
                                    $fwrite(ofp, "\n");
        
                                    i = i + k;
                                    aaaa = aaaa + 1;
                                end // end of while (i < nn)
                            end
                            // last record
                            8'h01: 
                            begin
                                last_rec = `TRUE;
                                done = `TRUE;
                            end
                            // address base record
                            8'h02:
                            begin
                                off_addr= 0;

                                // get the extended segment address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin                    
                                    r = $fgetc(ifp);
                
                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        done = `TRUE;
                                        disable READER;
                                    end
        
                                    off_addr = (off_addr * `H10) + hex;        
                                    dd = (dd * 16) + hex;
        
                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end
            
                                off_addr = off_addr * `H10;
                            end
                            // address base record
                            8'h03:
                                // get the start segment address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin                    
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        done = `TRUE;
                                        disable READER;
                                    end
                                    dd = (dd * 16) + hex;
        
                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end
                            // address base record
                            8'h04:
                            begin
                                off_addr= 0;

                                // get the extended linear address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin                    
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        done = `TRUE;
                                        disable READER;
                                    end
        
                                    off_addr = (off_addr * `H10) + hex;        
                                    dd = (dd * 16) + hex;
        
                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end
            
                                off_addr = off_addr * `H10000;
                            end
                            // address base record
                            8'h05:
                                // get the start linear address record
                                for(i = 1; i <= (nn*2); i= i+1)
                                begin                    
                                    r = $fgetc(ifp);

                                    if ((r >= "0") && (r <= "9"))
                                        hex = (r - 'h30);
                                    else if ((r >= "A") && (r <= "F"))
                                        hex = 10 + (r - 'h41);
                                    else if ((r >= "a") && (r <= "f"))
                                        hex = 10 + (r - 'h61);
                                    else
                                    begin
                                        error_status = `TRUE;
                                        $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                        done = `TRUE;
                                        disable READER;
                                    end
                                    dd = (dd * 16) + hex;
        
                                    if(i % 2 == 0)
                                    begin
                                        sum = sum + dd;
                                        dd = 0;
                                    end
                                end
                            default:
                            begin
                                error_status = `TRUE;
                                $display("ERROR: %0s, line %0d, Unknown record type.", in_file, line_no);
                            end
                        endcase
                        
                        // get the checksum bytes
                        for (i = 0; i < 2; i = i+1)
                        begin
                            r = $fgetc(ifp);
                            
                            if ((r >= "0") && (r <= "9"))
                                cc = (cc * 16) + (r - 'h30);
                            else if ((r >= "A") && (r <= "F"))
                                cc = 10 + (cc * 16) + (r - 'h41);
                            else if ((r >= "a") && (r <= "f"))
                                cc = 10 + (cc * 16) + (r - 'h61);
                            else
                            begin
                                error_status = `TRUE;
                                $display("ERROR: %0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                                done = `TRUE;
                                disable READER;
                            end
                        end
                        
                        // Perform check sum.
                        if(((~sum+1)& `MASK15) != cc)
                        begin
                            error_status = `TRUE;
                            $display("ERROR: %0s, line %0d, Invalid checksum.", in_file, line_no);
                        end
                    end
                end
                else if ((r == `NEWLINE) || (r == `CARRIAGE_RETURN))
                begin
                    line_no = line_no +1;
                end
                else if (r == `SPACE)
                begin
                    // continue to next character;
                end
                else
                begin
                    error_status = `TRUE;
                    $display("ERROR:%0s, line %0d, Invalid INTEL HEX record.", in_file, line_no);
                    done = `TRUE;
                end
            end
            $fclose(ifp);
            $fclose(ofp);
        end
    `endif 
`endif    
end
endtask // convert_hex2ver

task convert_to_ver_file;
    input[`MAX_NAME_SZ*8 : 1] in_file;
    input width;
    output [`MAX_NAME_SZ*8 : 1] out_file;
    reg [`MAX_NAME_SZ*8 : 1] in_file;
    reg [`MAX_NAME_SZ*8 : 1] out_file;
    integer width;
begin    
           
        if((in_file[4*8 : 1] == ".hex") || (in_file[4*8 : 1] == ".HEX") ||
            (in_file[4*8 : 1] == ".dat") || (in_file[4*8 : 1] == ".DAT"))
            convert_hex2ver(in_file, width, out_file);
        else if((in_file[4*8 : 1] == ".mif") || (in_file[4*8 : 1] == ".MIF"))
            convert_mif2ver(in_file, width, out_file);
        else
            $display("ERROR: Invalid input file name %0s. Expecting file with .hex extension (with Intel-hex data format) or .mif extension (with Altera-mif data format).", in_file);
end
endtask // convert_to_ver_file

endmodule // ALTERA_MF_MEMORY_INITIALIZATION


module ALTERA_DEVICE_FAMILIES;

function IS_FAMILY_STRATIX;
    input[8*20:1] device;
    reg is_stratix;
begin
    if ((device == "Stratix") || (device == "STRATIX") || (device == "stratix") || (device == "Yeager") || (device == "YEAGER") || (device == "yeager"))
        is_stratix = 1;
    else
        is_stratix = 0;

    IS_FAMILY_STRATIX  = is_stratix;
end
endfunction //IS_FAMILY_STRATIX

function IS_FAMILY_STRATIXGX;
    input[8*20:1] device;
    reg is_stratixgx;
begin
    if ((device == "Stratix GX") || (device == "STRATIX GX") || (device == "stratix gx") || (device == "Stratix-GX") || (device == "STRATIX-GX") || (device == "stratix-gx") || (device == "StratixGX") || (device == "STRATIXGX") || (device == "stratixgx") || (device == "Aurora") || (device == "AURORA") || (device == "aurora"))
        is_stratixgx = 1;
    else
        is_stratixgx = 0;

    IS_FAMILY_STRATIXGX  = is_stratixgx;
end
endfunction //IS_FAMILY_STRATIXGX

function IS_FAMILY_CYCLONE;
    input[8*20:1] device;
    reg is_cyclone;
begin
    if ((device == "Cyclone") || (device == "CYCLONE") || (device == "cyclone") || (device == "ACEX2K") || (device == "acex2k") || (device == "ACEX 2K") || (device == "acex 2k") || (device == "Tornado") || (device == "TORNADO") || (device == "tornado"))
        is_cyclone = 1;
    else
        is_cyclone = 0;

    IS_FAMILY_CYCLONE  = is_cyclone;
end
endfunction //IS_FAMILY_CYCLONE

function IS_FAMILY_MAXII;
    input[8*20:1] device;
    reg is_maxii;
begin
    if ((device == "MAX II") || (device == "max ii") || (device == "MAXII") || (device == "maxii") || (device == "Tsunami") || (device == "TSUNAMI") || (device == "tsunami"))
        is_maxii = 1;
    else
        is_maxii = 0;

    IS_FAMILY_MAXII  = is_maxii;
end
endfunction //IS_FAMILY_MAXII

function IS_FAMILY_STRATIXII;
    input[8*20:1] device;
    reg is_stratixii;
begin
    if ((device == "Stratix II") || (device == "STRATIX II") || (device == "stratix ii") || (device == "StratixII") || (device == "STRATIXII") || (device == "stratixii") || (device == "Armstrong") || (device == "ARMSTRONG") || (device == "armstrong"))
        is_stratixii = 1;
    else
        is_stratixii = 0;

    IS_FAMILY_STRATIXII  = is_stratixii;
end
endfunction //IS_FAMILY_STRATIXII

function IS_FAMILY_STRATIXIIGX;
    input[8*20:1] device;
    reg is_stratixiigx;
begin
    if ((device == "Stratix II GX") || (device == "STRATIX II GX") || (device == "stratix ii gx") || (device == "StratixIIGX") || (device == "STRATIXIIGX") || (device == "stratixiigx"))
        is_stratixiigx = 1;
    else
        is_stratixiigx = 0;

    IS_FAMILY_STRATIXIIGX  = is_stratixiigx;
end
endfunction //IS_FAMILY_STRATIXIIGX

function IS_FAMILY_ARRIAGX;
    input[8*20:1] device;
    reg is_arriagx;
begin
    if ((device == "Arria GX") || (device == "ARRIA GX") || (device == "arria gx") || (device == "ArriaGX") || (device == "ARRIAGX") || (device == "arriagx") || (device == "Stratix II GX Lite") || (device == "STRATIX II GX LITE") || (device == "stratix ii gx lite") || (device == "StratixIIGXLite") || (device == "STRATIXIIGXLITE") || (device == "stratixiigxlite"))
        is_arriagx = 1;
    else
        is_arriagx = 0;

    IS_FAMILY_ARRIAGX  = is_arriagx;
end
endfunction //IS_FAMILY_ARRIAGX

function IS_FAMILY_CYCLONEII;
    input[8*20:1] device;
    reg is_cycloneii;
begin
    if ((device == "Cyclone II") || (device == "CYCLONE II") || (device == "cyclone ii") || (device == "Cycloneii") || (device == "CYCLONEII") || (device == "cycloneii") || (device == "Magellan") || (device == "MAGELLAN") || (device == "magellan"))
        is_cycloneii = 1;
    else
        is_cycloneii = 0;

    IS_FAMILY_CYCLONEII  = is_cycloneii;
end
endfunction //IS_FAMILY_CYCLONEII

function IS_FAMILY_HARDCOPYII;
    input[8*20:1] device;
    reg is_hardcopyii;
begin
    if ((device == "HardCopy II") || (device == "HARDCOPY II") || (device == "hardcopy ii") || (device == "HardCopyII") || (device == "HARDCOPYII") || (device == "hardcopyii") || (device == "Fusion") || (device == "FUSION") || (device == "fusion"))
        is_hardcopyii = 1;
    else
        is_hardcopyii = 0;

    IS_FAMILY_HARDCOPYII  = is_hardcopyii;
end
endfunction //IS_FAMILY_HARDCOPYII

function IS_FAMILY_STRATIXIII;
    input[8*20:1] device;
    reg is_stratixiii;
begin
    if ((device == "Stratix III") || (device == "STRATIX III") || (device == "stratix iii") || (device == "StratixIII") || (device == "STRATIXIII") || (device == "stratixiii") || (device == "Titan") || (device == "TITAN") || (device == "titan") || (device == "SIII") || (device == "siii"))
        is_stratixiii = 1;
    else
        is_stratixiii = 0;

    IS_FAMILY_STRATIXIII  = is_stratixiii;
end
endfunction //IS_FAMILY_STRATIXIII

function IS_FAMILY_CYCLONEIII;
    input[8*20:1] device;
    reg is_cycloneiii;
begin
    if ((device == "Cyclone III") || (device == "CYCLONE III") || (device == "cyclone iii") || (device == "CycloneIII") || (device == "CYCLONEIII") || (device == "cycloneiii") || (device == "Barracuda") || (device == "BARRACUDA") || (device == "barracuda") || (device == "Cuda") || (device == "CUDA") || (device == "cuda") || (device == "CIII") || (device == "ciii"))
        is_cycloneiii = 1;
    else
        is_cycloneiii = 0;

    IS_FAMILY_CYCLONEIII  = is_cycloneiii;
end
endfunction //IS_FAMILY_CYCLONEIII

function IS_FAMILY_STRATIXIV;
    input[8*20:1] device;
    reg is_stratixiv;
begin
    if ((device == "Stratix IV") || (device == "STRATIX IV") || (device == "stratix iv") || (device == "TGX") || (device == "tgx") || (device == "StratixIV") || (device == "STRATIXIV") || (device == "stratixiv") || (device == "Stratix IV (GT)") || (device == "STRATIX IV (GT)") || (device == "stratix iv (gt)") || (device == "Stratix IV (GX)") || (device == "STRATIX IV (GX)") || (device == "stratix iv (gx)") || (device == "Stratix IV (E)") || (device == "STRATIX IV (E)") || (device == "stratix iv (e)") || (device == "StratixIV(GT)") || (device == "STRATIXIV(GT)") || (device == "stratixiv(gt)") || (device == "StratixIV(GX)") || (device == "STRATIXIV(GX)") || (device == "stratixiv(gx)") || (device == "StratixIV(E)") || (device == "STRATIXIV(E)") || (device == "stratixiv(e)") || (device == "StratixIIIGX") || (device == "STRATIXIIIGX") || (device == "stratixiiigx") || (device == "Stratix IV (GT/GX/E)") || (device == "STRATIX IV (GT/GX/E)") || (device == "stratix iv (gt/gx/e)") || (device == "Stratix IV (GT/E/GX)") || (device == "STRATIX IV (GT/E/GX)") || (device == "stratix iv (gt/e/gx)") || (device == "Stratix IV (E/GT/GX)") || (device == "STRATIX IV (E/GT/GX)") || (device == "stratix iv (e/gt/gx)") || (device == "Stratix IV (E/GX/GT)") || (device == "STRATIX IV (E/GX/GT)") || (device == "stratix iv (e/gx/gt)") || (device == "StratixIV(GT/GX/E)") || (device == "STRATIXIV(GT/GX/E)") || (device == "stratixiv(gt/gx/e)") || (device == "StratixIV(GT/E/GX)") || (device == "STRATIXIV(GT/E/GX)") || (device == "stratixiv(gt/e/gx)") || (device == "StratixIV(E/GX/GT)") || (device == "STRATIXIV(E/GX/GT)") || (device == "stratixiv(e/gx/gt)") || (device == "StratixIV(E/GT/GX)") || (device == "STRATIXIV(E/GT/GX)") || (device == "stratixiv(e/gt/gx)") || (device == "Stratix IV (GX/E)") || (device == "STRATIX IV (GX/E)") || (device == "stratix iv (gx/e)") || (device == "StratixIV(GX/E)") || (device == "STRATIXIV(GX/E)") || (device == "stratixiv(gx/e)"))
        is_stratixiv = 1;
    else
        is_stratixiv = 0;

    IS_FAMILY_STRATIXIV  = is_stratixiv;
end
endfunction //IS_FAMILY_STRATIXIV

function IS_FAMILY_ARRIAIIGX;
    input[8*20:1] device;
    reg is_arriaiigx;
begin
    if ((device == "Arria II GX") || (device == "ARRIA II GX") || (device == "arria ii gx") || (device == "ArriaIIGX") || (device == "ARRIAIIGX") || (device == "arriaiigx") || (device == "Arria IIGX") || (device == "ARRIA IIGX") || (device == "arria iigx") || (device == "ArriaII GX") || (device == "ARRIAII GX") || (device == "arriaii gx") || (device == "Arria II") || (device == "ARRIA II") || (device == "arria ii") || (device == "ArriaII") || (device == "ARRIAII") || (device == "arriaii") || (device == "Arria II (GX/E)") || (device == "ARRIA II (GX/E)") || (device == "arria ii (gx/e)") || (device == "ArriaII(GX/E)") || (device == "ARRIAII(GX/E)") || (device == "arriaii(gx/e)") || (device == "PIRANHA") || (device == "piranha"))
        is_arriaiigx = 1;
    else
        is_arriaiigx = 0;

    IS_FAMILY_ARRIAIIGX  = is_arriaiigx;
end
endfunction //IS_FAMILY_ARRIAIIGX

function IS_FAMILY_HARDCOPYIII;
    input[8*20:1] device;
    reg is_hardcopyiii;
begin
    if ((device == "HardCopy III") || (device == "HARDCOPY III") || (device == "hardcopy iii") || (device == "HardCopyIII") || (device == "HARDCOPYIII") || (device == "hardcopyiii") || (device == "HCX") || (device == "hcx"))
        is_hardcopyiii = 1;
    else
        is_hardcopyiii = 0;

    IS_FAMILY_HARDCOPYIII  = is_hardcopyiii;
end
endfunction //IS_FAMILY_HARDCOPYIII

function IS_FAMILY_HARDCOPYIV;
    input[8*20:1] device;
    reg is_hardcopyiv;
begin
    if ((device == "HardCopy IV") || (device == "HARDCOPY IV") || (device == "hardcopy iv") || (device == "HardCopyIV") || (device == "HARDCOPYIV") || (device == "hardcopyiv") || (device == "HardCopy IV (GX)") || (device == "HARDCOPY IV (GX)") || (device == "hardcopy iv (gx)") || (device == "HardCopy IV (E)") || (device == "HARDCOPY IV (E)") || (device == "hardcopy iv (e)") || (device == "HardCopyIV(GX)") || (device == "HARDCOPYIV(GX)") || (device == "hardcopyiv(gx)") || (device == "HardCopyIV(E)") || (device == "HARDCOPYIV(E)") || (device == "hardcopyiv(e)") || (device == "HCXIV") || (device == "hcxiv") || (device == "HardCopy IV (GX/E)") || (device == "HARDCOPY IV (GX/E)") || (device == "hardcopy iv (gx/e)") || (device == "HardCopy IV (E/GX)") || (device == "HARDCOPY IV (E/GX)") || (device == "hardcopy iv (e/gx)") || (device == "HardCopyIV(GX/E)") || (device == "HARDCOPYIV(GX/E)") || (device == "hardcopyiv(gx/e)") || (device == "HardCopyIV(E/GX)") || (device == "HARDCOPYIV(E/GX)") || (device == "hardcopyiv(e/gx)"))
        is_hardcopyiv = 1;
    else
        is_hardcopyiv = 0;

    IS_FAMILY_HARDCOPYIV  = is_hardcopyiv;
end
endfunction //IS_FAMILY_HARDCOPYIV

function IS_FAMILY_CYCLONEIIILS;
    input[8*20:1] device;
    reg is_cycloneiiils;
begin
    if ((device == "Cyclone III LS") || (device == "CYCLONE III LS") || (device == "cyclone iii ls") || (device == "CycloneIIILS") || (device == "CYCLONEIIILS") || (device == "cycloneiiils") || (device == "Cyclone III LPS") || (device == "CYCLONE III LPS") || (device == "cyclone iii lps") || (device == "Cyclone LPS") || (device == "CYCLONE LPS") || (device == "cyclone lps") || (device == "CycloneLPS") || (device == "CYCLONELPS") || (device == "cyclonelps") || (device == "Tarpon") || (device == "TARPON") || (device == "tarpon") || (device == "Cyclone IIIE") || (device == "CYCLONE IIIE") || (device == "cyclone iiie"))
        is_cycloneiiils = 1;
    else
        is_cycloneiiils = 0;

    IS_FAMILY_CYCLONEIIILS  = is_cycloneiiils;
end
endfunction //IS_FAMILY_CYCLONEIIILS

function IS_FAMILY_CYCLONEIVGX;
    input[8*20:1] device;
    reg is_cycloneivgx;
begin
    if ((device == "Cyclone IV GX") || (device == "CYCLONE IV GX") || (device == "cyclone iv gx") || (device == "Cyclone IVGX") || (device == "CYCLONE IVGX") || (device == "cyclone ivgx") || (device == "CycloneIV GX") || (device == "CYCLONEIV GX") || (device == "cycloneiv gx") || (device == "CycloneIVGX") || (device == "CYCLONEIVGX") || (device == "cycloneivgx") || (device == "Cyclone IV") || (device == "CYCLONE IV") || (device == "cyclone iv") || (device == "CycloneIV") || (device == "CYCLONEIV") || (device == "cycloneiv") || (device == "Cyclone IV (GX)") || (device == "CYCLONE IV (GX)") || (device == "cyclone iv (gx)") || (device == "CycloneIV(GX)") || (device == "CYCLONEIV(GX)") || (device == "cycloneiv(gx)") || (device == "Cyclone III GX") || (device == "CYCLONE III GX") || (device == "cyclone iii gx") || (device == "CycloneIII GX") || (device == "CYCLONEIII GX") || (device == "cycloneiii gx") || (device == "Cyclone IIIGX") || (device == "CYCLONE IIIGX") || (device == "cyclone iiigx") || (device == "CycloneIIIGX") || (device == "CYCLONEIIIGX") || (device == "cycloneiiigx") || (device == "Cyclone III GL") || (device == "CYCLONE III GL") || (device == "cyclone iii gl") || (device == "CycloneIII GL") || (device == "CYCLONEIII GL") || (device == "cycloneiii gl") || (device == "Cyclone IIIGL") || (device == "CYCLONE IIIGL") || (device == "cyclone iiigl") || (device == "CycloneIIIGL") || (device == "CYCLONEIIIGL") || (device == "cycloneiiigl") || (device == "Stingray") || (device == "STINGRAY") || (device == "stingray"))
        is_cycloneivgx = 1;
    else
        is_cycloneivgx = 0;

    IS_FAMILY_CYCLONEIVGX  = is_cycloneivgx;
end
endfunction //IS_FAMILY_CYCLONEIVGX

function IS_FAMILY_CYCLONEIVE;
    input[8*20:1] device;
    reg is_cycloneive;
begin
    if ((device == "Cyclone IV E") || (device == "CYCLONE IV E") || (device == "cyclone iv e") || (device == "CycloneIV E") || (device == "CYCLONEIV E") || (device == "cycloneiv e") || (device == "Cyclone IVE") || (device == "CYCLONE IVE") || (device == "cyclone ive") || (device == "CycloneIVE") || (device == "CYCLONEIVE") || (device == "cycloneive"))
        is_cycloneive = 1;
    else
        is_cycloneive = 0;

    IS_FAMILY_CYCLONEIVE  = is_cycloneive;
end
endfunction //IS_FAMILY_CYCLONEIVE

function IS_FAMILY_STRATIXV;
    input[8*20:1] device;
    reg is_stratixv;
begin
    if ((device == "Stratix V") || (device == "STRATIX V") || (device == "stratix v") || (device == "StratixV") || (device == "STRATIXV") || (device == "stratixv") || (device == "Stratix V (GS)") || (device == "STRATIX V (GS)") || (device == "stratix v (gs)") || (device == "StratixV(GS)") || (device == "STRATIXV(GS)") || (device == "stratixv(gs)") || (device == "Stratix V (GX)") || (device == "STRATIX V (GX)") || (device == "stratix v (gx)") || (device == "StratixV(GX)") || (device == "STRATIXV(GX)") || (device == "stratixv(gx)") || (device == "Stratix V (GS/GX)") || (device == "STRATIX V (GS/GX)") || (device == "stratix v (gs/gx)") || (device == "StratixV(GS/GX)") || (device == "STRATIXV(GS/GX)") || (device == "stratixv(gs/gx)") || (device == "Stratix V (GX/GS)") || (device == "STRATIX V (GX/GS)") || (device == "stratix v (gx/gs)") || (device == "StratixV(GX/GS)") || (device == "STRATIXV(GX/GS)") || (device == "stratixv(gx/gs)"))
        is_stratixv = 1;
    else
        is_stratixv = 0;

    IS_FAMILY_STRATIXV  = is_stratixv;
end
endfunction //IS_FAMILY_STRATIXV

function FEATURE_FAMILY_STRATIXGX;
    input[8*20:1] device;
    reg var_family_stratixgx;
begin
    if (IS_FAMILY_STRATIXGX(device) )
        var_family_stratixgx = 1;
    else
        var_family_stratixgx = 0;

    FEATURE_FAMILY_STRATIXGX  = var_family_stratixgx;
end
endfunction //FEATURE_FAMILY_STRATIXGX

function FEATURE_FAMILY_CYCLONE;
    input[8*20:1] device;
    reg var_family_cyclone;
begin
    if (IS_FAMILY_CYCLONE(device) )
        var_family_cyclone = 1;
    else
        var_family_cyclone = 0;

    FEATURE_FAMILY_CYCLONE  = var_family_cyclone;
end
endfunction //FEATURE_FAMILY_CYCLONE

function FEATURE_FAMILY_STRATIXIIGX;
    input[8*20:1] device;
    reg var_family_stratixiigx;
begin
    if (IS_FAMILY_STRATIXIIGX(device) || IS_FAMILY_ARRIAGX(device) )
        var_family_stratixiigx = 1;
    else
        var_family_stratixiigx = 0;

    FEATURE_FAMILY_STRATIXIIGX  = var_family_stratixiigx;
end
endfunction //FEATURE_FAMILY_STRATIXIIGX

function FEATURE_FAMILY_STRATIXIII;
    input[8*20:1] device;
    reg var_family_stratixiii;
begin
    if (IS_FAMILY_STRATIXIII(device) || FEATURE_FAMILY_STRATIXIV(device) || IS_FAMILY_HARDCOPYIII(device) )
        var_family_stratixiii = 1;
    else
        var_family_stratixiii = 0;

    FEATURE_FAMILY_STRATIXIII  = var_family_stratixiii;
end
endfunction //FEATURE_FAMILY_STRATIXIII

function FEATURE_FAMILY_STRATIXV;
    input[8*20:1] device;
    reg var_family_stratixv;
begin
    if (IS_FAMILY_STRATIXV(device) )
        var_family_stratixv = 1;
    else
        var_family_stratixv = 0;

    FEATURE_FAMILY_STRATIXV  = var_family_stratixv;
end
endfunction //FEATURE_FAMILY_STRATIXV

function FEATURE_FAMILY_STRATIXII;
    input[8*20:1] device;
    reg var_family_stratixii;
begin
    if (IS_FAMILY_STRATIXII(device) || IS_FAMILY_HARDCOPYII(device) || FEATURE_FAMILY_STRATIXIIGX(device) || FEATURE_FAMILY_STRATIXIII(device) )
        var_family_stratixii = 1;
    else
        var_family_stratixii = 0;

    FEATURE_FAMILY_STRATIXII  = var_family_stratixii;
end
endfunction //FEATURE_FAMILY_STRATIXII

function FEATURE_FAMILY_CYCLONEIVGX;
    input[8*20:1] device;
    reg var_family_cycloneivgx;
begin
    if (IS_FAMILY_CYCLONEIVGX(device) || IS_FAMILY_CYCLONEIVGX(device) )
        var_family_cycloneivgx = 1;
    else
        var_family_cycloneivgx = 0;

    FEATURE_FAMILY_CYCLONEIVGX  = var_family_cycloneivgx;
end
endfunction //FEATURE_FAMILY_CYCLONEIVGX

function FEATURE_FAMILY_CYCLONEIVE;
    input[8*20:1] device;
    reg var_family_cycloneive;
begin
    if (IS_FAMILY_CYCLONEIVE(device) )
        var_family_cycloneive = 1;
    else
        var_family_cycloneive = 0;

    FEATURE_FAMILY_CYCLONEIVE  = var_family_cycloneive;
end
endfunction //FEATURE_FAMILY_CYCLONEIVE

function FEATURE_FAMILY_CYCLONEIII;
    input[8*20:1] device;
    reg var_family_cycloneiii;
begin
    if (IS_FAMILY_CYCLONEIII(device) || IS_FAMILY_CYCLONEIIILS(device) || FEATURE_FAMILY_CYCLONEIVGX(device) || FEATURE_FAMILY_CYCLONEIVE(device) )
        var_family_cycloneiii = 1;
    else
        var_family_cycloneiii = 0;

    FEATURE_FAMILY_CYCLONEIII  = var_family_cycloneiii;
end
endfunction //FEATURE_FAMILY_CYCLONEIII

function FEATURE_FAMILY_STRATIX_HC;
    input[8*20:1] device;
    reg var_family_stratix_hc;
begin
    if ((device == "StratixHC") )
        var_family_stratix_hc = 1;
    else
        var_family_stratix_hc = 0;

    FEATURE_FAMILY_STRATIX_HC  = var_family_stratix_hc;
end
endfunction //FEATURE_FAMILY_STRATIX_HC

function FEATURE_FAMILY_HARDCOPYII;
    input[8*20:1] device;
    reg var_family_hardcopyii;
begin
    if (IS_FAMILY_HARDCOPYII(device) )
        var_family_hardcopyii = 1;
    else
        var_family_hardcopyii = 0;

    FEATURE_FAMILY_HARDCOPYII  = var_family_hardcopyii;
end
endfunction //FEATURE_FAMILY_HARDCOPYII

function FEATURE_FAMILY_STRATIX;
    input[8*20:1] device;
    reg var_family_stratix;
begin
    if (IS_FAMILY_STRATIX(device) || FEATURE_FAMILY_STRATIX_HC(device) || FEATURE_FAMILY_STRATIXGX(device) || FEATURE_FAMILY_CYCLONE(device) || FEATURE_FAMILY_STRATIXII(device) || FEATURE_FAMILY_MAXII(device) || FEATURE_FAMILY_CYCLONEII(device) )
        var_family_stratix = 1;
    else
        var_family_stratix = 0;

    FEATURE_FAMILY_STRATIX  = var_family_stratix;
end
endfunction //FEATURE_FAMILY_STRATIX

function FEATURE_FAMILY_MAXII;
    input[8*20:1] device;
    reg var_family_maxii;
begin
    if (IS_FAMILY_MAXII(device) )
        var_family_maxii = 1;
    else
        var_family_maxii = 0;

    FEATURE_FAMILY_MAXII  = var_family_maxii;
end
endfunction //FEATURE_FAMILY_MAXII

function FEATURE_FAMILY_CYCLONEII;
    input[8*20:1] device;
    reg var_family_cycloneii;
begin
    if (IS_FAMILY_CYCLONEII(device) || FEATURE_FAMILY_CYCLONEIII(device) )
        var_family_cycloneii = 1;
    else
        var_family_cycloneii = 0;

    FEATURE_FAMILY_CYCLONEII  = var_family_cycloneii;
end
endfunction //FEATURE_FAMILY_CYCLONEII

function FEATURE_FAMILY_STRATIXIV;
    input[8*20:1] device;
    reg var_family_stratixiv;
begin
    if (IS_FAMILY_STRATIXIV(device) || IS_FAMILY_ARRIAIIGX(device) || IS_FAMILY_HARDCOPYIV(device) || FEATURE_FAMILY_STRATIXV(device) )
        var_family_stratixiv = 1;
    else
        var_family_stratixiv = 0;

    FEATURE_FAMILY_STRATIXIV  = var_family_stratixiv;
end
endfunction //FEATURE_FAMILY_STRATIXIV

function FEATURE_FAMILY_ARRIAIIGX;
    input[8*20:1] device;
    reg var_family_arriaiigx;
begin
    if (IS_FAMILY_ARRIAIIGX(device) )
        var_family_arriaiigx = 1;
    else
        var_family_arriaiigx = 0;

    FEATURE_FAMILY_ARRIAIIGX  = var_family_arriaiigx;
end
endfunction //FEATURE_FAMILY_ARRIAIIGX

function FEATURE_FAMILY_HARDCOPYIII;
    input[8*20:1] device;
    reg var_family_hardcopyiii;
begin
    if (IS_FAMILY_HARDCOPYIII(device) || IS_FAMILY_HARDCOPYIII(device) )
        var_family_hardcopyiii = 1;
    else
        var_family_hardcopyiii = 0;

    FEATURE_FAMILY_HARDCOPYIII  = var_family_hardcopyiii;
end
endfunction //FEATURE_FAMILY_HARDCOPYIII

function FEATURE_FAMILY_HARDCOPYIV;
    input[8*20:1] device;
    reg var_family_hardcopyiv;
begin
    if (IS_FAMILY_HARDCOPYIV(device) || IS_FAMILY_HARDCOPYIV(device) )
        var_family_hardcopyiv = 1;
    else
        var_family_hardcopyiv = 0;

    FEATURE_FAMILY_HARDCOPYIV  = var_family_hardcopyiv;
end
endfunction //FEATURE_FAMILY_HARDCOPYIV

function FEATURE_FAMILY_BASE_STRATIXII;
    input[8*20:1] device;
    reg var_family_base_stratixii;
begin
    if (IS_FAMILY_STRATIXII(device) || IS_FAMILY_HARDCOPYII(device) || FEATURE_FAMILY_STRATIXIIGX(device) )
        var_family_base_stratixii = 1;
    else
        var_family_base_stratixii = 0;

    FEATURE_FAMILY_BASE_STRATIXII  = var_family_base_stratixii;
end
endfunction //FEATURE_FAMILY_BASE_STRATIXII

function FEATURE_FAMILY_BASE_STRATIX;
    input[8*20:1] device;
    reg var_family_base_stratix;
begin
    if (IS_FAMILY_STRATIX(device) || IS_FAMILY_STRATIXGX(device) )
        var_family_base_stratix = 1;
    else
        var_family_base_stratix = 0;

    FEATURE_FAMILY_BASE_STRATIX  = var_family_base_stratix;
end
endfunction //FEATURE_FAMILY_BASE_STRATIX

function FEATURE_FAMILY_BASE_CYCLONEII;
    input[8*20:1] device;
    reg var_family_base_cycloneii;
begin
    if (IS_FAMILY_CYCLONEII(device) )
        var_family_base_cycloneii = 1;
    else
        var_family_base_cycloneii = 0;

    FEATURE_FAMILY_BASE_CYCLONEII  = var_family_base_cycloneii;
end
endfunction //FEATURE_FAMILY_BASE_CYCLONEII

function FEATURE_FAMILY_BASE_CYCLONE;
    input[8*20:1] device;
    reg var_family_base_cyclone;
begin
    if (IS_FAMILY_CYCLONE(device) )
        var_family_base_cyclone = 1;
    else
        var_family_base_cyclone = 0;

    FEATURE_FAMILY_BASE_CYCLONE  = var_family_base_cyclone;
end
endfunction //FEATURE_FAMILY_BASE_CYCLONE

function FEATURE_FAMILY_HAS_MEGARAM;
    input[8*20:1] device;
    reg var_family_has_megaram;
begin
    if (IS_FAMILY_STRATIX(device) || FEATURE_FAMILY_STRATIX_HC(device) || IS_FAMILY_STRATIXGX(device) || FEATURE_FAMILY_STRATIXII(device) && ! FEATURE_FAMILY_ARRIAIIGX(device) && ! FEATURE_FAMILY_STRATIXV(device) )
        var_family_has_megaram = 1;
    else
        var_family_has_megaram = 0;

    FEATURE_FAMILY_HAS_MEGARAM  = var_family_has_megaram;
end
endfunction //FEATURE_FAMILY_HAS_MEGARAM

function FEATURE_FAMILY_HAS_M512;
    input[8*20:1] device;
    reg var_family_has_m512;
begin
    if (IS_FAMILY_STRATIX(device) || FEATURE_FAMILY_STRATIX_HC(device) || IS_FAMILY_STRATIXGX(device) || IS_FAMILY_STRATIXII(device) || FEATURE_FAMILY_STRATIXIIGX(device) )
        var_family_has_m512 = 1;
    else
        var_family_has_m512 = 0;

    FEATURE_FAMILY_HAS_M512  = var_family_has_m512;
end
endfunction //FEATURE_FAMILY_HAS_M512

function FEATURE_FAMILY_HAS_LUTRAM;
    input[8*20:1] device;
    reg var_family_has_lutram;
begin
    if (FEATURE_FAMILY_STRATIXIII(device) || FEATURE_FAMILY_STRATIXV(device) )
        var_family_has_lutram = 1;
    else
        var_family_has_lutram = 0;

    FEATURE_FAMILY_HAS_LUTRAM  = var_family_has_lutram;
end
endfunction //FEATURE_FAMILY_HAS_LUTRAM

function FEATURE_FAMILY_HAS_STRATIXI_STYLE_RAM;
    input[8*20:1] device;
    reg var_family_has_stratixi_style_ram;
begin
    if (IS_FAMILY_STRATIX(device) || FEATURE_FAMILY_STRATIX_HC(device) || FEATURE_FAMILY_STRATIXGX(device) || FEATURE_FAMILY_CYCLONE(device) )
        var_family_has_stratixi_style_ram = 1;
    else
        var_family_has_stratixi_style_ram = 0;

    FEATURE_FAMILY_HAS_STRATIXI_STYLE_RAM  = var_family_has_stratixi_style_ram;
end
endfunction //FEATURE_FAMILY_HAS_STRATIXI_STYLE_RAM

function FEATURE_FAMILY_HAS_STRATIXII_STYLE_RAM;
    input[8*20:1] device;
    reg var_family_has_stratixii_style_ram;
begin
    if (FEATURE_FAMILY_STRATIXII(device) || FEATURE_FAMILY_CYCLONEII(device) )
        var_family_has_stratixii_style_ram = 1;
    else
        var_family_has_stratixii_style_ram = 0;

    FEATURE_FAMILY_HAS_STRATIXII_STYLE_RAM  = var_family_has_stratixii_style_ram;
end
endfunction //FEATURE_FAMILY_HAS_STRATIXII_STYLE_RAM

function FEATURE_FAMILY_HAS_STRATIXIII_STYLE_RAM;
    input[8*20:1] device;
    reg var_family_has_stratixiii_style_ram;
begin
    if (FEATURE_FAMILY_STRATIXIII(device) || FEATURE_FAMILY_CYCLONEIII(device) )
        var_family_has_stratixiii_style_ram = 1;
    else
        var_family_has_stratixiii_style_ram = 0;

    FEATURE_FAMILY_HAS_STRATIXIII_STYLE_RAM  = var_family_has_stratixiii_style_ram;
end
endfunction //FEATURE_FAMILY_HAS_STRATIXIII_STYLE_RAM

function FEATURE_FAMILY_HAS_STRATIXV_STYLE_RAM;
    input[8*20:1] device;
    reg var_family_has_stratixv_style_ram;
begin
    if (FEATURE_FAMILY_STRATIXV(device) )
        var_family_has_stratixv_style_ram = 1;
    else
        var_family_has_stratixv_style_ram = 0;

    FEATURE_FAMILY_HAS_STRATIXV_STYLE_RAM  = var_family_has_stratixv_style_ram;
end
endfunction //FEATURE_FAMILY_HAS_STRATIXV_STYLE_RAM

function FEATURE_FAMILY_HAS_STRATIX_STYLE_PLL;
    input[8*20:1] device;
    reg var_family_has_stratix_style_pll;
begin
    if (FEATURE_FAMILY_CYCLONE(device) || FEATURE_FAMILY_STRATIX_HC(device) || IS_FAMILY_STRATIX(device) || FEATURE_FAMILY_STRATIXGX(device) )
        var_family_has_stratix_style_pll = 1;
    else
        var_family_has_stratix_style_pll = 0;

    FEATURE_FAMILY_HAS_STRATIX_STYLE_PLL  = var_family_has_stratix_style_pll;
end
endfunction //FEATURE_FAMILY_HAS_STRATIX_STYLE_PLL

function FEATURE_FAMILY_HAS_STRATIXII_STYLE_PLL;
    input[8*20:1] device;
    reg var_family_has_stratixii_style_pll;
begin
    if (FEATURE_FAMILY_STRATIXII(device) && ! FEATURE_FAMILY_STRATIXIII(device) || FEATURE_FAMILY_CYCLONEII(device) && ! FEATURE_FAMILY_CYCLONEIII(device) )
        var_family_has_stratixii_style_pll = 1;
    else
        var_family_has_stratixii_style_pll = 0;

    FEATURE_FAMILY_HAS_STRATIXII_STYLE_PLL  = var_family_has_stratixii_style_pll;
end
endfunction //FEATURE_FAMILY_HAS_STRATIXII_STYLE_PLL

function FEATURE_FAMILY_HAS_INVERTED_OUTPUT_DDIO;
    input[8*20:1] device;
    reg var_family_has_inverted_output_ddio;
begin
    if (FEATURE_FAMILY_CYCLONEII(device) )
        var_family_has_inverted_output_ddio = 1;
    else
        var_family_has_inverted_output_ddio = 0;

    FEATURE_FAMILY_HAS_INVERTED_OUTPUT_DDIO  = var_family_has_inverted_output_ddio;
end
endfunction //FEATURE_FAMILY_HAS_INVERTED_OUTPUT_DDIO

function IS_VALID_FAMILY;
    input[8*20:1] device;
    reg is_valid;
begin
    if (((device == "MAX7000B") || (device == "max7000b") || (device == "MAX 7000B") || (device == "max 7000b"))
    || ((device == "MAX7000AE") || (device == "max7000ae") || (device == "MAX 7000AE") || (device == "max 7000ae"))
    || ((device == "MAX3000A") || (device == "max3000a") || (device == "MAX 3000A") || (device == "max 3000a"))
    || ((device == "MAX7000S") || (device == "max7000s") || (device == "MAX 7000S") || (device == "max 7000s"))
    || ((device == "Stratix") || (device == "STRATIX") || (device == "stratix") || (device == "Yeager") || (device == "YEAGER") || (device == "yeager"))
    || ((device == "Stratix GX") || (device == "STRATIX GX") || (device == "stratix gx") || (device == "Stratix-GX") || (device == "STRATIX-GX") || (device == "stratix-gx") || (device == "StratixGX") || (device == "STRATIXGX") || (device == "stratixgx") || (device == "Aurora") || (device == "AURORA") || (device == "aurora"))
    || ((device == "Cyclone") || (device == "CYCLONE") || (device == "cyclone") || (device == "ACEX2K") || (device == "acex2k") || (device == "ACEX 2K") || (device == "acex 2k") || (device == "Tornado") || (device == "TORNADO") || (device == "tornado"))
    || ((device == "MAX II") || (device == "max ii") || (device == "MAXII") || (device == "maxii") || (device == "Tsunami") || (device == "TSUNAMI") || (device == "tsunami"))
    || ((device == "Stratix II") || (device == "STRATIX II") || (device == "stratix ii") || (device == "StratixII") || (device == "STRATIXII") || (device == "stratixii") || (device == "Armstrong") || (device == "ARMSTRONG") || (device == "armstrong"))
    || ((device == "Stratix II GX") || (device == "STRATIX II GX") || (device == "stratix ii gx") || (device == "StratixIIGX") || (device == "STRATIXIIGX") || (device == "stratixiigx"))
    || ((device == "Arria GX") || (device == "ARRIA GX") || (device == "arria gx") || (device == "ArriaGX") || (device == "ARRIAGX") || (device == "arriagx") || (device == "Stratix II GX Lite") || (device == "STRATIX II GX LITE") || (device == "stratix ii gx lite") || (device == "StratixIIGXLite") || (device == "STRATIXIIGXLITE") || (device == "stratixiigxlite"))
    || ((device == "Cyclone II") || (device == "CYCLONE II") || (device == "cyclone ii") || (device == "Cycloneii") || (device == "CYCLONEII") || (device == "cycloneii") || (device == "Magellan") || (device == "MAGELLAN") || (device == "magellan"))
    || ((device == "HardCopy II") || (device == "HARDCOPY II") || (device == "hardcopy ii") || (device == "HardCopyII") || (device == "HARDCOPYII") || (device == "hardcopyii") || (device == "Fusion") || (device == "FUSION") || (device == "fusion"))
    || ((device == "Stratix III") || (device == "STRATIX III") || (device == "stratix iii") || (device == "StratixIII") || (device == "STRATIXIII") || (device == "stratixiii") || (device == "Titan") || (device == "TITAN") || (device == "titan") || (device == "SIII") || (device == "siii"))
    || ((device == "Cyclone III") || (device == "CYCLONE III") || (device == "cyclone iii") || (device == "CycloneIII") || (device == "CYCLONEIII") || (device == "cycloneiii") || (device == "Barracuda") || (device == "BARRACUDA") || (device == "barracuda") || (device == "Cuda") || (device == "CUDA") || (device == "cuda") || (device == "CIII") || (device == "ciii"))
    || ((device == "BS") || (device == "bs"))
    || ((device == "Stratix IV") || (device == "STRATIX IV") || (device == "stratix iv") || (device == "TGX") || (device == "tgx") || (device == "StratixIV") || (device == "STRATIXIV") || (device == "stratixiv") || (device == "Stratix IV (GT)") || (device == "STRATIX IV (GT)") || (device == "stratix iv (gt)") || (device == "Stratix IV (GX)") || (device == "STRATIX IV (GX)") || (device == "stratix iv (gx)") || (device == "Stratix IV (E)") || (device == "STRATIX IV (E)") || (device == "stratix iv (e)") || (device == "StratixIV(GT)") || (device == "STRATIXIV(GT)") || (device == "stratixiv(gt)") || (device == "StratixIV(GX)") || (device == "STRATIXIV(GX)") || (device == "stratixiv(gx)") || (device == "StratixIV(E)") || (device == "STRATIXIV(E)") || (device == "stratixiv(e)") || (device == "StratixIIIGX") || (device == "STRATIXIIIGX") || (device == "stratixiiigx") || (device == "Stratix IV (GT/GX/E)") || (device == "STRATIX IV (GT/GX/E)") || (device == "stratix iv (gt/gx/e)") || (device == "Stratix IV (GT/E/GX)") || (device == "STRATIX IV (GT/E/GX)") || (device == "stratix iv (gt/e/gx)") || (device == "Stratix IV (E/GT/GX)") || (device == "STRATIX IV (E/GT/GX)") || (device == "stratix iv (e/gt/gx)") || (device == "Stratix IV (E/GX/GT)") || (device == "STRATIX IV (E/GX/GT)") || (device == "stratix iv (e/gx/gt)") || (device == "StratixIV(GT/GX/E)") || (device == "STRATIXIV(GT/GX/E)") || (device == "stratixiv(gt/gx/e)") || (device == "StratixIV(GT/E/GX)") || (device == "STRATIXIV(GT/E/GX)") || (device == "stratixiv(gt/e/gx)") || (device == "StratixIV(E/GX/GT)") || (device == "STRATIXIV(E/GX/GT)") || (device == "stratixiv(e/gx/gt)") || (device == "StratixIV(E/GT/GX)") || (device == "STRATIXIV(E/GT/GX)") || (device == "stratixiv(e/gt/gx)") || (device == "Stratix IV (GX/E)") || (device == "STRATIX IV (GX/E)") || (device == "stratix iv (gx/e)") || (device == "StratixIV(GX/E)") || (device == "STRATIXIV(GX/E)") || (device == "stratixiv(gx/e)"))
    || ((device == "Arria II GX") || (device == "ARRIA II GX") || (device == "arria ii gx") || (device == "ArriaIIGX") || (device == "ARRIAIIGX") || (device == "arriaiigx") || (device == "Arria IIGX") || (device == "ARRIA IIGX") || (device == "arria iigx") || (device == "ArriaII GX") || (device == "ARRIAII GX") || (device == "arriaii gx") || (device == "Arria II") || (device == "ARRIA II") || (device == "arria ii") || (device == "ArriaII") || (device == "ARRIAII") || (device == "arriaii") || (device == "Arria II (GX/E)") || (device == "ARRIA II (GX/E)") || (device == "arria ii (gx/e)") || (device == "ArriaII(GX/E)") || (device == "ARRIAII(GX/E)") || (device == "arriaii(gx/e)") || (device == "PIRANHA") || (device == "piranha"))
    || ((device == "HardCopy III") || (device == "HARDCOPY III") || (device == "hardcopy iii") || (device == "HardCopyIII") || (device == "HARDCOPYIII") || (device == "hardcopyiii") || (device == "HCX") || (device == "hcx"))
    || ((device == "HardCopy IV") || (device == "HARDCOPY IV") || (device == "hardcopy iv") || (device == "HardCopyIV") || (device == "HARDCOPYIV") || (device == "hardcopyiv") || (device == "HardCopy IV (GX)") || (device == "HARDCOPY IV (GX)") || (device == "hardcopy iv (gx)") || (device == "HardCopy IV (E)") || (device == "HARDCOPY IV (E)") || (device == "hardcopy iv (e)") || (device == "HardCopyIV(GX)") || (device == "HARDCOPYIV(GX)") || (device == "hardcopyiv(gx)") || (device == "HardCopyIV(E)") || (device == "HARDCOPYIV(E)") || (device == "hardcopyiv(e)") || (device == "HCXIV") || (device == "hcxiv") || (device == "HardCopy IV (GX/E)") || (device == "HARDCOPY IV (GX/E)") || (device == "hardcopy iv (gx/e)") || (device == "HardCopy IV (E/GX)") || (device == "HARDCOPY IV (E/GX)") || (device == "hardcopy iv (e/gx)") || (device == "HardCopyIV(GX/E)") || (device == "HARDCOPYIV(GX/E)") || (device == "hardcopyiv(gx/e)") || (device == "HardCopyIV(E/GX)") || (device == "HARDCOPYIV(E/GX)") || (device == "hardcopyiv(e/gx)"))
    || ((device == "Cyclone III LS") || (device == "CYCLONE III LS") || (device == "cyclone iii ls") || (device == "CycloneIIILS") || (device == "CYCLONEIIILS") || (device == "cycloneiiils") || (device == "Cyclone III LPS") || (device == "CYCLONE III LPS") || (device == "cyclone iii lps") || (device == "Cyclone LPS") || (device == "CYCLONE LPS") || (device == "cyclone lps") || (device == "CycloneLPS") || (device == "CYCLONELPS") || (device == "cyclonelps") || (device == "Tarpon") || (device == "TARPON") || (device == "tarpon") || (device == "Cyclone IIIE") || (device == "CYCLONE IIIE") || (device == "cyclone iiie"))
    || ((device == "Cyclone IV GX") || (device == "CYCLONE IV GX") || (device == "cyclone iv gx") || (device == "Cyclone IVGX") || (device == "CYCLONE IVGX") || (device == "cyclone ivgx") || (device == "CycloneIV GX") || (device == "CYCLONEIV GX") || (device == "cycloneiv gx") || (device == "CycloneIVGX") || (device == "CYCLONEIVGX") || (device == "cycloneivgx") || (device == "Cyclone IV") || (device == "CYCLONE IV") || (device == "cyclone iv") || (device == "CycloneIV") || (device == "CYCLONEIV") || (device == "cycloneiv") || (device == "Cyclone IV (GX)") || (device == "CYCLONE IV (GX)") || (device == "cyclone iv (gx)") || (device == "CycloneIV(GX)") || (device == "CYCLONEIV(GX)") || (device == "cycloneiv(gx)") || (device == "Cyclone III GX") || (device == "CYCLONE III GX") || (device == "cyclone iii gx") || (device == "CycloneIII GX") || (device == "CYCLONEIII GX") || (device == "cycloneiii gx") || (device == "Cyclone IIIGX") || (device == "CYCLONE IIIGX") || (device == "cyclone iiigx") || (device == "CycloneIIIGX") || (device == "CYCLONEIIIGX") || (device == "cycloneiiigx") || (device == "Cyclone III GL") || (device == "CYCLONE III GL") || (device == "cyclone iii gl") || (device == "CycloneIII GL") || (device == "CYCLONEIII GL") || (device == "cycloneiii gl") || (device == "Cyclone IIIGL") || (device == "CYCLONE IIIGL") || (device == "cyclone iiigl") || (device == "CycloneIIIGL") || (device == "CYCLONEIIIGL") || (device == "cycloneiiigl") || (device == "Stingray") || (device == "STINGRAY") || (device == "stingray"))
    || ((device == "Cyclone IV E") || (device == "CYCLONE IV E") || (device == "cyclone iv e") || (device == "CycloneIV E") || (device == "CYCLONEIV E") || (device == "cycloneiv e") || (device == "Cyclone IVE") || (device == "CYCLONE IVE") || (device == "cyclone ive") || (device == "CycloneIVE") || (device == "CYCLONEIVE") || (device == "cycloneive"))
    || ((device == "Stratix V") || (device == "STRATIX V") || (device == "stratix v") || (device == "StratixV") || (device == "STRATIXV") || (device == "stratixv") || (device == "Stratix V (GS)") || (device == "STRATIX V (GS)") || (device == "stratix v (gs)") || (device == "StratixV(GS)") || (device == "STRATIXV(GS)") || (device == "stratixv(gs)") || (device == "Stratix V (GX)") || (device == "STRATIX V (GX)") || (device == "stratix v (gx)") || (device == "StratixV(GX)") || (device == "STRATIXV(GX)") || (device == "stratixv(gx)") || (device == "Stratix V (GS/GX)") || (device == "STRATIX V (GS/GX)") || (device == "stratix v (gs/gx)") || (device == "StratixV(GS/GX)") || (device == "STRATIXV(GS/GX)") || (device == "stratixv(gs/gx)") || (device == "Stratix V (GX/GS)") || (device == "STRATIX V (GX/GS)") || (device == "stratix v (gx/gs)") || (device == "StratixV(GX/GS)") || (device == "STRATIXV(GX/GS)") || (device == "stratixv(gx/gs)")))
        is_valid = 1;
    else
        is_valid = 0;

    IS_VALID_FAMILY = is_valid;
end
endfunction // IS_VALID_FAMILY


endmodule // ALTERA_DEVICE_FAMILIES


module ALTERA_MF_HINT_EVALUATION;

// FUNCTON DECLARATION

// This function will search through the string (given string) to look for a match for the
// a given parameter(compare_param_name). It will return the value for the given parameter.
function [8*200:1] GET_PARAMETER_VALUE;
    input [8*200:1] given_string;  // string to be searched
    input [8*50:1] compare_param_name; // parameter name to be looking for in the given_string.
    integer param_value_char_count; // to indicate current character count in the param_value
    integer param_name_char_count;  // to indicate current character count in the param_name
    integer white_space_count;

    reg extract_param_value; // if 1 mean extracting parameters value from given string
    reg extract_param_name;  // if 1 mean extracting parameters name from given string
    reg param_found; // to indicate whether compare_param_name have been found in the given_string
    reg include_white_space; // if 1, include white space in the parameter value

    reg [8*200:1] reg_string; // to store the value of the given string
    reg [8*50:1] param_name;  // to store parameter name
    reg [8*20:1] param_value; // to store parameter value
    reg [8:1] tmp; // to get the value of the current byte
begin
    reg_string = given_string;
    param_value_char_count = 0;
    param_name_char_count =0;
    extract_param_value = 1;
    extract_param_name = 0;
    param_found = 0;
    include_white_space = 0;
    white_space_count = 0;

    tmp = reg_string[8:1];

    // checking every bytes of the reg_string from right to left.
    while ((tmp != 0 ) && (param_found != 1))
    begin
        tmp = reg_string[8:1];

        //if tmp != ' ' or should include white space (trailing white space are ignored)
        if((tmp != 32) || (include_white_space == 1))
        begin
            if(tmp == 32)
            begin
                white_space_count = 1;
            end
            else if(tmp == 61)  // if tmp = '='
            begin
                extract_param_value = 0;
                extract_param_name =  1;  // subsequent bytes should be part of param_name
                include_white_space = 0;  // ignore the white space (if any) between param_name and '='
                white_space_count = 0;
                param_value = param_value >> (8 * (20 - param_value_char_count));
                param_value_char_count = 0;
            end
            else if (tmp == 44) // if tmp = ','
            begin
                extract_param_value = 1; // subsequent bytes should be part of param_value
                extract_param_name =  0;
                param_name = param_name >> (8 * (50 - param_name_char_count));
                param_name_char_count = 0;
                if(param_name == compare_param_name)
                    param_found = 1;  // the compare_param_name have been found in the reg_string
            end
            else
            begin
                if(extract_param_value == 1)
                begin
                    param_value_char_count = param_value_char_count + white_space_count + 1;
                    include_white_space = 1;
                    if(white_space_count > 0)
                    begin
                        param_value = {8'b100000, param_value[20*8:9]};
                        white_space_count = 0;
                    end
                    param_value = {tmp, param_value[20*8:9]};
                end
                else if(extract_param_name == 1)
                begin
                    param_name = {tmp, param_name[50*8:9]};
                    param_name_char_count = param_name_char_count + 1;
                end
            end
        end
        reg_string = reg_string >> 8;  // shift 1 byte to the right
    end

    // for the case whether param_name is the left most part of the reg_string
    if(extract_param_name == 1)
    begin
        param_name = param_name >> (8 * (50 - param_name_char_count));

        if(param_name == compare_param_name)
            param_found = 1;
    end

    if (param_found == 1)
        GET_PARAMETER_VALUE = param_value;   // return the value of the parameter been looking for
    else
        GET_PARAMETER_VALUE = "";  // return empty string if parameter not found

end
endfunction

endmodule // ALTERA_MF_HINT_EVALUATION
