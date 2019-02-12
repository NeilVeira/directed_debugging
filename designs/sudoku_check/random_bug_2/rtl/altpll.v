
///////////////////////////////////////////////////////////////////////////////
//
//                             STRATIX_PLL and STRATIXII_PLL
//
///////////////////////////////////////////////////////////////////////////////

// DFFP
`timescale 1ps / 1ps
module dffp ( 
    q, 
    clk, 
    ena, 
    d, 
    clrn, 
    prn );

    input d;
    input clk;
    input clrn;
    input prn;
    input ena;
    output q;


    tri1 prn, clrn, ena;
    reg q;

    always @ (posedge clk or negedge clrn or negedge prn )
        if (prn == 1'b0) 
            q <= 1;
        else if (clrn == 1'b0) 
            q <= 0;
        else
        begin
            if (ena == 1'b1)
                q <= d;
        end
    endmodule

// pll_iobuf
`timescale 1 ps / 1 ps
module pll_iobuf (i, oe, io, o);
    input i;
    input oe;
    inout io;
    output o;
    reg    o;
    
    always @(io)
    begin
        o = io;
    end

    assign io = (oe == 1) ? i : 1'bz;
endmodule    


///////////////////////////////////////////////////////////////////////////////
//
// Module Name : stx_m_cntr
//
// Description : Simulation model for the M counter. This is the
//               loop feedback counter for the Stratix PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module stx_m_cntr  (clk,
                        reset,
                        cout,
                        initial_value,
                        modulus,
                        time_delay);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] initial_value;
    input [31:0] modulus;
    input [31:0] time_delay;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'b1 && first_rising_edge)
                begin
                    first_rising_edge = 0;
                    tmp_cout = clk;
                end
                else if (first_rising_edge == 0)
                begin
                    if (count < modulus)
                        count = count + 1;
                    else
                    begin
                        count = 1;
                        tmp_cout = ~tmp_cout;
                    end
                end
            end
        end
        clk_last_value = clk;

        cout_tmp <= #(time_delay) tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // stx_m_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : stx_n_cntr
//
// Description : Simulation model for the N counter. This is the
//               input clock divide counter for the Stratix PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module stx_n_cntr  (clk,
                        reset,
                        cout,
                        modulus,
                        time_delay);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] modulus;
    input [31:0] time_delay;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg clk_last_valid_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'bx)
                begin
                    $display("Warning : Invalid transition to 'X' detected on PLL input clk. This edge will be ignored.");
                    $display("Time: %0t  Instance: %m", $time);
                end
                else if ((clk === 1'b1) && first_rising_edge)
                begin
                    first_rising_edge = 0;
                    tmp_cout = clk;
                end
                else if ((first_rising_edge == 0) && (clk_last_valid_value !== clk))
                begin
                    if (count < modulus)
                        count = count + 1;
                    else
                    begin
                        count = 1;
                        tmp_cout = ~tmp_cout;
                    end
                end
            end
        end
        clk_last_value = clk;
        if (clk !== 1'bx)
            clk_last_valid_value = clk;

        cout_tmp <= #(time_delay) tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // stx_n_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : stx_scale_cntr
//
// Description : Simulation model for the output scale-down counters.
//               This is a common model for the L0, L1, G0, G1, G2, G3, E0,
//               E1, E2 and E3 output counters of the Stratix PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module stx_scale_cntr  (clk,
                            reset,
                            cout,
                            high,
                            low,
                            initial_value,
                            mode,
                            time_delay,
                            ph_tap);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] high;
    input [31:0] low;
    input [31:0] initial_value;
    input [8*6:1] mode;
    input [31:0] time_delay;
    input [31:0] ph_tap;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg init;
    integer count;
    integer output_shift_count;
    reg cout_tmp;
    reg [31:0] high_reg;
    reg [31:0] low_reg;
    reg high_cnt_xfer_done;

    initial
    begin
        count = 1;
        first_rising_edge = 0;
        tmp_cout = 0;
        output_shift_count = 0;
        high_cnt_xfer_done = 0;
    end

    always @(clk or reset)
    begin
        if (init !== 1'b1)
        begin
            high_reg = high;
            low_reg = low;
            clk_last_value = 0;
            init = 1'b1;
        end
        if (reset)
        begin
            count = 1;
            output_shift_count = 0;
            tmp_cout = 0;
            first_rising_edge = 0;
        end
        else if (clk_last_value !== clk)
        begin
            if (mode == "off")
                tmp_cout = 0;
            else if (mode == "bypass")
                tmp_cout = clk;
            else if (first_rising_edge == 0)
            begin
                if (clk == 1)
                begin
                    output_shift_count = output_shift_count + 1;
                    if (output_shift_count == initial_value)
                    begin
                        tmp_cout = clk;
                        first_rising_edge = 1;
                    end
                end
            end
            else if (output_shift_count < initial_value)
            begin
                if (clk == 1)
                    output_shift_count = output_shift_count + 1;
            end
            else
            begin
                count = count + 1;
                if (mode == "even" && (count == (high_reg*2) + 1))
                begin
                    tmp_cout = 0;
                    if (high_cnt_xfer_done === 1'b1)
                    begin
                        low_reg = low;
                        high_cnt_xfer_done = 0;
                    end
                end
                else if (mode == "odd" && (count == (high_reg*2)))
                begin
                    tmp_cout = 0;
                    if (high_cnt_xfer_done === 1'b1)
                    begin
                        low_reg = low;
                        high_cnt_xfer_done = 0;
                    end
                end
                else if (count == (high_reg + low_reg)*2 + 1)
                begin
                    tmp_cout = 1;
                    count = 1;        // reset count
                    if (high_reg != high)
                    begin
                        high_reg = high;
                        high_cnt_xfer_done = 1;
                    end
                end
            end
        end
        clk_last_value = clk;
        cout_tmp <= #(time_delay) tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // stx_scale_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_pll_reg
//
// Description : Simulation model for a simple DFF.
//               This is required for the generation of the bit slip-signals.
//               No timing, powers upto 0.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1ps / 1ps
module MF_pll_reg (q,
                        clk,
                        ena,
                        d,
                        clrn,
                        prn);

    // INPUT PORTS
    input d;
    input clk;
    input clrn;
    input prn;
    input ena;

    // OUTPUT PORTS
    output q;

    // INTERNAL VARIABLES
    reg q;

    // DEFAULT VALUES THRO' PULLUPs
    tri1 prn, clrn, ena;

    initial q = 0;

    always @ (posedge clk or negedge clrn or negedge prn )
    begin
        if (prn == 1'b0)
            q <= 1;
        else if (clrn == 1'b0)
            q <= 0;
        else if ((clk == 1) & (ena == 1'b1))
            q <= d;
    end

endmodule // MF_pll_reg

//////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_stratix_pll
//
// Description : The behavioral model for Stratix PLL.
// 
// Limitations : Applies to the Stratix and Stratix GX device families
//               No support for spread spectrum feature in the model
//
// Outputs     : Up to 10 output clocks, each defined by its own set of
//               parameters. Locked output (active high) indicates when the
//               PLL locks. clkbad, clkloss and activeclock are used for
//               clock switchover to indicate which input clock has gone
//               bad, when the clock switchover initiates and which input
//               clock is being used as the reference, respectively.
//               scandataout is the data output of the serial scan chain.
//
//////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps
`define STX_PLL_WORD_LENGTH 18

module MF_stratix_pll (inclk,
                    fbin,
                    ena,
                    clkswitch,
                    areset,
                    pfdena,
                    clkena,
                    extclkena,
                    scanclk,
                    scanaclr,
                    scandata,
                    clk,
                    extclk,
                    clkbad,
                    activeclock,
                    locked,
                    clkloss,
                    scandataout,
                    // lvds mode specific ports
                    comparator,
                    enable0,
                    enable1);

    parameter operation_mode = "normal";
    parameter qualify_conf_done = "off";
    parameter compensate_clock = "clk0";
    parameter pll_type = "auto";
    parameter scan_chain = "long";

    parameter clk0_multiply_by = 1;
    parameter clk0_divide_by = 1;
    parameter clk0_phase_shift = 0;
    parameter clk0_time_delay = 0;
    parameter clk0_duty_cycle = 50;

    parameter clk1_multiply_by = 1;
    parameter clk1_divide_by = 1;
    parameter clk1_phase_shift = 0;
    parameter clk1_time_delay = 0;
    parameter clk1_duty_cycle = 50;

    parameter clk2_multiply_by = 1;
    parameter clk2_divide_by = 1;
    parameter clk2_phase_shift = 0;
    parameter clk2_time_delay = 0;
    parameter clk2_duty_cycle = 50;

    parameter clk3_multiply_by = 1;
    parameter clk3_divide_by = 1;
    parameter clk3_phase_shift = 0;
    parameter clk3_time_delay = 0;
    parameter clk3_duty_cycle = 50;

    parameter clk4_multiply_by = 1;
    parameter clk4_divide_by = 1;
    parameter clk4_phase_shift = 0;
    parameter clk4_time_delay = 0;
    parameter clk4_duty_cycle = 50;

    parameter clk5_multiply_by = 1;
    parameter clk5_divide_by = 1;
    parameter clk5_phase_shift = 0;
    parameter clk5_time_delay = 0;
    parameter clk5_duty_cycle = 50;

    parameter extclk0_multiply_by = 1;
    parameter extclk0_divide_by = 1;
    parameter extclk0_phase_shift = 0;
    parameter extclk0_time_delay = 0;
    parameter extclk0_duty_cycle = 50;

    parameter extclk1_multiply_by = 1;
    parameter extclk1_divide_by = 1;
    parameter extclk1_phase_shift = 0;
    parameter extclk1_time_delay = 0;
    parameter extclk1_duty_cycle = 50;

    parameter extclk2_multiply_by = 1;
    parameter extclk2_divide_by = 1;
    parameter extclk2_phase_shift = 0;
    parameter extclk2_time_delay = 0;
    parameter extclk2_duty_cycle = 50;

    parameter extclk3_multiply_by = 1;
    parameter extclk3_divide_by = 1;
    parameter extclk3_phase_shift = 0;
    parameter extclk3_time_delay = 0;
    parameter extclk3_duty_cycle = 50;

    parameter primary_clock = "inclk0";
    parameter inclk0_input_frequency = 10000;
    parameter inclk1_input_frequency = 10000;
    parameter gate_lock_signal = "no";
    parameter gate_lock_counter = 1;
    parameter valid_lock_multiplier = 5;
    parameter invalid_lock_multiplier = 5;

    parameter switch_over_on_lossclk = "off";
    parameter switch_over_on_gated_lock = "off";
    parameter switch_over_counter = 1;
    parameter enable_switch_over_counter = "off";
    parameter feedback_source = "extclk0";
    parameter bandwidth = 0;
    parameter bandwidth_type = "auto";
    parameter spread_frequency = 0;
    parameter common_rx_tx = "off";
    parameter rx_outclock_resource = "auto";
    parameter use_vco_bypass = "false";
    parameter use_dc_coupling = "false";

    parameter pfd_min = 0;
    parameter pfd_max = 0;
    parameter vco_min = 0;
    parameter vco_max = 0;
    parameter vco_center = 0;

    // ADVANCED USE PARAMETERS
    parameter m_initial = 1;
    parameter m = 0;
    parameter n = 1;
    parameter m2 = 1;
    parameter n2 = 1;
    parameter ss = 0;

    parameter l0_high = 1;
    parameter l0_low = 1;
    parameter l0_initial = 1;
    parameter l0_mode = "bypass";
    parameter l0_ph = 0;
    parameter l0_time_delay = 0;

    parameter l1_high = 1;
    parameter l1_low = 1;
    parameter l1_initial = 1;
    parameter l1_mode = "bypass";
    parameter l1_ph = 0;
    parameter l1_time_delay = 0;

    parameter g0_high = 1;
    parameter g0_low = 1;
    parameter g0_initial = 1;
    parameter g0_mode = "bypass";
    parameter g0_ph = 0;
    parameter g0_time_delay = 0;

    parameter g1_high = 1;
    parameter g1_low = 1;
    parameter g1_initial = 1;
    parameter g1_mode = "bypass";
    parameter g1_ph = 0;
    parameter g1_time_delay = 0;

    parameter g2_high = 1;
    parameter g2_low = 1;
    parameter g2_initial = 1;
    parameter g2_mode = "bypass";
    parameter g2_ph = 0;
    parameter g2_time_delay = 0;

    parameter g3_high = 1;
    parameter g3_low = 1;
    parameter g3_initial = 1;
    parameter g3_mode = "bypass";
    parameter g3_ph = 0;
    parameter g3_time_delay = 0;

    parameter e0_high = 1;
    parameter e0_low = 1;
    parameter e0_initial = 1;
    parameter e0_mode = "bypass";
    parameter e0_ph = 0;
    parameter e0_time_delay = 0;

    parameter e1_high = 1;
    parameter e1_low = 1;
    parameter e1_initial = 1;
    parameter e1_mode = "bypass";
    parameter e1_ph = 0;
    parameter e1_time_delay = 0;

    parameter e2_high = 1;
    parameter e2_low = 1;
    parameter e2_initial = 1;
    parameter e2_mode = "bypass";
    parameter e2_ph = 0;
    parameter e2_time_delay = 0;

    parameter e3_high = 1;
    parameter e3_low = 1;
    parameter e3_initial = 1;
    parameter e3_mode = "bypass";
    parameter e3_ph = 0;
    parameter e3_time_delay = 0;

    parameter m_ph = 0;
    parameter m_time_delay = 0;
    parameter n_time_delay = 0;

    parameter extclk0_counter = "e0";
    parameter extclk1_counter = "e1";
    parameter extclk2_counter = "e2";
    parameter extclk3_counter = "e3";

    parameter clk0_counter = "g0";
    parameter clk1_counter = "g1";
    parameter clk2_counter = "g2";
    parameter clk3_counter = "g3";
    parameter clk4_counter = "l0";
    parameter clk5_counter = "l1";

    // LVDS mode parameters
    parameter enable0_counter = "l0";
    parameter enable1_counter = "l0";

    parameter charge_pump_current = 0;
    parameter loop_filter_r = "1.0";
    parameter loop_filter_c = 1;

    parameter pll_compensation_delay = 0;
    parameter simulation_type = "timing";

// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter down_spread = "0.0";

    parameter clk0_phase_shift_num = 0;
    parameter clk1_phase_shift_num = 0;
    parameter clk2_phase_shift_num = 0;
    parameter family_name = "Stratix";

    parameter skip_vco = "off";

    parameter clk0_use_even_counter_mode = "off";
    parameter clk1_use_even_counter_mode = "off";
    parameter clk2_use_even_counter_mode = "off";
    parameter clk3_use_even_counter_mode = "off";
    parameter clk4_use_even_counter_mode = "off";
    parameter clk5_use_even_counter_mode = "off";
    parameter extclk0_use_even_counter_mode = "off";
    parameter extclk1_use_even_counter_mode = "off";
    parameter extclk2_use_even_counter_mode = "off";
    parameter extclk3_use_even_counter_mode = "off";

    parameter clk0_use_even_counter_value = "off";
    parameter clk1_use_even_counter_value = "off";
    parameter clk2_use_even_counter_value = "off";
    parameter clk3_use_even_counter_value = "off";
    parameter clk4_use_even_counter_value = "off";
    parameter clk5_use_even_counter_value = "off";
    parameter extclk0_use_even_counter_value = "off";
    parameter extclk1_use_even_counter_value = "off";
    parameter extclk2_use_even_counter_value = "off";
    parameter extclk3_use_even_counter_value = "off";

// SIMULATION_ONLY_PARAMETERS_END

    parameter scan_chain_mif_file = "";

    // INPUT PORTS
    input [1:0] inclk;
    input fbin;
    input ena;
    input clkswitch;
    input areset;
    input pfdena;
    input [5:0] clkena;
    input [3:0] extclkena;
    input scanclk;
    input scanaclr;
    input scandata;
    // lvds specific input ports
    input comparator;

    // OUTPUT PORTS
    output [5:0] clk;
    output [3:0] extclk;
    output [1:0] clkbad;
    output activeclock;
    output locked;
    output clkloss;
    output scandataout;
    // lvds specific output ports
    output enable0;
    output enable1;

    // BUFFER INPUTS
    wire inclk0_ipd;
    wire inclk1_ipd;
    wire ena_ipd;
    wire fbin_ipd;
    wire areset_ipd;
    wire pfdena_ipd;
    wire clkena0_ipd;
    wire clkena1_ipd;
    wire clkena2_ipd;
    wire clkena3_ipd;
    wire clkena4_ipd;
    wire clkena5_ipd;
    wire extclkena0_ipd;
    wire extclkena1_ipd;
    wire extclkena2_ipd;
    wire extclkena3_ipd;
    wire scanclk_ipd;
    wire scanaclr_ipd;
    wire scandata_ipd;
    wire comparator_ipd;
    wire clkswitch_ipd;

    buf (inclk0_ipd, inclk[0]);
    buf (inclk1_ipd, inclk[1]);
    buf (ena_ipd, ena);
    buf (fbin_ipd, fbin);
    buf (areset_ipd, areset);
    buf (pfdena_ipd, pfdena);
    buf (clkena0_ipd, clkena[0]);
    buf (clkena1_ipd, clkena[1]);
    buf (clkena2_ipd, clkena[2]);
    buf (clkena3_ipd, clkena[3]);
    buf (clkena4_ipd, clkena[4]);
    buf (clkena5_ipd, clkena[5]);
    buf (extclkena0_ipd, extclkena[0]);
    buf (extclkena1_ipd, extclkena[1]);
    buf (extclkena2_ipd, extclkena[2]);
    buf (extclkena3_ipd, extclkena[3]);
    buf (scanclk_ipd, scanclk);
    buf (scanaclr_ipd, scanaclr);
    buf (scandata_ipd, scandata);
    buf (comparator_ipd, comparator);
    buf (clkswitch_ipd, clkswitch);

    // INTERNAL VARIABLES AND NETS
    integer scan_chain_length;
    integer i;
    integer j;
    integer k;
    integer l_index;
    integer gate_count;
    integer egpp_offset;
    integer sched_time;
    integer delay_chain;
    integer low;
    integer high;
    integer initial_delay;
    integer fbk_phase;
    integer fbk_delay;
    integer phase_shift[0:7];
    integer last_phase_shift[0:7];

    integer m_times_vco_period;
    integer new_m_times_vco_period;
    integer refclk_period;
    integer fbclk_period;
    integer primary_clock_frequency;
    integer high_time;
    integer low_time;
    integer my_rem;
    integer tmp_rem;
    integer rem;
    integer tmp_vco_per;
    integer vco_per;
    integer offset;
    integer temp_offset;
    integer cycles_to_lock;
    integer cycles_to_unlock;
    integer l0_count;
    integer l1_count;
    integer loop_xplier;
    integer loop_initial;
    integer loop_ph;
    integer loop_time_delay;
    integer cycle_to_adjust;
    integer total_pull_back;
    integer pull_back_M;
    integer pull_back_ext_cntr;

    time    fbclk_time;
    time    first_fbclk_time;
    time    refclk_time;
    time    scanaclr_rising_time;
    time    scanaclr_falling_time;
 
    reg got_first_refclk;
    reg got_second_refclk;
    reg got_first_fbclk;
    reg refclk_last_value;
    reg fbclk_last_value;
    reg inclk_last_value;
    reg pll_is_locked;
    reg pll_about_to_lock;
    reg locked_tmp;
    reg l0_got_first_rising_edge;
    reg l1_got_first_rising_edge;
    reg vco_l0_last_value;
    reg vco_l1_last_value;
    reg areset_ipd_last_value;
    reg ena_ipd_last_value;
    reg pfdena_ipd_last_value;
    reg inclk_out_of_range;
    reg schedule_vco_last_value;

    reg gate_out;
    reg vco_val;

    reg [31:0] m_initial_val;
    reg [31:0] m_val;
    reg [31:0] m_val_tmp;
    reg [31:0] m2_val;
    reg [31:0] n_val;
    reg [31:0] n_val_tmp;
    reg [31:0] n2_val;
    reg [31:0] m_time_delay_val;
    reg [31:0] n_time_delay_val;
    reg [31:0] m_delay;
    reg [8*6:1] m_mode_val;
    reg [8*6:1] m2_mode_val;
    reg [8*6:1] n_mode_val;
    reg [8*6:1] n2_mode_val;
    reg [31:0] l0_high_val;
    reg [31:0] l0_low_val;
    reg [31:0] l0_initial_val;
    reg [31:0] l0_time_delay_val;
    reg [8*6:1] l0_mode_val;
    reg [31:0] l1_high_val;
    reg [31:0] l1_low_val;
    reg [31:0] l1_initial_val;
    reg [31:0] l1_time_delay_val;
    reg [8*6:1] l1_mode_val;

    reg [31:0] g0_high_val;
    reg [31:0] g0_low_val;
    reg [31:0] g0_initial_val;
    reg [31:0] g0_time_delay_val;
    reg [8*6:1] g0_mode_val;

    reg [31:0] g1_high_val;
    reg [31:0] g1_low_val;
    reg [31:0] g1_initial_val;
    reg [31:0] g1_time_delay_val;
    reg [8*6:1] g1_mode_val;

    reg [31:0] g2_high_val;
    reg [31:0] g2_low_val;
    reg [31:0] g2_initial_val;
    reg [31:0] g2_time_delay_val;
    reg [8*6:1] g2_mode_val;

    reg [31:0] g3_high_val;
    reg [31:0] g3_low_val;
    reg [31:0] g3_initial_val;
    reg [31:0] g3_time_delay_val;
    reg [8*6:1] g3_mode_val;

    reg [31:0] e0_high_val;
    reg [31:0] e0_low_val;
    reg [31:0] e0_initial_val;
    reg [31:0] e0_time_delay_val;
    reg [8*6:1] e0_mode_val;

    reg [31:0] e1_high_val;
    reg [31:0] e1_low_val;
    reg [31:0] e1_initial_val;
    reg [31:0] e1_time_delay_val;
    reg [8*6:1] e1_mode_val;

    reg [31:0] e2_high_val;
    reg [31:0] e2_low_val;
    reg [31:0] e2_initial_val;
    reg [31:0] e2_time_delay_val;
    reg [8*6:1] e2_mode_val;

    reg [31:0] e3_high_val;
    reg [31:0] e3_low_val;
    reg [31:0] e3_initial_val;
    reg [31:0] e3_time_delay_val;
    reg [8*6:1] e3_mode_val;

    reg scanclk_last_value;
    reg scanaclr_last_value;
    reg transfer;
    reg transfer_enable;
    reg [288:0] scan_data;
    reg schedule_vco;
    reg schedule_offset;
    reg stop_vco;
    reg inclk_n;

    reg [7:0] vco_out;
    wire inclk_l0;
    wire inclk_l1;
    wire inclk_m;
    wire clk0_tmp;
    wire clk1_tmp;
    wire clk2_tmp;
    wire clk3_tmp;
    wire clk4_tmp;
    wire clk5_tmp;
    wire extclk0_tmp;
    wire extclk1_tmp;
    wire extclk2_tmp;
    wire extclk3_tmp;
    wire nce_l0;
    wire nce_l1;
    wire nce_temp;

    reg vco_l0;
    reg vco_l1;

    wire clk0;
    wire clk1;
    wire clk2;
    wire clk3;
    wire clk4;
    wire clk5;
    wire extclk0;
    wire extclk1;
    wire extclk2;
    wire extclk3;
    wire ena0;
    wire ena1;
    wire ena2;
    wire ena3;
    wire ena4;
    wire ena5;
    wire extena0;
    wire extena1;
    wire extena2;
    wire extena3;
    wire refclk;
    wire fbclk;
    wire l0_clk;
    wire l1_clk;
    wire g0_clk;
    wire g1_clk;
    wire g2_clk;
    wire g3_clk;
    wire e0_clk;
    wire e1_clk;
    wire e2_clk;
    wire e3_clk;
    wire dffa_out;
    wire dffb_out;
    wire dffc_out;
    wire dffd_out;
    wire lvds_dffb_clk;
    wire lvds_dffc_clk;
    wire lvds_dffd_clk;
    
    reg first_schedule;

    wire enable0_tmp;
    wire enable1_tmp;
    wire enable_0;
    wire enable_1;
    reg l0_tmp;
    reg l1_tmp;

    reg vco_period_was_phase_adjusted;
    reg phase_adjust_was_scheduled;

    // for external feedback mode

    reg [31:0] ext_fbk_cntr_high;
    reg [31:0] ext_fbk_cntr_low;
    reg [31:0] ext_fbk_cntr_modulus;
    reg [31:0] ext_fbk_cntr_delay;
    reg [8*2:1] ext_fbk_cntr;
    reg [8*6:1] ext_fbk_cntr_mode;
    integer ext_fbk_cntr_ph;
    integer ext_fbk_cntr_initial;

    wire inclk_e0;
    wire inclk_e1;
    wire inclk_e2;
    wire inclk_e3;
    wire [31:0] cntr_e0_initial;
    wire [31:0] cntr_e1_initial;
    wire [31:0] cntr_e2_initial;
    wire [31:0] cntr_e3_initial;
    wire [31:0] cntr_e0_delay;
    wire [31:0] cntr_e1_delay;
    wire [31:0] cntr_e2_delay;
    wire [31:0] cntr_e3_delay;
    reg  [31:0] ext_fbk_delay;

    // variables for clk_switch
    reg clk0_is_bad;
    reg clk1_is_bad;
    reg inclk0_last_value;
    reg inclk1_last_value;
    reg other_clock_value;
    reg other_clock_last_value;
    reg primary_clk_is_bad;
    reg current_clk_is_bad;
    reg external_switch;
//    reg [8*6:1] current_clock;
    reg active_clock;
    reg clkloss_tmp;
    reg got_curr_clk_falling_edge_after_clkswitch;
    reg active_clk_was_switched;

    integer clk0_count;
    integer clk1_count;
    integer switch_over_count;

    reg scandataout_tmp;
    reg scandataout_trigger;
    integer quiet_time;
    reg pll_in_quiet_period;
    time start_quiet_time;
    reg quiet_period_violation;
    reg reconfig_err;
    reg scanclr_violation;
    reg scanclr_clk_violation;
    reg got_first_scanclk_after_scanclr_inactive_edge;
    reg error;

    reg no_warn;

// LOCAL_PARAMETERS_BEGIN

    parameter EGPP_SCAN_CHAIN = 289;
    parameter GPP_SCAN_CHAIN = 193;
    parameter TRST = 5000;
    parameter TRSTCLK = 5000;

// LOCAL_PARAMETERS_END

    // internal variables for scaling of multiply_by and divide_by values
    integer i_clk0_mult_by;
    integer i_clk0_div_by;
    integer i_clk1_mult_by;
    integer i_clk1_div_by;
    integer i_clk2_mult_by;
    integer i_clk2_div_by;
    integer i_clk3_mult_by;
    integer i_clk3_div_by;
    integer i_clk4_mult_by;
    integer i_clk4_div_by;
    integer i_clk5_mult_by;
    integer i_clk5_div_by;
    integer i_extclk0_mult_by;
    integer i_extclk0_div_by;
    integer i_extclk1_mult_by;
    integer i_extclk1_div_by;
    integer i_extclk2_mult_by;
    integer i_extclk2_div_by;
    integer i_extclk3_mult_by;
    integer i_extclk3_div_by;
    integer max_d_value;
    integer new_multiplier;

    // internal variables for storing the phase shift number.(used in lvds mode only)
    integer i_clk0_phase_shift;
    integer i_clk1_phase_shift;
    integer i_clk2_phase_shift;

    // user to advanced internal signals

    integer   i_m_initial;
    integer   i_m;
    integer   i_n;
    integer   i_m2;
    integer   i_n2;
    integer   i_ss;
    integer   i_l0_high;
    integer   i_l1_high;
    integer   i_g0_high;
    integer   i_g1_high;
    integer   i_g2_high;
    integer   i_g3_high;
    integer   i_e0_high;
    integer   i_e1_high;
    integer   i_e2_high;
    integer   i_e3_high;
    integer   i_l0_low;
    integer   i_l1_low;
    integer   i_g0_low;
    integer   i_g1_low;
    integer   i_g2_low;
    integer   i_g3_low;
    integer   i_e0_low;
    integer   i_e1_low;
    integer   i_e2_low;
    integer   i_e3_low;
    integer   i_l0_initial;
    integer   i_l1_initial;
    integer   i_g0_initial;
    integer   i_g1_initial;
    integer   i_g2_initial;
    integer   i_g3_initial;
    integer   i_e0_initial;
    integer   i_e1_initial;
    integer   i_e2_initial;
    integer   i_e3_initial;
    reg [8*6:1]   i_l0_mode;
    reg [8*6:1]   i_l1_mode;
    reg [8*6:1]   i_g0_mode;
    reg [8*6:1]   i_g1_mode;
    reg [8*6:1]   i_g2_mode;
    reg [8*6:1]   i_g3_mode;
    reg [8*6:1]   i_e0_mode;
    reg [8*6:1]   i_e1_mode;
    reg [8*6:1]   i_e2_mode;
    reg [8*6:1]   i_e3_mode;
    integer   i_vco_min;
    integer   i_vco_max;
    integer   i_vco_center;
    integer   i_pfd_min;
    integer   i_pfd_max;
    integer   i_l0_ph;
    integer   i_l1_ph;
    integer   i_g0_ph;
    integer   i_g1_ph;
    integer   i_g2_ph;
    integer   i_g3_ph;
    integer   i_e0_ph;
    integer   i_e1_ph;
    integer   i_e2_ph;
    integer   i_e3_ph;
    integer   i_m_ph;
    integer   m_ph_val;
    integer   i_l0_time_delay;
    integer   i_l1_time_delay;
    integer   i_g0_time_delay;
    integer   i_g1_time_delay;
    integer   i_g2_time_delay;
    integer   i_g3_time_delay;
    integer   i_e0_time_delay;
    integer   i_e1_time_delay;
    integer   i_e2_time_delay;
    integer   i_e3_time_delay;
    integer   i_m_time_delay;
    integer   i_n_time_delay;
    integer   i_extclk3_counter;
    integer   i_extclk2_counter;
    integer   i_extclk1_counter;
    integer   i_extclk0_counter;
    integer   i_clk5_counter;
    integer   i_clk4_counter;
    integer   i_clk3_counter;
    integer   i_clk2_counter;
    integer   i_clk1_counter;
    integer   i_clk0_counter;
    integer   i_charge_pump_current;
    integer   i_loop_filter_r;
    integer   max_neg_abs;
    integer   output_count;
    integer   new_divisor;

    reg pll_is_in_reset;

    // uppercase to lowercase parameter values
    reg [8*`STX_PLL_WORD_LENGTH:1] l_operation_mode;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_pll_type;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_qualify_conf_done;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_compensate_clock;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_scan_chain;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_primary_clock;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_gate_lock_signal;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_switch_over_on_lossclk;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_switch_over_on_gated_lock;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_enable_switch_over_counter;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_feedback_source;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_bandwidth_type;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_simulation_type;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_enable0_counter;
    reg [8*`STX_PLL_WORD_LENGTH:1] l_enable1_counter;

    integer current_clock;
    reg is_fast_pll;
    reg op_mode;

    reg init;

    specify
    endspecify

    // finds the closest integer fraction of a given pair of numerator and denominator. 
    task find_simple_integer_fraction;
        input numerator;
        input denominator;
        input max_denom;
        output fraction_num; 
        output fraction_div; 
        parameter max_iter = 20;
        
        integer numerator;
        integer denominator;
        integer max_denom;
        integer fraction_num; 
        integer fraction_div; 
        
        integer quotient_array[max_iter-1:0];
        integer int_loop_iter;
        integer int_quot;
        integer m_value;
        integer d_value;
        integer old_m_value;
        integer swap;

        integer loop_iter;
        integer num;
        integer den;
        integer i_max_iter;

    begin      
        loop_iter = 0;
        num = numerator;
        den = denominator;
        i_max_iter = max_iter;
       
        while (loop_iter < i_max_iter)
        begin
            int_quot = num / den;
            quotient_array[loop_iter] = int_quot;
            num = num - (den*int_quot);
            loop_iter=loop_iter+1;
            
            if ((num == 0) || (max_denom != -1) || (loop_iter == i_max_iter)) 
            begin
                // calculate the numerator and denominator if there is a restriction on the
                // max denom value or if the loop is ending
                m_value = 0;
                d_value = 1;
                // get the rounded value at this stage for the remaining fraction
                if (den != 0)
                begin
                    m_value = (2*num/den);
                end
                // calculate the fraction numerator and denominator at this stage
                for (int_loop_iter = loop_iter-1; int_loop_iter >= 0; int_loop_iter=int_loop_iter-1)
                begin
                    if (m_value == 0)
                    begin
                        m_value = quotient_array[int_loop_iter];
                        d_value = 1;
                    end
                    else
                    begin
                        old_m_value = m_value;
                        m_value = quotient_array[int_loop_iter]*m_value + d_value;
                        d_value = old_m_value;
                    end
                end
                // if the denominator is less than the maximum denom_value or if there is no restriction save it
                if ((d_value <= max_denom) || (max_denom == -1))
                begin
                    if ((m_value == 0) || (d_value == 0))
                    begin
                        fraction_num = numerator;
                        fraction_div = denominator;
                    end
                    else
                    begin
                        fraction_num = m_value;
                        fraction_div = d_value;
                    end
                end
                // end the loop if the denomitor has overflown or the numerator is zero (no remainder during this round)
                if (((d_value > max_denom) && (max_denom != -1)) || (num == 0))
                begin
                    i_max_iter = loop_iter;
                end
            end
            // swap the numerator and denominator for the next round
            swap = den;
            den = num;
            num = swap;
        end
    end
    endtask // find_simple_integer_fraction

// get the absolute value
    function integer abs;
    input value;
    integer value;
    begin
        if (value < 0)
            abs = value * -1;
        else abs = value;
    end
    endfunction

    // find twice the period of the slowest clock
    function integer slowest_clk;
    input L0, L0_mode, L1, L1_mode, G0, G0_mode, G1, G1_mode, G2, G2_mode, G3, G3_mode, E0, E0_mode, E1, E1_mode, E2, E2_mode, E3, E3_mode, scan_chain, refclk, m_mod;
    integer L0, L1, G0, G1, G2, G3, E0, E1, E2, E3;
    reg [8*6:1] L0_mode, L1_mode, G0_mode, G1_mode, G2_mode, G3_mode, E0_mode, E1_mode, E2_mode, E3_mode;
    reg [8*5:1] scan_chain;
    integer refclk;
    reg [31:0] m_mod;
    integer max_modulus;
    begin
        max_modulus = 1;
        if (L0_mode != "bypass" && L0_mode != "   off")
            max_modulus = L0;
        if (L1 > max_modulus && L1_mode != "bypass" && L1_mode != "   off")
            max_modulus = L1;
        if (G0 > max_modulus && G0_mode != "bypass" && G0_mode != "   off")
            max_modulus = G0;
        if (G1 > max_modulus && G1_mode != "bypass" && G1_mode != "   off")
            max_modulus = G1;
        if (G2 > max_modulus && G2_mode != "bypass" && G2_mode != "   off")
            max_modulus = G2;
        if (G3 > max_modulus && G3_mode != "bypass" && G3_mode != "   off")
            max_modulus = G3;
        if (scan_chain == "long")
        begin
            if (E0 > max_modulus && E0_mode != "bypass" && E0_mode != "   off")
                max_modulus = E0;
            if (E1 > max_modulus && E1_mode != "bypass" && E1_mode != "   off")
                max_modulus = E1;
            if (E2 > max_modulus && E2_mode != "bypass" && E2_mode != "   off")
                max_modulus = E2;
            if (E3 > max_modulus && E3_mode != "bypass" && E3_mode != "   off")
                max_modulus = E3;
        end

        slowest_clk = ((refclk/m_mod) * max_modulus *2);
    end
    endfunction
    
    // count the number of digits in the given integer
    function integer count_digit;
    input X;
    integer X;
    integer count, result;
    begin
        count = 0;
        result = X;
        while (result != 0)
        begin
            result = (result / 10);
            count = count + 1;
        end
        
        count_digit = count;
    end
    endfunction

    // reduce the given huge number(X) to Y significant digits
    function integer scale_num;
    input X, Y;
    integer X, Y;
    integer count;
    integer fac_ten, lc;
    begin
        fac_ten = 1;
        count = count_digit(X);
        
        for (lc = 0; lc < (count-Y); lc = lc + 1)
            fac_ten = fac_ten * 10;

        scale_num = (X / fac_ten);
    end
    endfunction     

    // find the greatest common denominator of X and Y
    function integer gcd;
    input X,Y;
    integer X,Y;
    integer L, S, R, G;
    begin
        if (X < Y) // find which is smaller.
        begin
            S = X;
            L = Y;
        end
        else
        begin
            S = Y;
            L = X;
        end

        R = S;
        while ( R > 1)
        begin
            S = L;
            L = R;
            R = S % L;  // divide bigger number by smaller.
                        // remainder becomes smaller number.
        end
        if (R == 0)    // if evenly divisible then L is gcd else it is 1.
            G = L;
        else
            G = R;
        gcd = G;
    end
    endfunction

    // find the least common multiple of A1 to A10
    function integer lcm;
    input A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer M1, M2, M3, M4, M5 , M6, M7, M8, M9, R;
    begin
        M1 = (A1 * A2)/gcd(A1, A2);
        M2 = (M1 * A3)/gcd(M1, A3);
        M3 = (M2 * A4)/gcd(M2, A4);
        M4 = (M3 * A5)/gcd(M3, A5);
        M5 = (M4 * A6)/gcd(M4, A6);
        M6 = (M5 * A7)/gcd(M5, A7);
        M7 = (M6 * A8)/gcd(M6, A8);
        M8 = (M7 * A9)/gcd(M7, A9);
        M9 = (M8 * A10)/gcd(M8, A10);
        if (M9 < 3)
            R = 10;
        else if ((M9 <= 10) && (M9 >= 3))
            R = 4 * M9;
        else if (M9 > 1000)
            R = scale_num(M9,3);
        else
            R = M9;
        lcm = R; 
    end
    endfunction

    // find the factor of division of the output clock frequency
    // compared to the VCO
    function integer output_counter_value;
    input clk_divide, clk_mult, M, N;
    integer clk_divide, clk_mult, M, N;
    integer R;
    begin
        R = (clk_divide * M)/(clk_mult * N);
        output_counter_value = R;
    end
    endfunction

    // find the mode of each of the PLL counters - bypass, even or odd
    function [8*6:1] counter_mode;
    input duty_cycle;
    input output_counter_value;
    integer duty_cycle;
    integer output_counter_value;
    integer half_cycle_high;
    reg [8*6:1] R;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100;
        if (output_counter_value == 1)
            R = "bypass";
        else if ((half_cycle_high % 2) == 0)
            R = "even";
        else
            R = "odd";
        counter_mode = R;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock high
    function integer counter_high;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle;
    integer half_cycle_high;
    integer tmp_counter_high;
    integer mode;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_high = tmp_counter_high + !mode;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock low
    function integer counter_low;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle, counter_h;
    integer half_cycle_high;
    integer mode;
    integer tmp_counter_high;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_h = tmp_counter_high + !mode;
        counter_low =  output_counter_value - counter_h;
        if (counter_low == 0)
            counter_low = 1;
    end
    endfunction

    // find the smallest time delay amongst t1 to t10
    function integer mintimedelay;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2)
            m1 = t1;
        else
            m1 = t2;
        if (m1 < t3)
            m2 = m1;
        else
            m2 = t3;
        if (m2 < t4)
            m3 = m2;
        else
            m3 = t4;
        if (m3 < t5)
            m4 = m3;
        else
            m4 = t5;
        if (m4 < t6)
            m5 = m4;
        else
            m5 = t6;
        if (m5 < t7)
            m6 = m5;
        else
            m6 = t7;
        if (m6 < t8)
            m7 = m6;
        else
            m7 = t8;
        if (m7 < t9)
            m8 = m7;
        else
            m8 = t9;
        if (m8 < t10)
            m9 = m8;
        else
            m9 = t10;
        if (m9 > 0)
            mintimedelay = m9;
        else
            mintimedelay = 0;
    end
    endfunction

    // find the numerically largest negative number, and return its absolute value
    function integer maxnegabs;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2) m1 = t1; else m1 = t2;
        if (m1 < t3) m2 = m1; else m2 = t3;
        if (m2 < t4) m3 = m2; else m3 = t4;
        if (m3 < t5) m4 = m3; else m4 = t5;
        if (m4 < t6) m5 = m4; else m5 = t6;
        if (m5 < t7) m6 = m5; else m6 = t7;
        if (m6 < t8) m7 = m6; else m7 = t8;
        if (m7 < t9) m8 = m7; else m8 = t9;
        if (m8 < t10) m9 = m8; else m9 = t10;
        maxnegabs = (m9 < 0) ? 0 - m9 : 0;
    end
    endfunction

    // adjust the given tap_phase by adding the largest negative number (ph_base) 
    function integer ph_adjust;
    input tap_phase, ph_base;
    integer tap_phase, ph_base;
    begin
        ph_adjust = tap_phase + ph_base;
    end
    endfunction

    // find the actual time delay for each PLL counter
    function integer counter_time_delay;
    input clk_time_delay, m_time_delay, n_time_delay;
    integer clk_time_delay, m_time_delay, n_time_delay;
    begin
        counter_time_delay = clk_time_delay + m_time_delay - n_time_delay;
    end
    endfunction

    // find the number of VCO clock cycles to wait initially before the first 
    // rising edge of the output clock
    function integer counter_initial;
    input tap_phase, m, n;
    integer tap_phase, m, n, phase;
    begin
        if (tap_phase < 0) tap_phase = 0 - tap_phase;
        // adding 0.5 for rounding correction (required in order to round
        // to the nearest integer instead of truncating)
        phase = ((tap_phase * m) / (360 * n)) + 0.5;
        counter_initial = phase;
    end
    endfunction

    // find which VCO phase tap to align the rising edge of the output clock to
    function integer counter_ph;
    input tap_phase;
    input m,n;
    integer m,n, phase;
    integer tap_phase;
    begin
    // adding 0.5 for rounding correction
        phase = (tap_phase * m / n) + 0.5;
        counter_ph = (phase % 360) / 45;
    end
    endfunction

    // convert the given string to length 6 by padding with spaces
    function [8*6:1] translate_string;
    input mode;
    reg [8*6:1] new_mode;
    begin
        if (mode == "bypass")
            new_mode = "bypass";
        else if (mode == "even")
            new_mode = "  even";
        else if (mode == "odd")
            new_mode = "   odd";

        translate_string = new_mode;
    end
    endfunction

    // convert string to integer with sign
    function integer str2int; 
    input [8*16:1] s;

    reg [8*16:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    integer m, magnitude;
    integer sign;

    begin
        sign = 1;
        magnitude = 0;
        reg_s = s;
        for (m=1; m<=16; m=m+1)
        begin
            tmp = reg_s[128:121];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            // Accumulate ascii digits 0-9 only.
            if ((tmp>=48) && (tmp<=57)) 
                magnitude = (magnitude * 10) + digit;
            if (tmp == 45)
                sign = -1;  // Found a '-' character, i.e. number is negative.
        end
        str2int = sign*magnitude;
    end
    endfunction

    // this is for stratix lvds only
    // convert phase delay to integer
    function integer get_int_phase_shift; 
    input [8*16:1] s;
    input i_phase_shift;
    integer i_phase_shift;

    begin
        if (i_phase_shift != 0)
        begin                   
            get_int_phase_shift = i_phase_shift;
        end       
        else
        begin
            get_int_phase_shift = str2int(s);
        end        
    end
    endfunction

    // calculate the given phase shift (in ps) in terms of degrees
    function integer get_phase_degree; 
    input phase_shift;
    integer phase_shift, result;
    begin
        result = (phase_shift * 360) / inclk0_input_frequency;
        // this is to round up the calculation result
        if ( result > 0 )
            result = result + 1;
        else if ( result < 0 )
            result = result - 1;
        else
            result = 0;

        // assign the rounded up result
        get_phase_degree = result;
    end
    endfunction

    // convert uppercase parameter values to lowercase
    // assumes that the maximum character length of a parameter is 18
    function [8*`STX_PLL_WORD_LENGTH:1] alpha_tolower;
    input [8*`STX_PLL_WORD_LENGTH:1] given_string;

    reg [8*`STX_PLL_WORD_LENGTH:1] return_string;
    reg [8*`STX_PLL_WORD_LENGTH:1] reg_string;
    reg [8:1] tmp;
    reg [8:1] conv_char;
    integer byte_count;
    begin
        return_string = "                    "; // initialise strings to spaces
        conv_char = "        ";
        reg_string = given_string;
        for (byte_count = `STX_PLL_WORD_LENGTH; byte_count >= 1; byte_count = byte_count - 1)
        begin
            tmp = reg_string[8*`STX_PLL_WORD_LENGTH:(8*(`STX_PLL_WORD_LENGTH-1)+1)];
            reg_string = reg_string << 8;
            if ((tmp >= 65) && (tmp <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
            begin
                conv_char = tmp + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
                return_string = {return_string, conv_char};
            end
            else
                return_string = {return_string, tmp};
        end
    
        alpha_tolower = return_string;
    end
    endfunction

    initial
    begin
        // convert string parameter values from uppercase to lowercase,
        // as expected in this model
        l_operation_mode             = alpha_tolower(operation_mode);
        l_pll_type                   = alpha_tolower(pll_type);
        l_qualify_conf_done          = alpha_tolower(qualify_conf_done);
        l_compensate_clock           = alpha_tolower(compensate_clock);
        l_scan_chain                 = alpha_tolower(scan_chain);
        l_primary_clock              = alpha_tolower(primary_clock);
        l_gate_lock_signal           = alpha_tolower(gate_lock_signal);
        l_switch_over_on_lossclk     = alpha_tolower(switch_over_on_lossclk);
        l_switch_over_on_gated_lock  = alpha_tolower(switch_over_on_gated_lock);
        l_enable_switch_over_counter = alpha_tolower(enable_switch_over_counter);
        l_feedback_source            = alpha_tolower(feedback_source);
        l_bandwidth_type             = alpha_tolower(bandwidth_type);
        l_simulation_type            = alpha_tolower(simulation_type);
        l_enable0_counter            = alpha_tolower(enable0_counter);
        l_enable1_counter            = alpha_tolower(enable1_counter);

        if (m == 0)
        begin 
            // set the limit of the divide_by value that can be returned by
            // the following function.
            max_d_value = 500;
            
            // scale down the multiply_by and divide_by values provided by the design
            // before attempting to use them in the calculations below
            find_simple_integer_fraction(clk0_multiply_by, clk0_divide_by,
                            max_d_value, i_clk0_mult_by, i_clk0_div_by);
            find_simple_integer_fraction(clk1_multiply_by, clk1_divide_by,
                            max_d_value, i_clk1_mult_by, i_clk1_div_by);
            find_simple_integer_fraction(clk2_multiply_by, clk2_divide_by,
                            max_d_value, i_clk2_mult_by, i_clk2_div_by);
            find_simple_integer_fraction(clk3_multiply_by, clk3_divide_by,
                            max_d_value, i_clk3_mult_by, i_clk3_div_by);
            find_simple_integer_fraction(clk4_multiply_by, clk4_divide_by,
                            max_d_value, i_clk4_mult_by, i_clk4_div_by);
            find_simple_integer_fraction(clk5_multiply_by, clk5_divide_by,
                            max_d_value, i_clk5_mult_by, i_clk5_div_by);
            find_simple_integer_fraction(extclk0_multiply_by, extclk0_divide_by,
                            max_d_value, i_extclk0_mult_by, i_extclk0_div_by);
            find_simple_integer_fraction(extclk1_multiply_by, extclk1_divide_by,
                            max_d_value, i_extclk1_mult_by, i_extclk1_div_by);
            find_simple_integer_fraction(extclk2_multiply_by, extclk2_divide_by,
                            max_d_value, i_extclk2_mult_by, i_extclk2_div_by);
            find_simple_integer_fraction(extclk3_multiply_by, extclk3_divide_by,
                            max_d_value, i_extclk3_mult_by, i_extclk3_div_by);

            // convert user parameters to advanced
            i_n = 1;
            if (l_pll_type == "lvds")
                i_m = clk0_multiply_by;
            else
                i_m = lcm  (i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,
                            i_clk4_mult_by, i_clk5_mult_by,
                            i_extclk0_mult_by,
                            i_extclk1_mult_by, i_extclk2_mult_by,
                            i_extclk3_mult_by, inclk0_input_frequency);
            i_m_time_delay = maxnegabs (str2int(clk0_time_delay),
                                        str2int(clk1_time_delay),
                                        str2int(clk2_time_delay),
                                        str2int(clk3_time_delay),
                                        str2int(clk4_time_delay),
                                        str2int(clk5_time_delay),
                                        str2int(extclk0_time_delay),
                                        str2int(extclk1_time_delay),
                                        str2int(extclk2_time_delay),
                                        str2int(extclk3_time_delay));
            i_n_time_delay = mintimedelay(str2int(clk0_time_delay),
                                        str2int(clk1_time_delay),
                                        str2int(clk2_time_delay),
                                        str2int(clk3_time_delay),
                                        str2int(clk4_time_delay),
                                        str2int(clk5_time_delay),
                                        str2int(extclk0_time_delay),
                                        str2int(extclk1_time_delay),
                                        str2int(extclk2_time_delay),
                                        str2int(extclk3_time_delay));
            if (l_pll_type == "lvds")
                i_g0_high = counter_high(output_counter_value(i_clk2_div_by,
                            i_clk2_mult_by, i_m, i_n), clk2_duty_cycle);
            else
                i_g0_high = counter_high(output_counter_value(i_clk0_div_by,
                            i_clk0_mult_by, i_m, i_n), clk0_duty_cycle);

            
            i_g1_high = counter_high(output_counter_value(i_clk1_div_by,
                        i_clk1_mult_by, i_m, i_n), clk1_duty_cycle);
            i_g2_high = counter_high(output_counter_value(i_clk2_div_by,
                        i_clk2_mult_by, i_m, i_n), clk2_duty_cycle);
            i_g3_high = counter_high(output_counter_value(i_clk3_div_by,
                        i_clk3_mult_by, i_m, i_n), clk3_duty_cycle);
            if (l_pll_type == "lvds")
            begin
                i_l0_high = i_g0_high;
                i_l1_high = i_g0_high;
            end
            else
            begin
                i_l0_high = counter_high(output_counter_value(i_clk4_div_by,
                            i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);
                i_l1_high = counter_high(output_counter_value(i_clk5_div_by,
                            i_clk5_mult_by,  i_m, i_n), clk5_duty_cycle);
            end
            i_e0_high = counter_high(output_counter_value(i_extclk0_div_by,
                        i_extclk0_mult_by,  i_m, i_n), extclk0_duty_cycle);
            i_e1_high = counter_high(output_counter_value(i_extclk1_div_by,
                        i_extclk1_mult_by,  i_m, i_n), extclk1_duty_cycle);
            i_e2_high = counter_high(output_counter_value(i_extclk2_div_by,
                        i_extclk2_mult_by,  i_m, i_n), extclk2_duty_cycle);
            i_e3_high = counter_high(output_counter_value(i_extclk3_div_by,
                        i_extclk3_mult_by,  i_m, i_n), extclk3_duty_cycle);
            if (l_pll_type == "lvds")
                i_g0_low  = counter_low(output_counter_value(i_clk2_div_by,
                            i_clk2_mult_by,  i_m, i_n), clk2_duty_cycle);
            else
                i_g0_low  = counter_low(output_counter_value(i_clk0_div_by,
                            i_clk0_mult_by,  i_m, i_n), clk0_duty_cycle);
            i_g1_low  = counter_low(output_counter_value(i_clk1_div_by,
                        i_clk1_mult_by,  i_m, i_n), clk1_duty_cycle);
            i_g2_low  = counter_low(output_counter_value(i_clk2_div_by,
                        i_clk2_mult_by,  i_m, i_n), clk2_duty_cycle);
            i_g3_low  = counter_low(output_counter_value(i_clk3_div_by,
                        i_clk3_mult_by,  i_m, i_n), clk3_duty_cycle);
            if (l_pll_type == "lvds")
            begin
                i_l0_low  = i_g0_low;
                i_l1_low  = i_g0_low;
            end
            else
            begin
                i_l0_low  = counter_low(output_counter_value(i_clk4_div_by,
                            i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);
                i_l1_low  = counter_low(output_counter_value(i_clk5_div_by,
                            i_clk5_mult_by,  i_m, i_n), clk5_duty_cycle);
            end
            i_e0_low  = counter_low(output_counter_value(i_extclk0_div_by,
                        i_extclk0_mult_by,  i_m, i_n), extclk0_duty_cycle);
            i_e1_low  = counter_low(output_counter_value(i_extclk1_div_by,
                        i_extclk1_mult_by,  i_m, i_n), extclk1_duty_cycle);
            i_e2_low  = counter_low(output_counter_value(i_extclk2_div_by,
                        i_extclk2_mult_by,  i_m, i_n), extclk2_duty_cycle);
            i_e3_low  = counter_low(output_counter_value(i_extclk3_div_by,
                        i_extclk3_mult_by,  i_m, i_n), extclk3_duty_cycle);            
            
            if (l_pll_type == "flvds")
            begin
                // Need to readjust phase shift values when the clock multiply value has been readjusted.
                new_multiplier = clk0_multiply_by / i_clk0_mult_by;
                i_clk0_phase_shift = (clk0_phase_shift_num * new_multiplier);
                i_clk1_phase_shift = (clk1_phase_shift_num * new_multiplier);
                i_clk2_phase_shift = (clk2_phase_shift_num * new_multiplier);
            end
            else
            begin
                i_clk0_phase_shift = get_int_phase_shift(clk0_phase_shift, clk0_phase_shift_num);
                i_clk1_phase_shift = get_int_phase_shift(clk1_phase_shift, clk1_phase_shift_num);
                i_clk2_phase_shift = get_int_phase_shift(clk2_phase_shift, clk2_phase_shift_num);
            end
            
            max_neg_abs = maxnegabs(i_clk0_phase_shift,
                                    i_clk1_phase_shift,
                                    i_clk2_phase_shift,
                                    str2int(clk3_phase_shift),
                                    str2int(clk4_phase_shift),
                                    str2int(clk5_phase_shift),
                                    str2int(extclk0_phase_shift),
                                    str2int(extclk1_phase_shift),
                                    str2int(extclk2_phase_shift),
                                    str2int(extclk3_phase_shift));
            if (l_pll_type == "lvds")
                i_g0_initial = counter_initial(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            else
                i_g0_initial = counter_initial(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);

            i_g1_initial = counter_initial(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_g2_initial = counter_initial(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_g3_initial = counter_initial(get_phase_degree(ph_adjust(str2int(clk3_phase_shift), max_neg_abs)), i_m, i_n);
            if (l_pll_type == "lvds")
            begin
                i_l0_initial = i_g0_initial;
                i_l1_initial = i_g0_initial;
            end
            else
            begin
                i_l0_initial = counter_initial(get_phase_degree(ph_adjust(str2int(clk4_phase_shift), max_neg_abs)), i_m, i_n);
                i_l1_initial = counter_initial(get_phase_degree(ph_adjust(str2int(clk5_phase_shift), max_neg_abs)), i_m, i_n);
            end
            i_e0_initial = counter_initial(get_phase_degree(ph_adjust(str2int(extclk0_phase_shift), max_neg_abs)), i_m, i_n);
            i_e1_initial = counter_initial(get_phase_degree(ph_adjust(str2int(extclk1_phase_shift), max_neg_abs)), i_m, i_n);
            i_e2_initial = counter_initial(get_phase_degree(ph_adjust(str2int(extclk2_phase_shift), max_neg_abs)), i_m, i_n);
            i_e3_initial = counter_initial(get_phase_degree(ph_adjust(str2int(extclk3_phase_shift), max_neg_abs)), i_m, i_n);
            if (l_pll_type == "lvds")
                i_g0_mode = counter_mode(clk2_duty_cycle, output_counter_value(i_clk2_div_by, i_clk2_mult_by,  i_m, i_n));
            else
                i_g0_mode = counter_mode(clk0_duty_cycle, output_counter_value(i_clk0_div_by, i_clk0_mult_by,  i_m, i_n));
            i_g1_mode = counter_mode(clk1_duty_cycle,output_counter_value(i_clk1_div_by, i_clk1_mult_by,  i_m, i_n));
            i_g2_mode = counter_mode(clk2_duty_cycle,output_counter_value(i_clk2_div_by, i_clk2_mult_by,  i_m, i_n));
            i_g3_mode = counter_mode(clk3_duty_cycle,output_counter_value(i_clk3_div_by, i_clk3_mult_by,  i_m, i_n));
            if (l_pll_type == "lvds")
            begin
                i_l0_mode = "bypass";
                i_l1_mode = "bypass";
            end
            else
            begin
                i_l0_mode = counter_mode(clk4_duty_cycle,output_counter_value(i_clk4_div_by, i_clk4_mult_by,  i_m, i_n));
                i_l1_mode = counter_mode(clk5_duty_cycle,output_counter_value(i_clk5_div_by, i_clk5_mult_by,  i_m, i_n));
            end
            i_e0_mode = counter_mode(extclk0_duty_cycle,output_counter_value(i_extclk0_div_by, i_extclk0_mult_by,  i_m, i_n));
            i_e1_mode = counter_mode(extclk1_duty_cycle,output_counter_value(i_extclk1_div_by, i_extclk1_mult_by,  i_m, i_n));
            i_e2_mode = counter_mode(extclk2_duty_cycle,output_counter_value(i_extclk2_div_by, i_extclk2_mult_by,  i_m, i_n));
            i_e3_mode = counter_mode(extclk3_duty_cycle,output_counter_value(i_extclk3_div_by, i_extclk3_mult_by,  i_m, i_n));
            i_m_ph    = counter_ph(get_phase_degree(max_neg_abs), i_m, i_n);
            i_m_initial = counter_initial(get_phase_degree(max_neg_abs), i_m, i_n);
            if (l_pll_type == "lvds")
                i_g0_ph = counter_ph(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            else
                i_g0_ph = counter_ph(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);

            i_g1_ph = counter_ph(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_g2_ph = counter_ph(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_g3_ph = counter_ph(get_phase_degree(ph_adjust(str2int(clk3_phase_shift),max_neg_abs)), i_m, i_n);
            if (l_pll_type == "lvds")
            begin
                i_l0_ph = i_g0_ph;
                i_l1_ph = i_g0_ph;
            end
            else
            begin
                i_l0_ph = counter_ph(get_phase_degree(ph_adjust(str2int(clk4_phase_shift),max_neg_abs)), i_m, i_n);
                i_l1_ph = counter_ph(get_phase_degree(ph_adjust(str2int(clk5_phase_shift),max_neg_abs)), i_m, i_n);
            end
            i_e0_ph = counter_ph(get_phase_degree(ph_adjust(str2int(extclk0_phase_shift),max_neg_abs)), i_m, i_n);
            i_e1_ph = counter_ph(get_phase_degree(ph_adjust(str2int(extclk1_phase_shift),max_neg_abs)), i_m, i_n);
            i_e2_ph = counter_ph(get_phase_degree(ph_adjust(str2int(extclk2_phase_shift),max_neg_abs)), i_m, i_n);
            i_e3_ph = counter_ph(get_phase_degree(ph_adjust(str2int(extclk3_phase_shift),max_neg_abs)), i_m, i_n);

            if (l_pll_type == "lvds")
                i_g0_time_delay = counter_time_delay  ( str2int(clk2_time_delay),
                                                        i_m_time_delay,
                                                        i_n_time_delay);
            else
                i_g0_time_delay = counter_time_delay  ( str2int(clk0_time_delay),
                                                        i_m_time_delay,
                                                        i_n_time_delay);
            i_g1_time_delay = counter_time_delay  ( str2int(clk1_time_delay),
                                                    i_m_time_delay,
                                                    i_n_time_delay);
            i_g2_time_delay = counter_time_delay  ( str2int(clk2_time_delay),
                                                    i_m_time_delay,
                                                    i_n_time_delay);
            i_g3_time_delay = counter_time_delay  ( str2int(clk3_time_delay),
                                                    i_m_time_delay,
                                                    i_n_time_delay);
            if (l_pll_type == "lvds")
            begin
                i_l0_time_delay = i_g0_time_delay;
                i_l1_time_delay = i_g0_time_delay;
            end
            else
            begin
                i_l0_time_delay = counter_time_delay  ( str2int(clk4_time_delay),
                                                        i_m_time_delay,
                                                        i_n_time_delay);
                i_l1_time_delay = counter_time_delay  ( str2int(clk5_time_delay),
                                                        i_m_time_delay,
                                                        i_n_time_delay);
            end
            i_e0_time_delay = counter_time_delay ( str2int( extclk0_time_delay),
                                                            i_m_time_delay,
                                                            i_n_time_delay);
            i_e1_time_delay = counter_time_delay ( str2int( extclk1_time_delay),
                                                            i_m_time_delay,
                                                            i_n_time_delay);
            i_e2_time_delay = counter_time_delay ( str2int( extclk2_time_delay),
                                                            i_m_time_delay,
                                                            i_n_time_delay);
            i_e3_time_delay = counter_time_delay ( str2int( extclk3_time_delay),
                                                            i_m_time_delay,
                                                            i_n_time_delay);
            i_extclk3_counter = "e3" ;
            i_extclk2_counter = "e2" ;
            i_extclk1_counter = "e1" ;
            i_extclk0_counter = "e0" ;
            i_clk5_counter    = "l1" ;
            i_clk4_counter    = "l0" ;
            i_clk3_counter    = "g3" ;
            i_clk2_counter    = "g2" ;
            i_clk1_counter    = "g1" ;

            if (l_pll_type == "lvds")
            begin
                l_enable0_counter = "l0";
                l_enable1_counter = "l1";
                i_clk0_counter    = "l0" ;
            end
            else
                i_clk0_counter    = "g0" ;

            // in external feedback mode, need to adjust M value to take
            // into consideration the external feedback counter value
            if (l_operation_mode == "external_feedback")
            begin
                // if there is a negative phase shift, m_initial can only be 1
                if (max_neg_abs > 0)
                    i_m_initial = 1;

                if (l_feedback_source == "extclk0")
                begin
                    if (i_e0_mode == "bypass")
                        output_count = 1;
                    else
                        output_count = i_e0_high + i_e0_low;
                end
                else if (l_feedback_source == "extclk1")
                begin
                    if (i_e1_mode == "bypass")
                        output_count = 1;
                    else
                        output_count = i_e1_high + i_e1_low;
                end
                else if (l_feedback_source == "extclk2")
                begin
                    if (i_e2_mode == "bypass")
                        output_count = 1;
                    else
                        output_count = i_e2_high + i_e2_low;
                end
                else if (l_feedback_source == "extclk3")
                begin
                    if (i_e3_mode == "bypass")
                        output_count = 1;
                    else
                        output_count = i_e3_high + i_e3_low;
                end
                else // default to e0
                begin
                    if (i_e0_mode == "bypass")
                        output_count = 1;
                    else
                        output_count = i_e0_high + i_e0_low;
                end

                new_divisor = gcd(i_m, output_count);
                i_m = i_m / new_divisor;
                i_n = output_count / new_divisor;
            end

        end
        else 
        begin //  m != 0

            i_n = n;
            i_m = m;
            i_l0_high = l0_high;
            i_l1_high = l1_high;
            i_g0_high = g0_high;
            i_g1_high = g1_high;
            i_g2_high = g2_high;
            i_g3_high = g3_high;
            i_e0_high = e0_high;
            i_e1_high = e1_high;
            i_e2_high = e2_high;
            i_e3_high = e3_high;
            i_l0_low  = l0_low;
            i_l1_low  = l1_low;
            i_g0_low  = g0_low;
            i_g1_low  = g1_low;
            i_g2_low  = g2_low;
            i_g3_low  = g3_low;
            i_e0_low  = e0_low;
            i_e1_low  = e1_low;
            i_e2_low  = e2_low;
            i_e3_low  = e3_low;
            i_l0_initial = l0_initial;
            i_l1_initial = l1_initial;
            i_g0_initial = g0_initial;
            i_g1_initial = g1_initial;
            i_g2_initial = g2_initial;
            i_g3_initial = g3_initial;
            i_e0_initial = e0_initial;
            i_e1_initial = e1_initial;
            i_e2_initial = e2_initial;
            i_e3_initial = e3_initial;
            i_l0_mode = alpha_tolower(l0_mode);
            i_l1_mode = alpha_tolower(l1_mode);
            i_g0_mode = alpha_tolower(g0_mode);
            i_g1_mode = alpha_tolower(g1_mode);
            i_g2_mode = alpha_tolower(g2_mode);
            i_g3_mode = alpha_tolower(g3_mode);
            i_e0_mode = alpha_tolower(e0_mode);
            i_e1_mode = alpha_tolower(e1_mode);
            i_e2_mode = alpha_tolower(e2_mode);
            i_e3_mode = alpha_tolower(e3_mode);
            i_l0_ph  = l0_ph;
            i_l1_ph  = l1_ph;
            i_g0_ph  = g0_ph;
            i_g1_ph  = g1_ph;
            i_g2_ph  = g2_ph;
            i_g3_ph  = g3_ph;
            i_e0_ph  = e0_ph;
            i_e1_ph  = e1_ph;
            i_e2_ph  = e2_ph;
            i_e3_ph  = e3_ph;
            i_m_ph   = m_ph;        // default
            i_m_initial = m_initial;
            i_l0_time_delay = l0_time_delay;
            i_l1_time_delay = l1_time_delay;
            i_g0_time_delay = g0_time_delay;
            i_g1_time_delay = g1_time_delay;
            i_g2_time_delay = g2_time_delay;
            i_g3_time_delay = g3_time_delay;
            i_e0_time_delay = e0_time_delay;
            i_e1_time_delay = e1_time_delay;
            i_e2_time_delay = e2_time_delay;
            i_e3_time_delay = e3_time_delay;
            i_m_time_delay  = m_time_delay;
            i_n_time_delay  = n_time_delay;
            i_extclk3_counter = alpha_tolower(extclk3_counter);
            i_extclk2_counter = alpha_tolower(extclk2_counter);
            i_extclk1_counter = alpha_tolower(extclk1_counter);
            i_extclk0_counter = alpha_tolower(extclk0_counter);
            i_clk5_counter    = alpha_tolower(clk5_counter);
            i_clk4_counter    = alpha_tolower(clk4_counter);
            i_clk3_counter    = alpha_tolower(clk3_counter);
            i_clk2_counter    = alpha_tolower(clk2_counter);
            i_clk1_counter    = alpha_tolower(clk1_counter);
            i_clk0_counter    = alpha_tolower(clk0_counter);

        end // user to advanced conversion

        // set the scan_chain length
        if (l_scan_chain == "long")
            scan_chain_length = EGPP_SCAN_CHAIN;
        else if (l_scan_chain == "short")
            scan_chain_length = GPP_SCAN_CHAIN;

        if (l_primary_clock == "inclk0")
        begin
            refclk_period = inclk0_input_frequency * i_n;
            primary_clock_frequency = inclk0_input_frequency;
        end
        else if (l_primary_clock == "inclk1")
        begin
            refclk_period = inclk1_input_frequency * i_n;
            primary_clock_frequency = inclk1_input_frequency;
        end

        m_times_vco_period = refclk_period;
        new_m_times_vco_period = refclk_period;

        fbclk_period = 0;
        high_time = 0;
        low_time = 0;
        schedule_vco = 0;
        schedule_offset = 1;
        vco_out[7:0] = 8'b0;
        fbclk_last_value = 0;
        offset = 0;
        temp_offset = 0;
        got_first_refclk = 0;
        got_first_fbclk = 0;
        fbclk_time = 0;
        first_fbclk_time = 0;
        refclk_time = 0;
        first_schedule = 1;
        sched_time = 0;
        vco_val = 0;
        l0_got_first_rising_edge = 0;
        l1_got_first_rising_edge = 0;
        vco_l0_last_value = 0;
        l0_count = 1;
        l1_count = 1;
        l0_tmp = 0;
        l1_tmp = 0;
        gate_count = 0;
        gate_out = 0;
        initial_delay = 0;
        fbk_phase = 0;
        for (i = 0; i <= 7; i = i + 1)
        begin
            phase_shift[i] = 0;
            last_phase_shift[i] = 0;
        end
        fbk_delay = 0;
        inclk_n = 0;
        cycle_to_adjust = 0;
        m_delay = 0;
        vco_l0 = 0;
        vco_l1 = 0;
        total_pull_back = 0;
        pull_back_M = 0;
        pull_back_ext_cntr = 0;
        vco_period_was_phase_adjusted = 0;
        phase_adjust_was_scheduled = 0;
        ena_ipd_last_value = 0;
        inclk_out_of_range = 0;
        scandataout_tmp = 0;
        scandataout_trigger = 0;
        schedule_vco_last_value = 0;

        // set initial values for counter parameters
        m_initial_val = i_m_initial;
        m_val = i_m;
        m_time_delay_val = i_m_time_delay;
        n_val = i_n;
        n_time_delay_val = i_n_time_delay;
        m_ph_val = i_m_ph;

        m2_val = m2;
        n2_val = n2;

        if (m_val == 1)
            m_mode_val = "bypass";
        if (m2_val == 1)
            m2_mode_val = "bypass";
        if (n_val == 1)
            n_mode_val = "bypass";
        if (n2_val == 1)
            n2_mode_val = "bypass";

        if (skip_vco == "on")
        begin
            m_val = 1;
            m_initial_val = 1;
            m_time_delay_val = 0;
            m_ph_val = 0;
        end

        l0_high_val = i_l0_high;
        l0_low_val = i_l0_low;
        l0_initial_val = i_l0_initial;
        l0_mode_val = i_l0_mode;
        l0_time_delay_val = i_l0_time_delay;

        l1_high_val = i_l1_high;
        l1_low_val = i_l1_low;
        l1_initial_val = i_l1_initial;
        l1_mode_val = i_l1_mode;
        l1_time_delay_val = i_l1_time_delay;

        g0_high_val = i_g0_high;
        g0_low_val = i_g0_low;
        g0_initial_val = i_g0_initial;
        g0_mode_val = i_g0_mode;
        g0_time_delay_val = i_g0_time_delay;

        g1_high_val = i_g1_high;
        g1_low_val = i_g1_low;
        g1_initial_val = i_g1_initial;
        g1_mode_val = i_g1_mode;
        g1_time_delay_val = i_g1_time_delay;

        g2_high_val = i_g2_high;
        g2_low_val = i_g2_low;
        g2_initial_val = i_g2_initial;
        g2_mode_val = i_g2_mode;
        g2_time_delay_val = i_g2_time_delay;

        g3_high_val = i_g3_high;
        g3_low_val = i_g3_low;
        g3_initial_val = i_g3_initial;
        g3_mode_val = i_g3_mode;
        g3_time_delay_val = i_g3_time_delay;

        e0_high_val = i_e0_high;
        e0_low_val = i_e0_low;
        e0_initial_val = i_e0_initial;
        e0_mode_val = i_e0_mode;
        e0_time_delay_val = i_e0_time_delay;

        e1_high_val = i_e1_high;
        e1_low_val = i_e1_low;
        e1_initial_val = i_e1_initial;
        e1_mode_val = i_e1_mode;
        e1_time_delay_val = i_e1_time_delay;

        e2_high_val = i_e2_high;
        e2_low_val = i_e2_low;
        e2_initial_val = i_e2_initial;
        e2_mode_val = i_e2_mode;
        e2_time_delay_val = i_e2_time_delay;

        e3_high_val = i_e3_high;
        e3_low_val = i_e3_low;
        e3_initial_val = i_e3_initial;
        e3_mode_val = i_e3_mode;
        e3_time_delay_val = i_e3_time_delay;

        i = 0;
        j = 0;
        inclk_last_value = 0;

        ext_fbk_cntr_ph = 0;
        ext_fbk_cntr_initial = 1;

        // initialize clkswitch variables

        clk0_is_bad = 0;
        clk1_is_bad = 0;
        inclk0_last_value = 0;
        inclk1_last_value = 0;
        other_clock_value = 0;
        other_clock_last_value = 0;
        primary_clk_is_bad = 0;
        current_clk_is_bad = 0;
        external_switch = 0;
//        current_clock = l_primary_clock;
        if (l_primary_clock == "inclk0")
            current_clock = 0;
        else
            current_clock = 1;
        if (l_primary_clock == "inclk0")
            active_clock = 0;
        else
            active_clock = 1;
        clkloss_tmp = 0;
        got_curr_clk_falling_edge_after_clkswitch = 0;
        clk0_count = 0;
        clk1_count = 0;
        switch_over_count = 0;
        active_clk_was_switched = 0;

        // initialize quiet_time
        quiet_time = slowest_clk  ( l0_high_val+l0_low_val, l0_mode_val,
                                    l1_high_val+l1_low_val, l1_mode_val,
                                    g0_high_val+g0_low_val, g0_mode_val,
                                    g1_high_val+g1_low_val, g1_mode_val,
                                    g2_high_val+g2_low_val, g2_mode_val,
                                    g3_high_val+g3_low_val, g3_mode_val,
                                    e0_high_val+e0_low_val, e0_mode_val,
                                    e1_high_val+e1_low_val, e1_mode_val,
                                    e2_high_val+e2_low_val, e2_mode_val,
                                    e3_high_val+e3_low_val, e3_mode_val,
                                    l_scan_chain,
                                    refclk_period, m_val);
        pll_in_quiet_period = 0;
        start_quiet_time = 0; 
        quiet_period_violation = 0;
        reconfig_err = 0;
        scanclr_violation = 0;
        scanclr_clk_violation = 0;
        got_first_scanclk_after_scanclr_inactive_edge = 0;
        error = 0;
        scanaclr_rising_time = 0;
        scanaclr_falling_time = 0;

        // VCO feedback loop settings for external feedback mode
        // first find which ext counter is used for feedback

        if (l_operation_mode == "external_feedback")
        begin
            if (l_feedback_source == "extclk0")
            begin
                if (i_extclk0_counter == "e0")
                    ext_fbk_cntr = "e0";
                else if (i_extclk0_counter == "e1")
                    ext_fbk_cntr = "e1";
                else if (i_extclk0_counter == "e2")
                    ext_fbk_cntr = "e2";
                else if (i_extclk0_counter == "e3")
                    ext_fbk_cntr = "e3";
                else ext_fbk_cntr = "e0";
            end
            else if (l_feedback_source == "extclk1")
            begin
                if (i_extclk1_counter == "e0")
                    ext_fbk_cntr = "e0";
                else if (i_extclk1_counter == "e1")
                    ext_fbk_cntr = "e1";
                else if (i_extclk1_counter == "e2")
                    ext_fbk_cntr = "e2";
                else if (i_extclk1_counter == "e3")
                    ext_fbk_cntr = "e3";
                else ext_fbk_cntr = "e0";
            end
            else if (l_feedback_source == "extclk2")
            begin
                if (i_extclk2_counter == "e0")
                    ext_fbk_cntr = "e0";
                else if (i_extclk2_counter == "e1")
                    ext_fbk_cntr = "e1";
                else if (i_extclk2_counter == "e2")
                    ext_fbk_cntr = "e2";
                else if (i_extclk2_counter == "e3")
                    ext_fbk_cntr = "e3";
                else ext_fbk_cntr = "e0";
            end
            else if (l_feedback_source == "extclk3")
            begin
                if (i_extclk3_counter == "e0")
                    ext_fbk_cntr = "e0";
                else if (i_extclk3_counter == "e1")
                    ext_fbk_cntr = "e1";
                else if (i_extclk3_counter == "e2")
                    ext_fbk_cntr = "e2";
                else if (i_extclk3_counter == "e3")
                    ext_fbk_cntr = "e3";
                else ext_fbk_cntr = "e0";
            end

            // now save this counter's parameters
            if (ext_fbk_cntr == "e0")
            begin
                ext_fbk_cntr_high = e0_high_val;
                ext_fbk_cntr_low = e0_low_val;
                ext_fbk_cntr_ph = i_e0_ph;
                ext_fbk_cntr_initial = i_e0_initial;
                ext_fbk_cntr_delay = e0_time_delay_val;
                ext_fbk_cntr_mode = e0_mode_val;
            end
            else if (ext_fbk_cntr == "e1")
            begin
                ext_fbk_cntr_high = e1_high_val;
                ext_fbk_cntr_low = e1_low_val;
                ext_fbk_cntr_ph = i_e1_ph;
                ext_fbk_cntr_initial = i_e1_initial;
                ext_fbk_cntr_delay = e1_time_delay_val;
                ext_fbk_cntr_mode = e1_mode_val;
            end
            else if (ext_fbk_cntr == "e2")
            begin
                ext_fbk_cntr_high = e2_high_val;
                ext_fbk_cntr_low = e2_low_val;
                ext_fbk_cntr_ph = i_e2_ph;
                ext_fbk_cntr_initial = i_e2_initial;
                ext_fbk_cntr_delay = e2_time_delay_val;
                ext_fbk_cntr_mode = e2_mode_val;
            end
            else if (ext_fbk_cntr == "e3")
            begin
                ext_fbk_cntr_high = e3_high_val;
                ext_fbk_cntr_low = e3_low_val;
                ext_fbk_cntr_ph = i_e3_ph;
                ext_fbk_cntr_initial = i_e3_initial;
                ext_fbk_cntr_delay = e3_time_delay_val;
                ext_fbk_cntr_mode = e3_mode_val;
            end

            if (ext_fbk_cntr_mode == "bypass")
                ext_fbk_cntr_modulus = 1;
            else
                ext_fbk_cntr_modulus = ext_fbk_cntr_high + ext_fbk_cntr_low;
        end

        l_index = 1;
        stop_vco = 0;
        cycles_to_lock = 0;
        cycles_to_unlock = 0;
        if (l_pll_type == "fast")
            locked_tmp = 1;
        else
            locked_tmp = 0;
        pll_is_locked = 0;
        pll_about_to_lock = 0;

        no_warn = 0;
        m_val_tmp = m_val;
        n_val_tmp = n_val;

        pll_is_in_reset = 0;
        if (l_pll_type == "fast" || l_pll_type == "lvds")
            is_fast_pll = 1;
        else is_fast_pll = 0;
    end

    assign inclk_m  =   l_operation_mode == "external_feedback" ? (l_feedback_source == "extclk0" ? extclk0_tmp :
                        l_feedback_source == "extclk1" ? extclk1_tmp :
                        l_feedback_source == "extclk2" ? extclk2_tmp :
                        l_feedback_source == "extclk3" ? extclk3_tmp : 1'b0) :
                        vco_out[m_ph_val];

    stx_m_cntr m1 (.clk(inclk_m),
                .reset(areset_ipd || (!ena_ipd) || stop_vco),
                .cout(fbclk),
                .initial_value(m_initial_val),
                .modulus(m_val),
                .time_delay(m_delay));

    always @(clkswitch_ipd)
    begin
        if (clkswitch_ipd == 1'b1)
            external_switch = 1;
        clkloss_tmp <= clkswitch_ipd;
    end

    always @(inclk0_ipd or inclk1_ipd)
    begin
        // save the inclk event value
        if (inclk0_ipd !== inclk0_last_value)
        begin
            if (current_clock !== 0)
                other_clock_value = inclk0_ipd;
        end
        if (inclk1_ipd !== inclk1_last_value)
        begin
            if (current_clock !== 1)
                other_clock_value = inclk1_ipd;
        end

        // check if either input clk is bad
        if (inclk0_ipd === 1'b1 && inclk0_ipd !== inclk0_last_value)
        begin
            clk0_count = clk0_count + 1;
            clk0_is_bad = 0;
            if (current_clock == 0)
                current_clk_is_bad = 0;
            clk1_count = 0;
            if (clk0_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk1_is_bad = 1;
                if (current_clock == 1)
                    current_clk_is_bad = 1;
            end
        end
        if (inclk1_ipd === 1'b1 && inclk1_ipd !== inclk1_last_value)
        begin
            clk1_count = clk1_count + 1;
            clk1_is_bad = 0;
            if (current_clock == 1)
                current_clk_is_bad = 0;
            clk0_count = 0;
            if (clk1_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk0_is_bad = 1;
                if (current_clock == 0)
                    current_clk_is_bad = 1;
            end
        end

        // check if the bad clk is the primary clock
        if (((l_primary_clock == "inclk0") && (clk0_is_bad == 1'b1)) || ((l_primary_clock == "inclk1") && (clk1_is_bad == 1'b1)))
            primary_clk_is_bad = 1;
        else
            primary_clk_is_bad = 0;

        // actual switching
        if ((inclk0_ipd !== inclk0_last_value) && (current_clock == 0))
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk0_ipd === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_n = inclk0_ipd;
                end
            end
            else inclk_n = inclk0_ipd;
        end
        if ((inclk1_ipd !== inclk1_last_value) && (current_clock == 1))
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk1_ipd === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_n = inclk1_ipd;
                end
            end
            else inclk_n = inclk1_ipd;
        end
        if ((other_clock_value == 1'b1) && (other_clock_value != other_clock_last_value) && (l_switch_over_on_lossclk == "on") && (l_enable_switch_over_counter == "on") && primary_clk_is_bad)
            switch_over_count = switch_over_count + 1;
        if ((other_clock_value == 1'b0) && (other_clock_value != other_clock_last_value))
        begin
            if ((external_switch && (got_curr_clk_falling_edge_after_clkswitch || current_clk_is_bad)) || (l_switch_over_on_lossclk == "on" && primary_clk_is_bad && ((l_enable_switch_over_counter == "off" || switch_over_count == switch_over_counter))))
            begin
                got_curr_clk_falling_edge_after_clkswitch = 0;
                if (current_clock == 0)
                begin
                    current_clock = 1;
                end
                else
                begin
                    current_clock = 0;
                end
                active_clock = ~active_clock;
                active_clk_was_switched = 1;
                switch_over_count = 0;
                external_switch = 0;
                current_clk_is_bad = 0;
            end
        end

        if (l_switch_over_on_lossclk == "on" && (clkswitch_ipd != 1'b1))
        begin
            if (primary_clk_is_bad)
                clkloss_tmp = 1;
            else
                clkloss_tmp = 0;
        end

        inclk0_last_value = inclk0_ipd;
        inclk1_last_value = inclk1_ipd;
        other_clock_last_value = other_clock_value;

    end

    and (clkbad[0], clk0_is_bad, 1'b1);
    and (clkbad[1], clk1_is_bad, 1'b1);
    and (activeclock, active_clock, 1'b1);
    and (clkloss, clkloss_tmp, 1'b1);

    stx_n_cntr n1 ( .clk(inclk_n),
                        .reset(areset_ipd),
                        .cout(refclk),
                        .modulus(n_val),
                        .time_delay(n_time_delay_val));

    stx_scale_cntr l0 ( .clk(vco_out[i_l0_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(l0_clk),
                            .high(l0_high_val),
                            .low(l0_low_val),
                            .initial_value(l0_initial_val),
                            .mode(l0_mode_val),
                            .time_delay(l0_time_delay_val),
                            .ph_tap(i_l0_ph));

    stx_scale_cntr l1 ( .clk(vco_out[i_l1_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(l1_clk),
                            .high(l1_high_val),
                            .low(l1_low_val),
                            .initial_value(l1_initial_val),
                            .mode(l1_mode_val),
                            .time_delay(l1_time_delay_val),
                            .ph_tap(i_l1_ph));

    stx_scale_cntr g0 ( .clk(vco_out[i_g0_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(g0_clk),
                            .high(g0_high_val),
                            .low(g0_low_val),
                            .initial_value(g0_initial_val),
                            .mode(g0_mode_val),
                            .time_delay(g0_time_delay_val),
                            .ph_tap(i_g0_ph));

    MF_pll_reg lvds_dffa ( .d(comparator_ipd),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(g0_clk),
                                .q(dffa_out));

    MF_pll_reg lvds_dffb ( .d(dffa_out),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(lvds_dffb_clk),
                                .q(dffb_out));

    assign lvds_dffb_clk = (l_enable0_counter == "l0") ? l0_clk : (l_enable0_counter == "l1") ? l1_clk : 1'b0;

    MF_pll_reg lvds_dffc ( .d(dffb_out),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(lvds_dffc_clk),
                                .q(dffc_out));

    assign lvds_dffc_clk = (l_enable0_counter == "l0") ? l0_clk : (l_enable0_counter == "l1") ? l1_clk : 1'b0;

    assign nce_temp = ~dffc_out && dffb_out;

    MF_pll_reg lvds_dffd ( .d(nce_temp),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(~lvds_dffd_clk),
                                .q(dffd_out));

    assign lvds_dffd_clk = (l_enable0_counter == "l0") ? l0_clk : (l_enable0_counter == "l1") ? l1_clk : 1'b0;

    assign nce_l0 = (l_enable0_counter == "l0") ? dffd_out : 1'b0;
    assign nce_l1 = (l_enable0_counter == "l1") ? dffd_out : 1'b0;

    stx_scale_cntr g1 ( .clk(vco_out[i_g1_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(g1_clk),
                            .high(g1_high_val),
                            .low(g1_low_val),
                            .initial_value(g1_initial_val),
                            .mode(g1_mode_val),
                            .time_delay(g1_time_delay_val),
                            .ph_tap(i_g1_ph));

    stx_scale_cntr g2 ( .clk(vco_out[i_g2_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(g2_clk),
                            .high(g2_high_val),
                            .low(g2_low_val),
                            .initial_value(g2_initial_val),
                            .mode(g2_mode_val),
                            .time_delay(g2_time_delay_val),
                            .ph_tap(i_g2_ph));

    stx_scale_cntr g3 ( .clk(vco_out[i_g3_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(g3_clk),
                            .high(g3_high_val),
                            .low(g3_low_val),
                            .initial_value(g3_initial_val),
                            .mode(g3_mode_val),
                            .time_delay(g3_time_delay_val),
                            .ph_tap(i_g3_ph));
    assign cntr_e0_initial = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e0") ? 1 : e0_initial_val;
    assign cntr_e0_delay = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e0") ? ext_fbk_delay : e0_time_delay_val;

    stx_scale_cntr e0 ( .clk(vco_out[i_e0_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(e0_clk),
                            .high(e0_high_val),
                            .low(e0_low_val),
                            .initial_value(cntr_e0_initial),
                            .mode(e0_mode_val),
                            .time_delay(cntr_e0_delay),
                            .ph_tap(i_e0_ph));

    assign cntr_e1_initial = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e1") ? 1 : e1_initial_val;
    assign cntr_e1_delay = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e1") ? ext_fbk_delay : e1_time_delay_val;
    stx_scale_cntr e1 ( .clk(vco_out[i_e1_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(e1_clk),
                            .high(e1_high_val),
                            .low(e1_low_val),
                            .initial_value(cntr_e1_initial),
                            .mode(e1_mode_val),
                            .time_delay(cntr_e1_delay),
                            .ph_tap(i_e1_ph));

    assign cntr_e2_initial = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e2") ? 1 : e2_initial_val;
    assign cntr_e2_delay = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e2") ? ext_fbk_delay : e2_time_delay_val;
    stx_scale_cntr e2 ( .clk(vco_out[i_e2_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(e2_clk),
                            .high(e2_high_val),
                            .low(e2_low_val),
                            .initial_value(cntr_e2_initial),
                            .mode(e2_mode_val),
                            .time_delay(cntr_e2_delay),
                            .ph_tap(i_e2_ph));

    assign cntr_e3_initial = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e3") ? 1 : e3_initial_val;
    assign cntr_e3_delay = (l_operation_mode == "external_feedback" && ext_fbk_cntr == "e3") ? ext_fbk_delay : e3_time_delay_val;
    stx_scale_cntr e3 ( .clk(vco_out[i_e3_ph]),
                            .reset(areset_ipd || (!ena_ipd) || stop_vco),
                            .cout(e3_clk),
                            .high(e3_high_val),
                            .low(e3_low_val),
                            .initial_value(cntr_e3_initial),
                            .mode(e3_mode_val),
                            .time_delay(cntr_e3_delay),
                            .ph_tap(i_e3_ph));


    always @((vco_out[i_l0_ph] && is_fast_pll) or posedge areset_ipd or negedge ena_ipd or stop_vco)
    begin
        if ((areset_ipd == 1'b1) || (ena_ipd == 1'b0) || (stop_vco == 1'b1))
        begin
            l0_count = 1;
            l0_got_first_rising_edge = 0;
        end
        else begin
            if (nce_l0 == 1'b0)
            begin
                if (l0_got_first_rising_edge == 1'b0)
                begin
                    if (vco_out[i_l0_ph] == 1'b1 && vco_out[i_l0_ph] != vco_l0_last_value)
                        l0_got_first_rising_edge = 1;
                end
                else if (vco_out[i_l0_ph] != vco_l0_last_value)
                begin
                    l0_count = l0_count + 1;
                    if (l0_count == (l0_high_val + l0_low_val) * 2)
                        l0_count  = 1;
                end
            end
            if (vco_out[i_l0_ph] == 1'b0 && vco_out[i_l0_ph] != vco_l0_last_value)
            begin
                if (l0_count == 1)
                begin
                    l0_tmp = 1;
                    l0_got_first_rising_edge = 0;
                end
                else l0_tmp = 0;
            end
        end
        vco_l0_last_value = vco_out[i_l0_ph];
    end

    always @((vco_out[i_l1_ph] && is_fast_pll) or posedge areset_ipd or negedge ena_ipd or stop_vco)
    begin
        if (areset_ipd == 1'b1 || ena_ipd == 1'b0 || stop_vco == 1'b1)
        begin
            l1_count = 1;
            l1_got_first_rising_edge = 0;
        end
        else begin
            if (nce_l1 == 1'b0)
            begin
                if (l1_got_first_rising_edge == 1'b0)
                begin
                    if (vco_out[i_l1_ph] == 1'b1 && vco_out[i_l1_ph] != vco_l1_last_value)
                        l1_got_first_rising_edge = 1;
                end
                else if (vco_out[i_l1_ph] != vco_l1_last_value)
                begin
                    l1_count = l1_count + 1;
                    if (l1_count == (l1_high_val + l1_low_val) * 2)
                        l1_count  = 1;
                end
            end
            if (vco_out[i_l1_ph] == 1'b0 && vco_out[i_l1_ph] != vco_l1_last_value)
            begin
                if (l1_count == 1)
                begin
                    l1_tmp = 1;
                    l1_got_first_rising_edge = 0;
                end
                else l1_tmp = 0;
            end
        end
        vco_l1_last_value = vco_out[i_l1_ph];
    end

    assign enable0_tmp = (l_enable0_counter == "l0") ? l0_tmp : l1_tmp;
    assign enable1_tmp = (l_enable1_counter == "l0") ? l0_tmp : l1_tmp;

    always @ (inclk_n or ena_ipd or areset_ipd)
    begin
        if (areset_ipd == 'b1)
        begin
            gate_count = 0;
            gate_out = 0; 
        end
        else if (inclk_n == 'b1 && inclk_last_value != inclk_n)
            if (ena_ipd == 'b1)
            begin
                gate_count = gate_count + 1;
                if (gate_count == gate_lock_counter)
                    gate_out = 1;
            end
        inclk_last_value = inclk_n;
    end

    assign locked = (l_gate_lock_signal == "yes") ? gate_out && locked_tmp : locked_tmp;

    always @ (scanclk_ipd or scanaclr_ipd)
    begin
        if (scanaclr_ipd === 1'b1 && scanaclr_last_value === 1'b0)
            scanaclr_rising_time = $time;
        else if (scanaclr_ipd === 1'b0 && scanaclr_last_value === 1'b1)
        begin
            scanaclr_falling_time = $time;
            // check for scanaclr active pulse width
            if ($time - scanaclr_rising_time < TRST)
            begin
                scanclr_violation = 1;
                $display ("Warning : Detected SCANACLR ACTIVE pulse width violation. Required is 5000 ps, actual is %0t. Reconfiguration may not work.", $time - scanaclr_rising_time);
                $display ("Time: %0t  Instance: %m", $time);
            end
            else begin
                scanclr_violation = 0;
                for (i = 0; i <= scan_chain_length; i = i + 1)
                    scan_data[i] = 0;
            end
            got_first_scanclk_after_scanclr_inactive_edge = 0;
        end
        else if ((scanclk_ipd === 'b1 && scanclk_last_value !== scanclk_ipd) && (got_first_scanclk_after_scanclr_inactive_edge === 1'b0) && ($time - scanaclr_falling_time < TRSTCLK))
        begin
            scanclr_clk_violation = 1;
            $display ("Warning : Detected SCANACLR INACTIVE time violation before rising edge of SCANCLK. Required is 5000 ps, actual is %0t. Reconfiguration may not work.", $time - scanaclr_falling_time);
            $display ("Time: %0t  Instance: %m", $time);
            got_first_scanclk_after_scanclr_inactive_edge = 1;
        end
        else if (scanclk_ipd == 'b1 && scanclk_last_value != scanclk_ipd && scanaclr_ipd === 1'b0)
        begin
            if (pll_in_quiet_period && ($time - start_quiet_time < quiet_time))
            begin
                $display("Time: %0t", $time, "   Warning : Detected transition on SCANCLK during quiet time. PLL may not function correctly."); 
                $display ("Time: %0t  Instance: %m", $time);
                quiet_period_violation = 1;
            end
            else begin
                pll_in_quiet_period = 0;
                for (j = scan_chain_length-1; j >= 1; j = j - 1)
                begin
                    scan_data[j] = scan_data[j - 1];
                end
                scan_data[0] = scandata_ipd;
            end
            if (got_first_scanclk_after_scanclr_inactive_edge === 1'b0)
            begin
                got_first_scanclk_after_scanclr_inactive_edge = 1;
                scanclr_clk_violation = 0;
            end
        end
        else if (scanclk_ipd === 1'b0 && scanclk_last_value !== scanclk_ipd && scanaclr_ipd === 1'b0)
        begin
            if (pll_in_quiet_period && ($time - start_quiet_time < quiet_time))
            begin
                $display("Time: %0t", $time, "   Warning : Detected transition on SCANCLK during quiet time. PLL may not function correctly."); 
                $display ("Time: %0t  Instance: %m", $time);
                quiet_period_violation = 1;
            end
            else if (scan_data[scan_chain_length-1] == 1'b1)
            begin
                pll_in_quiet_period = 1;
                quiet_period_violation = 0;
                reconfig_err = 0;
                start_quiet_time = $time;
                // initiate transfer
                scandataout_tmp <= 1'b1;
                quiet_time = slowest_clk  ( l0_high_val+l0_low_val, l0_mode_val,
                                            l1_high_val+l1_low_val, l1_mode_val,
                                            g0_high_val+g0_low_val, g0_mode_val,
                                            g1_high_val+g1_low_val, g1_mode_val,
                                            g2_high_val+g2_low_val, g2_mode_val,
                                            g3_high_val+g3_low_val, g3_mode_val,
                                            e0_high_val+e0_low_val, e0_mode_val,
                                            e1_high_val+e1_low_val, e1_mode_val,
                                            e2_high_val+e2_low_val, e2_mode_val,
                                            e3_high_val+e3_low_val, e3_mode_val,
                                            l_scan_chain,
                                            refclk_period, m_val);
                scandataout_trigger <= #(quiet_time) ~scandataout_trigger;
                transfer <= 1;
            end
        end
        scanclk_last_value = scanclk_ipd;
        scanaclr_last_value = scanaclr_ipd;
    end

    always @(scandataout_trigger)
    begin
        if (areset_ipd === 1'b0)
            scandataout_tmp <= 1'b0;
    end

    always @(posedge transfer)
    begin
        if (transfer == 1'b1)
        begin
            $display("NOTE : Reconfiguring PLL");
            $display ("Time: %0t  Instance: %m", $time);
            if (l_scan_chain == "long")
            begin
                // cntr e3
                error = 0;
                if (scan_data[273] == 1'b1)
                begin
                    e3_mode_val = "bypass";
                    if (scan_data[283] == 1'b1)
                    begin
                        e3_mode_val = "off";
                        $display("Warning : The specified bit settings will turn OFF the E3 counter. It cannot be turned on unless the part is re-initialized.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (scan_data[283] == 1'b1)
                    e3_mode_val = "odd";
                else
                    e3_mode_val = "even";
                // before reading delay bits, clear e3_time_delay_val
                e3_time_delay_val = 32'b0;
                e3_time_delay_val = scan_data[287:284];
                e3_time_delay_val = e3_time_delay_val * 250;
                if (e3_time_delay_val > 3000)
                    e3_time_delay_val = 3000;
                e3_high_val[8:0] <= scan_data[272:264];
                e3_low_val[8:0] <= scan_data[282:274];
                if (scan_data[272:264] == 9'b000000000)
                    e3_high_val[9:0] <= 10'b1000000000;
                else
                    e3_high_val[9] <= 1'b0;
                if (scan_data[282:274] == 9'b000000000)
                    e3_low_val[9:0] <= 10'b1000000000;
                else
                    e3_low_val[9] <= 1'b0;

                if (ext_fbk_cntr == "e3")
                begin
                    ext_fbk_cntr_high = e3_high_val;
                    ext_fbk_cntr_low = e3_low_val;
                    ext_fbk_cntr_delay = e3_time_delay_val;
                    ext_fbk_cntr_mode = e3_mode_val;
                end

                // cntr e2
                if (scan_data[249] == 1'b1)
                begin
                    e2_mode_val = "bypass";
                    if (scan_data[259] == 1'b1)
                    begin
                        e2_mode_val = "off";
                        $display("Warning : The specified bit settings will turn OFF the E2 counter. It cannot be turned on unless the part is re-initialized.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (scan_data[259] == 1'b1)
                    e2_mode_val = "odd";
                else
                    e2_mode_val = "even";
                e2_time_delay_val = 32'b0;
                e2_time_delay_val = scan_data[263:260];
                e2_time_delay_val = e2_time_delay_val * 250;
                if (e2_time_delay_val > 3000)
                    e2_time_delay_val = 3000;
                e2_high_val[8:0] <= scan_data[248:240];
                e2_low_val[8:0] <= scan_data[258:250];
                if (scan_data[248:240] == 9'b000000000)
                    e2_high_val[9:0] <= 10'b1000000000;
                else
                    e2_high_val[9] <= 1'b0;
                if (scan_data[258:250] == 9'b000000000)
                    e2_low_val[9:0] <= 10'b1000000000;
                else
                    e2_low_val[9] <= 1'b0;

                if (ext_fbk_cntr == "e2")
                begin
                    ext_fbk_cntr_high = e2_high_val;
                    ext_fbk_cntr_low = e2_low_val;
                    ext_fbk_cntr_delay = e2_time_delay_val;
                    ext_fbk_cntr_mode = e2_mode_val;
                end

                // cntr e1
                if (scan_data[225] == 1'b1)
                begin
                    e1_mode_val = "bypass";
                    if (scan_data[235] == 1'b1)
                    begin
                        e1_mode_val = "off";
                        $display("Warning : The specified bit settings will turn OFF the E1 counter. It cannot be turned on unless the part is re-initialized.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (scan_data[235] == 1'b1)
                    e1_mode_val = "odd";
                else
                    e1_mode_val = "even";
                e1_time_delay_val = 32'b0;
                e1_time_delay_val = scan_data[239:236];
                e1_time_delay_val = e1_time_delay_val * 250;
                if (e1_time_delay_val > 3000)
                    e1_time_delay_val = 3000;
                e1_high_val[8:0] <= scan_data[224:216];
                e1_low_val[8:0] <= scan_data[234:226];
                if (scan_data[224:216] == 9'b000000000)
                    e1_high_val[9:0] <= 10'b1000000000;
                else
                    e1_high_val[9] <= 1'b0;
                if (scan_data[234:226] == 9'b000000000)
                    e1_low_val[9:0] <= 10'b1000000000;
                else
                    e1_low_val[9] <= 1'b0;

                if (ext_fbk_cntr == "e1")
                begin
                    ext_fbk_cntr_high = e1_high_val;
                    ext_fbk_cntr_low = e1_low_val;
                    ext_fbk_cntr_delay = e1_time_delay_val;
                    ext_fbk_cntr_mode = e1_mode_val;
                end

                // cntr e0
                if (scan_data[201] == 1'b1)
                begin
                    e0_mode_val = "bypass";
                    if (scan_data[211] == 1'b1)
                    begin
                        e0_mode_val = "off";
                        $display("Warning : The specified bit settings will turn OFF the E0 counter. It cannot be turned on unless the part is re-initialized.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
                else if (scan_data[211] == 1'b1)
                    e0_mode_val = "odd";
                else
                    e0_mode_val = "even";
                e0_time_delay_val = 32'b0;
                e0_time_delay_val = scan_data[215:212];
                e0_time_delay_val = e0_time_delay_val * 250;
                if (e0_time_delay_val > 3000)
                    e0_time_delay_val = 3000;
                e0_high_val[8:0] <= scan_data[200:192];
                e0_low_val[8:0] <= scan_data[210:202];
                if (scan_data[200:192] == 9'b000000000)
                    e0_high_val[9:0] <= 10'b1000000000;
                else
                    e0_high_val[9] <= 1'b0;
                if (scan_data[210:202] == 9'b000000000)
                    e0_low_val[9:0] <= 10'b1000000000;
                else
                    e0_low_val[9] <= 1'b0;

                if (ext_fbk_cntr == "e0")
                begin
                    ext_fbk_cntr_high = e0_high_val;
                    ext_fbk_cntr_low = e0_low_val;
                    ext_fbk_cntr_delay = e0_time_delay_val;
                    ext_fbk_cntr_mode = e0_mode_val;
                end
            end

            // cntr l1
            if (scan_data[177] == 1'b1)
            begin
                l1_mode_val = "bypass";
                if (scan_data[187] == 1'b1)
                begin
                    l1_mode_val = "off";
                    $display("Warning : The specified bit settings will turn OFF the L1 counter. It cannot be turned on unless the part is re-initialized.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end
            else if (scan_data[187] == 1'b1)
                l1_mode_val = "odd";
            else
                l1_mode_val = "even";
            l1_time_delay_val = 32'b0;
            l1_time_delay_val = scan_data[191:188];
            l1_time_delay_val = l1_time_delay_val * 250;
            if (l1_time_delay_val > 3000)
                l1_time_delay_val = 3000;
            l1_high_val[8:0] <= scan_data[176:168];
            l1_low_val[8:0] <= scan_data[186:178];
            if (scan_data[176:168] == 9'b000000000)
                l1_high_val[9:0] <= 10'b1000000000;
            else
                l1_high_val[9] <= 1'b0;
            if (scan_data[186:178] == 9'b000000000)
                l1_low_val[9:0] <= 10'b1000000000;
            else
                l1_low_val[9] <= 1'b0;

            // cntr l0
            if (scan_data[153] == 1'b1)
            begin
                l0_mode_val = "bypass";
                if (scan_data[163] == 1'b1)
                begin
                    l0_mode_val = "off";
                    $display("Warning : The specified bit settings will turn OFF the L0 counter. It cannot be turned on unless the part is re-initialized.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end
            else if (scan_data[163] == 1'b1)
                l0_mode_val = "odd";
            else
                l0_mode_val = "even";
            l0_time_delay_val = 32'b0;
            l0_time_delay_val = scan_data[167:164];
            l0_time_delay_val = l0_time_delay_val * 250;
            if (l0_time_delay_val > 3000)
                l0_time_delay_val = 3000;
            l0_high_val[8:0] <= scan_data[152:144];
            l0_low_val[8:0] <= scan_data[162:154];
            if (scan_data[152:144] == 9'b000000000)
                l0_high_val[9:0] <= 10'b1000000000;
            else
                l0_high_val[9] <= 1'b0;
            if (scan_data[162:154] == 9'b000000000)
                l0_low_val[9:0] <= 10'b1000000000;
            else
                l0_low_val[9] <= 1'b0;

            // cntr g3
            if (scan_data[129] == 1'b1)
            begin
                g3_mode_val = "bypass";
                if (scan_data[139] == 1'b1)
                begin
                    g3_mode_val = "off";
                    $display("Warning : The specified bit settings will turn OFF the G3 counter. It cannot be turned on unless the part is re-initialized.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end
            else if (scan_data[139] == 1'b1)
                g3_mode_val = "odd";
            else
                g3_mode_val = "even";
            g3_time_delay_val = 32'b0;
            g3_time_delay_val = scan_data[143:140];
            g3_time_delay_val = g3_time_delay_val * 250;
            if (g3_time_delay_val > 3000)
                g3_time_delay_val = 3000;
            g3_high_val[8:0] <= scan_data[128:120];
            g3_low_val[8:0] <= scan_data[138:130];
            if (scan_data[128:120] == 9'b000000000)
                g3_high_val[9:0] <= 10'b1000000000;
            else
                g3_high_val[9] <= 1'b0;
            if (scan_data[138:130] == 9'b000000000)
                g3_low_val[9:0] <= 10'b1000000000;
            else
                g3_low_val[9] <= 1'b0;

            // cntr g2
            if (scan_data[105] == 1'b1)
            begin
                g2_mode_val = "bypass";
                if (scan_data[115] == 1'b1)
                begin
                    g2_mode_val = "off";
                    $display("Warning : The specified bit settings will turn OFF the G2 counter. It cannot be turned on unless the part is re-initialized.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end
            else if (scan_data[115] == 1'b1)
                g2_mode_val = "odd";
            else
                g2_mode_val = "even";
            g2_time_delay_val = 32'b0;
            g2_time_delay_val = scan_data[119:116];
            g2_time_delay_val = g2_time_delay_val * 250;
            if (g2_time_delay_val > 3000)
                g2_time_delay_val = 3000;
            g2_high_val[8:0] <= scan_data[104:96];
            g2_low_val[8:0] <= scan_data[114:106];
            if (scan_data[104:96] == 9'b000000000)
                g2_high_val[9:0] <= 10'b1000000000;
            else
                g2_high_val[9] <= 1'b0;
            if (scan_data[114:106] == 9'b000000000)
                g2_low_val[9:0] <= 10'b1000000000;
            else
                g2_low_val[9] <= 1'b0;

            // cntr g1
            if (scan_data[81] == 1'b1)
            begin
                g1_mode_val = "bypass";
                if (scan_data[91] == 1'b1)
                begin
                    g1_mode_val = "off";
                    $display("Warning : The specified bit settings will turn OFF the G1 counter. It cannot be turned on unless the part is re-initialized.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end
            else if (scan_data[91] == 1'b1)
                g1_mode_val = "odd";
            else
                g1_mode_val = "even";
            g1_time_delay_val = 32'b0;
            g1_time_delay_val = scan_data[95:92];
            g1_time_delay_val = g1_time_delay_val * 250;
            if (g1_time_delay_val > 3000)
                g1_time_delay_val = 3000;
            g1_high_val[8:0] <= scan_data[80:72];
            g1_low_val[8:0] <= scan_data[90:82];
            if (scan_data[80:72] == 9'b000000000)
                g1_high_val[9:0] <= 10'b1000000000;
            else
                g1_high_val[9] <= 1'b0;
            if (scan_data[90:82] == 9'b000000000)
                g1_low_val[9:0] <= 10'b1000000000;
            else
                g1_low_val[9] <= 1'b0;

            // cntr g0
            if (scan_data[57] == 1'b1)
            begin
                g0_mode_val = "bypass";
                if (scan_data[67] == 1'b1)
                begin
                    g0_mode_val = "off";
                    $display("Warning : The specified bit settings will turn OFF the G0 counter. It cannot be turned on unless the part is re-initialized.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end
            else if (scan_data[67] == 1'b1)
                g0_mode_val = "odd";
            else
                g0_mode_val = "even";
            g0_time_delay_val = 32'b0;
            g0_time_delay_val = scan_data[71:68];
            g0_time_delay_val = g0_time_delay_val * 250;
            if (g0_time_delay_val > 3000)
                g0_time_delay_val = 3000;
            g0_high_val[8:0] <= scan_data[56:48];
            g0_low_val[8:0] <= scan_data[66:58];
            if (scan_data[56:48] == 9'b000000000)
                g0_high_val[9:0] <= 10'b1000000000;
            else
                g0_high_val[9] <= 1'b0;
            if (scan_data[66:58] == 9'b000000000)
                g0_low_val[9:0] <= 10'b1000000000;
            else
                g0_low_val[9] <= 1'b0;

            // cntr M
            error = 0;
            m_val_tmp = 0;
            m_val_tmp[8:0] = scan_data[32:24];
            if (scan_data[33] !== 1'b1)
            begin
                if (m_val_tmp[8:0] == 9'b000000001)
                begin
                    reconfig_err = 1;
                    error = 1;
                    $display ("Warning : Illegal 1 value for M counter. Instead, the M counter should be BYPASSED. Reconfiguration may not work.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                else if (m_val_tmp[8:0] == 9'b000000000)
                    m_val_tmp[9:0] = 10'b1000000000;
                if (error == 1'b0)
                begin
                    if (m_mode_val === "bypass")
                        $display ("Warning : M counter switched from BYPASS mode to enabled (M modulus = %d). PLL may lose lock.", m_val_tmp[9:0]);
                    else
                        $display("PLL reconfigured with : M modulus = %d ", m_val_tmp[9:0]);
                    $display ("Time: %0t  Instance: %m", $time);
                    m_mode_val = "";
                end
            end
            else if (scan_data[33] == 1'b1)
            begin
                if (scan_data[24] !== 1'b0)
                begin
                    reconfig_err = 1;
                    error = 1;
                    $display ("Warning : Illegal value for counter M in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                else begin
                    if (m_mode_val !== "bypass")
                        $display ("Warning : M counter switched from enabled to BYPASS mode. PLL may lose lock.");
                    m_val_tmp[9:0] = 10'b0000000001;
                    m_mode_val = "bypass";
                    $display("PLL reconfigured with : M modulus = %d ", m_val_tmp[9:0]);
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end

            if (skip_vco == "on")
                m_val_tmp[9:0] = 10'b0000000001;

            // cntr M2
            if (ss > 0)
            begin
                error = 0;
                m2_val[8:0] = scan_data[42:34];
                if (scan_data[43] !== 1'b1)
                begin
                    if (m2_val[8:0] == 9'b000000001)
                    begin
                        reconfig_err = 1;
                        error = 1;
                        $display ("Warning : Illegal 1 value for M2 counter. Instead, the M2 counter should be BYPASSED. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else if (m2_val[8:0] == 9'b000000000)
                        m2_val[9:0] = 10'b1000000000;
                    if (error == 1'b0)
                    begin
                        if (m2_mode_val === "bypass")
                        begin
                            $display ("Warning : M2 counter switched from BYPASS mode to enabled (M2 modulus = %d). Pll may lose lock.", m2_val[9:0]);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                        else
                        begin
                            $display(" M2 modulus = %d ", m2_val[9:0]);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                        m2_mode_val = "";
                    end
                end
                else if (scan_data[43] == 1'b1)
                begin
                    if (scan_data[34] !== 1'b0)
                    begin
                        reconfig_err = 1;
                        error = 1;
                        $display ("Warning : Illegal value for counter M2 in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else begin
                        if (m2_mode_val !== "bypass")
                        begin
                            $display ("Warning : M2 counter switched from enabled to BYPASS mode. PLL may lose lock.");
                        end
                        m2_val[9:0] = 10'b0000000001;
                        m2_mode_val = "bypass";
                        $display(" M2 modulus = %d ", m2_val[9:0]);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
                if (m_mode_val != m2_mode_val)
                begin
                    reconfig_err = 1;
                    error = 1;
                    $display ("Warning : Incompatible modes for M1/M2 counters. Either both should be BYASSED or both NON-BYPASSED. Reconfiguration may not work.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end

            m_time_delay_val = 32'b0;
            m_time_delay_val = scan_data[47:44];
            m_time_delay_val = m_time_delay_val * 250;
            if (m_time_delay_val > 3000)
                m_time_delay_val = 3000;
            if (skip_vco == "on")
                m_time_delay_val = 32'b0;
            $display("                                     M time delay = %0d", m_time_delay_val);
            $display ("Time: %0t  Instance: %m", $time);

            // cntr N
            error = 0;
            n_val_tmp[8:0] = scan_data[8:0];
            n_val_tmp[9] = 1'b0;
            if (scan_data[9] !== 1'b1)
            begin
                if (n_val_tmp[8:0] == 9'b000000001)
                begin
                    reconfig_err = 1;
                    error = 1;
                    $display ("Warning : Illegal 1 value for N counter. Instead, the N counter should be BYPASSED. Reconfiguration may not work.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                else if (n_val_tmp[8:0] == 9'b000000000)
                    n_val_tmp[9:0] = 10'b1000000000;
                if (error == 1'b0)
                begin
                    if (n_mode_val === "bypass")
                    begin
                        $display ("Warning : N counter switched from BYPASS mode to enabled (N modulus = %d). PLL may lose lock.", n_val_tmp[9:0]);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else
                    begin
                        $display("                                     N modulus = %d ", n_val_tmp[9:0]);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    n_mode_val = "";
                end
            end
            else if (scan_data[9] == 1'b1)     // bypass
            begin
                if (scan_data[0] !== 1'b0)
                begin
                    reconfig_err = 1;
                    error = 1;
                    $display ("Warning : Illegal value for counter N in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                else begin
                    if (n_mode_val !== "bypass")
                    begin
                        $display ("Warning : N counter switched from enabled to BYPASS mode. PLL may lose lock.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    n_val_tmp[9:0] = 10'b0000000001;
                    n_mode_val = "bypass";
                    $display("                                     N modulus = %d ", n_val_tmp[9:0]);
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end

            // cntr N2
            if (ss > 0)
            begin
                error = 0;
                n2_val[8:0] = scan_data[18:10];
                if (scan_data[19] !== 1'b1)
                begin
                    if (n2_val[8:0] == 9'b000000001)
                    begin
                        reconfig_err = 1;
                        error = 1;
                        $display ("Warning : Illegal 1 value for N2 counter. Instead, the N2 counter should be BYPASSED. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else if (n2_val[8:0] == 9'b000000000)
                        n2_val = 10'b1000000000;
                    if (error == 1'b0)
                    begin
                        if (n2_mode_val === "bypass")
                        begin
                            $display ("Warning : N2 counter switched from BYPASS mode to enabled (N2 modulus = %d). PLL may lose lock.", n2_val[9:0]);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                        else
                        begin
                            $display(" N2 modulus = %d ", n2_val[9:0]);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                        n2_mode_val = "";
                    end
                end
                else if (scan_data[19] == 1'b1)     // bypass
                begin
                    if (scan_data[10] !== 1'b0)
                    begin
                        reconfig_err = 1;
                        error = 1;
                        $display ("Warning : Illegal value for counter N2 in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else begin
                        if (n2_mode_val !== "bypass")
                        begin
                            $display ("Warning : N2 counter switched from enabled to BYPASS mode. PLL may lose lock.");
                            $display ("Time: %0t  Instance: %m", $time);
                        end    
                        n2_val[9:0] = 10'b0000000001;
                        n2_mode_val = "bypass";
                        $display(" N2 modulus = %d ", n2_val[9:0]);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
                if (n_mode_val != n2_mode_val)
                begin
                    reconfig_err = 1;
                    error = 1;
                    $display ("Warning : Incompatible modes for N1/N2 counters. Either both should be BYASSED or both NON-BYPASSED.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
            end // ss > 0

            n_time_delay_val = 32'b0;
            n_time_delay_val = scan_data[23:20];
            n_time_delay_val = n_time_delay_val * 250;
            if (n_time_delay_val > 3000)
                n_time_delay_val = 3000;
            $display("                                     N time delay = %0d", n_time_delay_val);
            $display ("Time: %0t  Instance: %m", $time);

            transfer <= 0;
            // clear the scan_chain
            for (i = 0; i <= scan_chain_length; i = i + 1)
                scan_data[i] = 0;
        end
    end

    always @(negedge transfer)
    begin
        if (l_scan_chain == "long")
        begin
            $display("                                     E3 high = %d, E3 low = %d, E3 mode = %s, E3 time delay = %0d", e3_high_val[9:0], e3_low_val[9:0], e3_mode_val, e3_time_delay_val);
            $display("                                     E2 high = %d, E2 low = %d, E2 mode = %s, E2 time delay = %0d", e2_high_val[9:0], e2_low_val[9:0], e2_mode_val, e2_time_delay_val);
            $display("                                     E1 high = %d, E1 low = %d, E1 mode = %s, E1 time delay = %0d", e1_high_val[9:0], e1_low_val[9:0], e1_mode_val, e1_time_delay_val);
            $display("                                     E0 high = %d, E0 low = %d, E0 mode = %s, E0 time delay = %0d", e0_high_val[9:0], e0_low_val[9:0], e0_mode_val, e0_time_delay_val);
        end
        $display("                                     L1 high = %d, L1 low = %d, L1 mode = %s, L1 time delay = %0d", l1_high_val[9:0], l1_low_val[9:0], l1_mode_val, l1_time_delay_val);
        $display("                                     L0 high = %d, L0 low = %d, L0 mode = %s, L0 time delay = %0d", l0_high_val[9:0], l0_low_val[9:0], l0_mode_val, l0_time_delay_val);
        $display("                                     G3 high = %d, G3 low = %d, G3 mode = %s, G3 time delay = %0d", g3_high_val[9:0], g3_low_val[9:0], g3_mode_val, g3_time_delay_val);
        $display("                                     G2 high = %d, G2 low = %d, G2 mode = %s, G2 time delay = %0d", g2_high_val[9:0], g2_low_val[9:0], g2_mode_val, g2_time_delay_val);
        $display("                                     G1 high = %d, G1 low = %d, G1 mode = %s, G1 time delay = %0d", g1_high_val[9:0], g1_low_val[9:0], g1_mode_val, g1_time_delay_val);
        $display("                                     G0 high = %d, G0 low = %d, G0 mode = %s, G0 time delay = %0d", g0_high_val[9:0], g0_low_val[9:0], g0_mode_val, g0_time_delay_val);
        $display ("Time: %0t  Instance: %m", $time);
    end

always @(schedule_vco or areset_ipd or ena_ipd)
begin
    sched_time = 0;

    for (i = 0; i <= 7; i=i+1)
        last_phase_shift[i] = phase_shift[i];
 
    cycle_to_adjust = 0;
    l_index = 1;
    m_times_vco_period = new_m_times_vco_period;

    // give appropriate messages
    // if areset was asserted
    if (areset_ipd == 1'b1 && areset_ipd_last_value !== areset_ipd)
    begin
        $display (" Note : %s PLL was reset", family_name);
        $display ("Time: %0t  Instance: %m", $time);
    end

    // if areset is deasserted
    if (areset_ipd === 1'b0 && areset_ipd_last_value === 1'b1)
    begin
        // deassert scandataout now and allow reconfig to complete if
        // areset was high during reconfig
        if (scandataout_tmp === 1'b1)
            scandataout_tmp <= #(quiet_time) 1'b0;
    end

    // if ena was deasserted
    if (ena_ipd == 1'b0 && ena_ipd_last_value !== ena_ipd)
    begin
        $display (" Note : %s PLL was disabled", family_name);
        $display ("Time: %0t  Instance: %m", $time);
    end

    // illegal value on areset_ipd
    if (areset_ipd === 1'bx && (areset_ipd_last_value === 1'b0 || areset_ipd_last_value === 1'b1))
    begin
        $display("Warning : Illegal value 'X' detected on ARESET input");
        $display ("Time: %0t  Instance: %m", $time);
    end

    if ((schedule_vco !== schedule_vco_last_value) && (areset_ipd == 1'b1 || ena_ipd == 1'b0 || stop_vco == 1'b1))
    begin
            if (areset_ipd === 1'b1)
                pll_is_in_reset = 1;

        // drop VCO taps to 0
        for (i = 0; i <= 7; i=i+1)
        begin
            for (j = 0; j <= last_phase_shift[i] + 1; j=j+1)
                vco_out[i] <= #(j) 1'b0;
            phase_shift[i] = 0;
            last_phase_shift[i] = 0;
        end

        // reset lock parameters
        locked_tmp = 0;
        if (l_pll_type == "fast")
            locked_tmp = 1;
        pll_is_locked = 0;
        pll_about_to_lock = 0;
        cycles_to_lock = 0;
        cycles_to_unlock = 0;

        got_first_refclk = 0;
        got_second_refclk = 0;
        refclk_time = 0;
        got_first_fbclk = 0;
        fbclk_time = 0;
        first_fbclk_time = 0;
        fbclk_period = 0;

        first_schedule = 1;
        schedule_offset = 1;
        vco_val = 0;
        vco_period_was_phase_adjusted = 0;
        phase_adjust_was_scheduled = 0;

        // reset enable0 and enable1 counter parameters
//      l0_count = 1;
//      l1_count = 1;
//      l0_got_first_rising_edge = 0;
//      l1_got_first_rising_edge = 0;

    end else if (ena_ipd === 1'b1 && areset_ipd === 1'b0 && stop_vco === 1'b0)
    begin

        // else note areset deassert time
        // note it as refclk_time to prevent false triggering
        // of stop_vco after areset
        if (areset_ipd === 1'b0 && areset_ipd_last_value === 1'b1 && pll_is_in_reset === 1'b1)
        begin
            refclk_time = $time;
            pll_is_in_reset = 0;
        end

        // calculate loop_xplier : this will be different from m_val in ext. fbk mode
        loop_xplier = m_val;
        loop_initial = i_m_initial - 1;
        loop_ph = i_m_ph;
        loop_time_delay = m_time_delay_val;

        if (l_operation_mode == "external_feedback")
        begin
            if (ext_fbk_cntr_mode == "bypass")
                ext_fbk_cntr_modulus = 1;
            else
                ext_fbk_cntr_modulus = ext_fbk_cntr_high + ext_fbk_cntr_low;

            loop_xplier = m_val * (ext_fbk_cntr_modulus);
            loop_ph = ext_fbk_cntr_ph;
            loop_initial = ext_fbk_cntr_initial - 1 + ((i_m_initial - 1) * (ext_fbk_cntr_modulus));
            loop_time_delay = m_time_delay_val + ext_fbk_cntr_delay;
        end

        // convert initial value to delay
        initial_delay = (loop_initial * m_times_vco_period)/loop_xplier;

        // convert loop ph_tap to delay
        rem = m_times_vco_period % loop_xplier;
        vco_per = m_times_vco_period/loop_xplier;
        if (rem != 0)
            vco_per = vco_per + 1;
        fbk_phase = (loop_ph * vco_per)/8;

        if (l_operation_mode == "external_feedback")
        begin
            pull_back_ext_cntr = ext_fbk_cntr_delay + (ext_fbk_cntr_initial - 1) * (m_times_vco_period/loop_xplier) + fbk_phase;

            while (pull_back_ext_cntr > refclk_period)
                pull_back_ext_cntr = pull_back_ext_cntr - refclk_period;

            pull_back_M =  m_time_delay_val + (i_m_initial - 1) * (ext_fbk_cntr_modulus) * (m_times_vco_period/loop_xplier);

            while (pull_back_M > refclk_period)
                pull_back_M = pull_back_M - refclk_period;
        end
        else begin
            pull_back_ext_cntr = 0;
            pull_back_M = initial_delay + m_time_delay_val + fbk_phase;
        end

        total_pull_back = pull_back_M + pull_back_ext_cntr;
        if (l_simulation_type == "timing")
            total_pull_back = total_pull_back + pll_compensation_delay;

        while (total_pull_back > refclk_period)
            total_pull_back = total_pull_back - refclk_period;

        if (total_pull_back > 0)
            offset = refclk_period - total_pull_back;

        if (l_operation_mode == "external_feedback")
        begin
            fbk_delay = pull_back_M;
            if (l_simulation_type == "timing")
                fbk_delay = fbk_delay + pll_compensation_delay;

            ext_fbk_delay = pull_back_ext_cntr - fbk_phase;
        end
        else begin
            fbk_delay = total_pull_back - fbk_phase;
            if (fbk_delay < 0)
            begin
                offset = offset - fbk_phase;
                fbk_delay = total_pull_back;
            end
        end

        // assign m_delay
        m_delay = fbk_delay;

        for (i = 1; i <= loop_xplier; i=i+1)
        begin
            // adjust cycles
            tmp_vco_per = m_times_vco_period/loop_xplier;
            if (rem != 0 && l_index <= rem)
            begin
                tmp_rem = (loop_xplier * l_index) % rem;
                cycle_to_adjust = (loop_xplier * l_index) / rem;
                if (tmp_rem != 0)
                    cycle_to_adjust = cycle_to_adjust + 1;
            end
            if (cycle_to_adjust == i)
            begin
                tmp_vco_per = tmp_vco_per + 1;
                l_index = l_index + 1;
            end

            // calculate high and low periods
            high_time = tmp_vco_per/2;
            if (tmp_vco_per % 2 != 0)
                high_time = high_time + 1;
            low_time = tmp_vco_per - high_time;

            // schedule the rising and falling egdes
            for (j=0; j<=1; j=j+1)
            begin
                vco_val = ~vco_val;
                if (vco_val == 1'b0)
                    sched_time = sched_time + high_time;
                else
                    sched_time = sched_time + low_time;

                // add offset
                if (schedule_offset == 1'b1)
                begin
                    sched_time = sched_time + offset;
                    schedule_offset = 0;
                end

                // schedule taps with appropriate phase shifts
                for (k = 0; k <= 7; k=k+1)
                begin
                    phase_shift[k] = (k*tmp_vco_per)/8;
                    if (first_schedule)
                        vco_out[k] <= #(sched_time + phase_shift[k]) vco_val;
                    else
                        vco_out[k] <= #(sched_time + last_phase_shift[k]) vco_val;
                end
            end
        end
        if (first_schedule)
        begin
            vco_val = ~vco_val;
            if (vco_val == 1'b0)
                sched_time = sched_time + high_time;
            else
                sched_time = sched_time + low_time;
            for (k = 0; k <= 7; k=k+1)
            begin
                phase_shift[k] = (k*tmp_vco_per)/8;
                vco_out[k] <= #(sched_time+phase_shift[k]) vco_val;
            end
            first_schedule = 0;
        end

        // this may no longer be required

        if (sched_time > 0)
            schedule_vco <= #(sched_time) ~schedule_vco;

        if (vco_period_was_phase_adjusted)
        begin
            m_times_vco_period = refclk_period;
            new_m_times_vco_period = refclk_period;
            vco_period_was_phase_adjusted = 0;
            phase_adjust_was_scheduled = 1;

            tmp_vco_per = m_times_vco_period/loop_xplier;
            for (k = 0; k <= 7; k=k+1)
                phase_shift[k] = (k*tmp_vco_per)/8;
        end
    end

    areset_ipd_last_value = areset_ipd;
    ena_ipd_last_value = ena_ipd;
    schedule_vco_last_value = schedule_vco;

end

always @(pfdena_ipd)
begin
    if (pfdena_ipd === 1'b0)
    begin
        locked_tmp = 1'bx;
        pll_is_locked = 0;
        cycles_to_lock = 0;
        $display (" Note : PFDENA was deasserted");
        $display ("Time: %0t  Instance: %m", $time);
    end
    else if (pfdena_ipd === 1'b1 && pfdena_ipd_last_value === 1'b0)
    begin
        // PFD was disabled, now enabled again
        got_first_refclk = 0;
        got_second_refclk = 0;
        refclk_time = $time;
    end
    pfdena_ipd_last_value = pfdena_ipd;
end

always @(negedge refclk)
begin
    refclk_last_value = refclk;
end

always @(negedge fbclk)
begin
    fbclk_last_value = fbclk;
end

always @(posedge refclk or posedge fbclk)
begin
    if (refclk == 1'b1 && refclk_last_value !== refclk && areset_ipd === 1'b0)
    begin
        n_val <= n_val_tmp;
        if (! got_first_refclk)
        begin
            got_first_refclk = 1;
        end else
        begin
            got_second_refclk = 1;
            refclk_period = $time - refclk_time;

            // check if incoming freq. will cause VCO range to be
            // exceeded
            if ( (vco_max != 0 && vco_min != 0) && (skip_vco == "off") && (pfdena_ipd === 1'b1) &&
                ((refclk_period/loop_xplier > vco_max) ||
                (refclk_period/loop_xplier < vco_min)) )
            begin
                if (pll_is_locked == 1'b1)
                begin
                    $display ("Warning : Input clock freq. is not within VCO range. PLL may lose lock");
                    $display ("Time: %0t  Instance: %m", $time);
                    if (inclk_out_of_range === 1'b1)
                    begin
                        // unlock
                        pll_is_locked = 0;
                        locked_tmp = 0;
                        if (l_pll_type == "fast")
                            locked_tmp = 1;
                        pll_about_to_lock = 0;
                        cycles_to_lock = 0;
                        $display ("Note : %s PLL lost lock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        first_schedule = 1;
                        schedule_offset = 1;
                        vco_period_was_phase_adjusted = 0;
                        phase_adjust_was_scheduled = 0;
                    end
                end
                else begin
                    if (no_warn == 0)
                    begin
                        $display ("Warning : Input clock freq. is not within VCO range. PLL may not lock");
                        $display ("Time: %0t  Instance: %m", $time);
                        no_warn = 1;
                    end
                end
                inclk_out_of_range = 1;
            end
            else begin
                inclk_out_of_range = 0;
            end

        end
        if (stop_vco == 1'b1)
        begin
            stop_vco = 0;
            schedule_vco = ~schedule_vco;
        end
        refclk_time = $time;
    end

    if (fbclk == 1'b1 && fbclk_last_value !== fbclk)
    begin
        m_val <= m_val_tmp;
        if (!got_first_fbclk)
        begin
            got_first_fbclk = 1;
            first_fbclk_time = $time;
        end
        else
            fbclk_period = $time - fbclk_time;

        // need refclk_period here, so initialized to proper value above
        if ( ( ($time - refclk_time > 1.5 * refclk_period) && pfdena_ipd === 1'b1 && pll_is_locked == 1'b1) || ( ($time - refclk_time > 5 * refclk_period) && pfdena_ipd === 1'b1) )
        begin
            stop_vco = 1;
            // reset
            got_first_refclk = 0;
            got_first_fbclk = 0;
            got_second_refclk = 0;
            if (pll_is_locked == 1'b1)
            begin
                pll_is_locked = 0;
                locked_tmp = 0;
                if (l_pll_type == "fast")
                    locked_tmp = 1;
                $display ("Note : %s PLL lost lock due to loss of input clock", family_name);
                $display ("Time: %0t  Instance: %m", $time);
            end
            pll_about_to_lock = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
            first_schedule = 1;
            vco_period_was_phase_adjusted = 0;
            phase_adjust_was_scheduled = 0;
        end
        fbclk_time = $time;
    end

    if (got_second_refclk && pfdena_ipd === 1'b1 && (!inclk_out_of_range))
    begin
        // now we know actual incoming period
//       if (abs(refclk_period - fbclk_period) > 2)
//       begin
//           new_m_times_vco_period = refclk_period;
//       end
//       else if (abs(fbclk_time - refclk_time) <= 2 || (refclk_period - abs(fbclk_time - refclk_time) <= 2))
        if (abs(fbclk_time - refclk_time) <= 5 || (got_first_fbclk && abs(refclk_period - abs(fbclk_time - refclk_time)) <= 5))
        begin
            // considered in phase
            if (cycles_to_lock == valid_lock_multiplier - 1)
                pll_about_to_lock <= 1;
            if (cycles_to_lock == valid_lock_multiplier)
            begin
                if (pll_is_locked === 1'b0)
                begin
                    $display (" Note : %s PLL locked to incoming clock", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
                end
                pll_is_locked = 1;
                locked_tmp = 1;
                if (l_pll_type == "fast")
                    locked_tmp = 0;
            end
            // increment lock counter only if the second part of the above
            // time check is NOT true
            if (!(abs(refclk_period - abs(fbclk_time - refclk_time)) <= 5))
            begin
                cycles_to_lock = cycles_to_lock + 1;
            end

            // adjust m_times_vco_period
            new_m_times_vco_period = refclk_period;

        end else
        begin
            // if locked, begin unlock
            if (pll_is_locked)
            begin
                cycles_to_unlock = cycles_to_unlock + 1;
                if (cycles_to_unlock == invalid_lock_multiplier)
                begin
                    pll_is_locked = 0;
                    locked_tmp = 0;
                    if (l_pll_type == "fast")
                        locked_tmp = 1;
                    pll_about_to_lock = 0;
                    cycles_to_lock = 0;
                    $display ("Note : %s PLL lost lock", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
                    first_schedule = 1;
                    schedule_offset = 1;
                    vco_period_was_phase_adjusted = 0;
                    phase_adjust_was_scheduled = 0;
                end
            end
            if (abs(refclk_period - fbclk_period) <= 2)
            begin
                // frequency is still good
                if ($time == fbclk_time && (!phase_adjust_was_scheduled))
                begin
                    if (abs(fbclk_time - refclk_time) > refclk_period/2)
                    begin
                        if (abs(fbclk_time - refclk_time) > 1.5 * refclk_period)
                        begin
                            // input clock may have stopped : do nothing
                        end
                        else begin
                        new_m_times_vco_period = m_times_vco_period + (refclk_period - abs(fbclk_time - refclk_time));
                        vco_period_was_phase_adjusted = 1;
                        end
                    end else
                    begin
                        new_m_times_vco_period = m_times_vco_period - abs(fbclk_time - refclk_time);
                        vco_period_was_phase_adjusted = 1;
                    end
                end
            end else
            begin
                new_m_times_vco_period = refclk_period;
                phase_adjust_was_scheduled = 0;
            end
        end
    end

    if (quiet_period_violation == 1'b1 || reconfig_err == 1'b1 || scanclr_violation == 1'b1 || scanclr_clk_violation == 1'b1)
    begin
        locked_tmp = 0;
        if (l_pll_type == "fast")
            locked_tmp = 1;
    end

    refclk_last_value = refclk;
    fbclk_last_value = fbclk;
end

    assign clk0_tmp = i_clk0_counter == "l0" ? l0_clk : i_clk0_counter == "l1" ? l1_clk : i_clk0_counter == "g0" ? g0_clk : i_clk0_counter == "g1" ? g1_clk : i_clk0_counter == "g2" ? g2_clk : i_clk0_counter == "g3" ? g3_clk : 1'b0;

    assign clk0 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? clk0_tmp : 1'bx;

    dffp ena0_reg ( .d(clkena0_ipd),
                            .clrn(1'b1),
                            .prn(1'b1),
                            .ena(1'b1),
                            .clk(!clk0_tmp),
                            .q(ena0));

    assign clk1_tmp = i_clk1_counter == "l0" ? l0_clk : i_clk1_counter == "l1" ? l1_clk : i_clk1_counter == "g0" ? g0_clk : i_clk1_counter == "g1" ? g1_clk : i_clk1_counter == "g2" ? g2_clk : i_clk1_counter == "g3" ? g3_clk : 1'b0;

    assign clk1 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? clk1_tmp : 1'bx;

    dffp ena1_reg ( .d(clkena1_ipd),
                            .clrn(1'b1),
                            .prn(1'b1),
                            .ena(1'b1),
                            .clk(!clk1_tmp),
                            .q(ena1));

    assign clk2_tmp = i_clk2_counter == "l0" ? l0_clk : i_clk2_counter == "l1" ? l1_clk : i_clk2_counter == "g0" ? g0_clk : i_clk2_counter == "g1" ? g1_clk : i_clk2_counter == "g2" ? g2_clk : i_clk2_counter == "g3" ? g3_clk : 1'b0;

    assign clk2 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? clk2_tmp : 1'bx;

    dffp ena2_reg ( .d(clkena2_ipd),
                            .clrn(1'b1),
                            .prn(1'b1),
                            .ena(1'b1),
                            .clk(!clk2_tmp),
                            .q(ena2));

    assign clk3_tmp = i_clk3_counter == "l0" ? l0_clk : i_clk3_counter == "l1" ? l1_clk : i_clk3_counter == "g0" ? g0_clk : i_clk3_counter == "g1" ? g1_clk : i_clk3_counter == "g2" ? g2_clk : i_clk3_counter == "g3" ? g3_clk : 1'b0;

    assign clk3 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? clk3_tmp : 1'bx;

    dffp ena3_reg ( .d(clkena3_ipd),
                            .clrn(1'b1),
                            .prn(1'b1),
                            .ena(1'b1),
                            .clk(!clk3_tmp),
                            .q(ena3));

    assign clk4_tmp = i_clk4_counter == "l0" ? l0_clk : i_clk4_counter == "l1" ? l1_clk : i_clk4_counter == "g0" ? g0_clk : i_clk4_counter == "g1" ? g1_clk : i_clk4_counter == "g2" ? g2_clk : i_clk4_counter == "g3" ? g3_clk : 1'b0;

    assign clk4 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? clk4_tmp : 1'bx;

    dffp ena4_reg ( .d(clkena4_ipd),
                            .clrn(1'b1),
                            .prn(1'b1),
                            .ena(1'b1),
                            .clk(!clk4_tmp),
                            .q(ena4));

    assign clk5_tmp = i_clk5_counter == "l0" ? l0_clk : i_clk5_counter == "l1" ? l1_clk : i_clk5_counter == "g0" ? g0_clk : i_clk5_counter == "g1" ? g1_clk : i_clk5_counter == "g2" ? g2_clk : i_clk5_counter == "g3" ? g3_clk : 1'b0;

    assign clk5 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? clk5_tmp : 1'bx;

    dffp ena5_reg ( .d(clkena5_ipd),
                            .clrn(1'b1),
                            .prn(1'b1),
                            .ena(1'b1),
                            .clk(!clk5_tmp),
                            .q(ena5));

    assign extclk0_tmp = i_extclk0_counter == "e0" ? e0_clk : i_extclk0_counter == "e1" ? e1_clk : i_extclk0_counter == "e2" ? e2_clk : i_extclk0_counter == "e3" ? e3_clk : i_extclk0_counter == "g0" ? g0_clk : 1'b0;

    assign extclk0 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? extclk0_tmp : 1'bx;

    dffp extena0_reg  ( .d(extclkena0_ipd),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(!extclk0_tmp),
                                .q(extena0));

    assign extclk1_tmp = i_extclk1_counter == "e0" ? e0_clk : i_extclk1_counter == "e1" ? e1_clk : i_extclk1_counter == "e2" ? e2_clk : i_extclk1_counter == "e3" ? e3_clk : i_extclk1_counter == "g0" ? g0_clk : 1'b0;

    assign extclk1 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? extclk1_tmp : 1'bx;

    dffp extena1_reg  ( .d(extclkena1_ipd),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(!extclk1_tmp),
                                .q(extena1));

    assign extclk2_tmp = i_extclk2_counter == "e0" ? e0_clk : i_extclk2_counter == "e1" ? e1_clk : i_extclk2_counter == "e2" ? e2_clk : i_extclk2_counter == "e3" ? e3_clk : i_extclk2_counter == "g0" ? g0_clk : 1'b0;

    assign extclk2 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? extclk2_tmp : 1'bx;

    dffp extena2_reg  ( .d(extclkena2_ipd),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(!extclk2_tmp),
                                .q(extena2));

    assign extclk3_tmp = i_extclk3_counter == "e0" ? e0_clk : i_extclk3_counter == "e1" ? e1_clk : i_extclk3_counter == "e2" ? e2_clk : i_extclk3_counter == "e3" ? e3_clk : i_extclk3_counter == "g0" ? g0_clk : 1'b0;

    assign extclk3 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || (pll_about_to_lock == 1'b1 && !quiet_period_violation && !reconfig_err && !scanclr_violation && !scanclr_clk_violation) ? extclk3_tmp : 1'bx;

    dffp extena3_reg  ( .d(extclkena3_ipd),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .ena(1'b1),
                                .clk(!extclk3_tmp),
                                .q(extena3));

    assign enable_0 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || pll_about_to_lock == 1'b1 ? enable0_tmp : 1'bx;
    assign enable_1 = (areset_ipd === 1'b1 || ena_ipd === 1'b0) || pll_about_to_lock == 1'b1 ? enable1_tmp : 1'bx;

    // ACCELERATE OUTPUTS
    and (clk[0], ena0, clk0);
    and (clk[1], ena1, clk1);
    and (clk[2], ena2, clk2);
    and (clk[3], ena3, clk3);
    and (clk[4], ena4, clk4);
    and (clk[5], ena5, clk5);

    and (extclk[0], extena0, extclk0);
    and (extclk[1], extena1, extclk1);
    and (extclk[2], extena2, extclk2);
    and (extclk[3], extena3, extclk3);

    and (enable0, 1'b1, enable_0);
    and (enable1, 1'b1, enable_1);

    and (scandataout, 1'b1, scandataout_tmp);

endmodule // MF_stratix_pll

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : arm_m_cntr
//
// Description : Simulation model for the M counter. This is the
//               loop feedback counter for the StratixII PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module arm_m_cntr   ( clk,
                            reset,
                            cout,
                            initial_value,
                            modulus,
                            time_delay);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] initial_value;
    input [31:0] modulus;
    input [31:0] time_delay;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
            cout_tmp <= tmp_cout;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'b1 && first_rising_edge)
                begin
                    first_rising_edge = 0;
                    tmp_cout = clk;
                    cout_tmp <= #(time_delay) tmp_cout;
                end
                else if (first_rising_edge == 0)
                begin
                    if (count < modulus)
                        count = count + 1;
                    else
                    begin
                        count = 1;
                        tmp_cout = ~tmp_cout;
                        cout_tmp <= #(time_delay) tmp_cout;
                    end
                end
            end
        end
        clk_last_value = clk;

    end

    and (cout, cout_tmp, 1'b1);

endmodule // arm_m_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : arm_n_cntr
//
// Description : Simulation model for the N counter. This is the
//               input clock divide counter for the StratixII PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module arm_n_cntr   ( clk,
                            reset,
                            cout,
                            modulus);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] modulus;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg clk_last_valid_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'bx)
                begin
                    $display("Warning : Invalid transition to 'X' detected on StratixII PLL input clk. This edge will be ignored.");
                    $display("Time: %0t  Instance: %m", $time);
                end
                else if (clk === 1'b1 && first_rising_edge)
                begin
                    first_rising_edge = 0;
                    tmp_cout = clk;
                end
                else if ((first_rising_edge == 0) && (clk_last_valid_value !== clk))
                begin
                    if (count < modulus)
                        count = count + 1;
                    else
                    begin
                        count = 1;
                        tmp_cout = ~tmp_cout;
                    end
                end
            end
        end
        clk_last_value = clk;
        if (clk !== 1'bx)
            clk_last_valid_value = clk;

    end

    assign cout = tmp_cout;

endmodule // arm_n_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : arm_scale_cntr
//
// Description : Simulation model for the output scale-down counters.
//               This is a common model for the C0, C1, C2, C3, C4 and
//               C5 output counters of the StratixII PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module arm_scale_cntr   ( clk,
                                reset,
                                cout,
                                high,
                                low,
                                initial_value,
                                mode,
                                ph_tap);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] high;
    input [31:0] low;
    input [31:0] initial_value;
    input [8*6:1] mode;
    input [31:0] ph_tap;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg init;
    integer count;
    integer output_shift_count;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 0;
        tmp_cout = 0;
        output_shift_count = 1;
    end

    always @(clk or reset)
    begin
        if (init !== 1'b1)
        begin
            clk_last_value = 0;
            init = 1'b1;
        end
        if (reset)
        begin
            count = 1;
            output_shift_count = 1;
            tmp_cout = 0;
            first_rising_edge = 0;
        end
        else if (clk_last_value !== clk)
        begin
            if (mode == "   off")
                tmp_cout = 0;
            else if (mode == "bypass")
            begin
                tmp_cout = clk;
                first_rising_edge = 1;
            end
            else if (first_rising_edge == 0)
            begin
                if (clk == 1)
                begin
                    if (output_shift_count == initial_value)
                    begin
                        tmp_cout = clk;
                        first_rising_edge = 1;
                    end
                    else
                        output_shift_count = output_shift_count + 1;
                end
            end
            else if (output_shift_count < initial_value)
            begin
                if (clk == 1)
                    output_shift_count = output_shift_count + 1;
            end
            else
            begin
                count = count + 1;
                if (mode == "  even" && (count == (high*2) + 1))
                    tmp_cout = 0;
                else if (mode == "   odd" && (count == (high*2)))
                    tmp_cout = 0;
                else if (count == (high + low)*2 + 1)
                begin
                    tmp_cout = 1;
                    count = 1;        // reset count
                end
            end
        end
        clk_last_value = clk;
        cout_tmp <= tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // arm_scale_cntr


//////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_stratixii_pll
//
// Description : Behavioral model for StratixII pll.
// 
// Limitations : Does not support Spread Spectrum and Bandwidth.
//
// Outputs     : Up to 6 output clocks, each defined by its own set of
//               parameters. Locked output (active high) indicates when the
//               PLL locks. clkbad, clkloss and activeclock are used for
//               clock switchover to indicate which input clock has gone
//               bad, when the clock switchover initiates and which input
//               clock is being used as the reference, respectively.
//               scandataout is the data output of the serial scan chain.
//
//////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps
`define STXII_PLL_WORD_LENGTH 18

module MF_stratixii_pll (inclk,
                    fbin,
                    ena,
                    clkswitch,
                    areset,
                    pfdena,
                    scanclk,
                    scanread,
                    scanwrite,
                    scandata,
                    testin,
                    clk,
                    clkbad,
                    activeclock,
                    locked,
                    clkloss,
                    scandataout,
                    scandone,
                    enable0,
                    enable1,
                    testupout,
                    testdownout,
                    sclkout
                    );

    parameter operation_mode                       = "normal";
    parameter pll_type                             = "auto";
    parameter compensate_clock                     = "clk0";
    parameter feedback_source                      = "clk0";
    parameter qualify_conf_done                    = "off";

    parameter test_input_comp_delay_chain_bits     = 0;
    parameter test_feedback_comp_delay_chain_bits  = 0;

    parameter inclk0_input_frequency               = 10000;
    parameter inclk1_input_frequency               = 10000;

    parameter gate_lock_signal                     = "no";
    parameter gate_lock_counter                    = 1;
    parameter self_reset_on_gated_loss_lock        = "off";
    parameter valid_lock_multiplier                = 1;
    parameter invalid_lock_multiplier              = 5;

    parameter switch_over_type                     = "auto";
    parameter switch_over_on_lossclk               = "off";
    parameter switch_over_on_gated_lock            = "off";
    parameter switch_over_counter                  = 1;
    parameter enable_switch_over_counter           = "on";

    parameter bandwidth                            = 0;
    parameter bandwidth_type                       = "auto";
    parameter spread_frequency                     = 0;
    parameter common_rx_tx                         = "off";
    parameter use_dc_coupling                      = "false";

    parameter clk0_output_frequency                = 0;
    parameter clk0_multiply_by                     = 1;
    parameter clk0_divide_by                       = 1;
    parameter clk0_phase_shift                     = "0";
    parameter clk0_duty_cycle                      = 50;

    parameter clk1_output_frequency                = 0;
    parameter clk1_multiply_by                     = 1;
    parameter clk1_divide_by                       = 1;
    parameter clk1_phase_shift                     = "0";
    parameter clk1_duty_cycle                      = 50;

    parameter clk2_output_frequency                = 0;
    parameter clk2_multiply_by                     = 1;
    parameter clk2_divide_by                       = 1;
    parameter clk2_phase_shift                     = "0";
    parameter clk2_duty_cycle                      = 50;

    parameter clk3_output_frequency                = 0;
    parameter clk3_multiply_by                     = 1;
    parameter clk3_divide_by                       = 1;
    parameter clk3_phase_shift                     = "0";
    parameter clk3_duty_cycle                      = 50;

    parameter clk4_output_frequency                = 0;
    parameter clk4_multiply_by                     = 1;
    parameter clk4_divide_by                       = 1;
    parameter clk4_phase_shift                     = "0";
    parameter clk4_duty_cycle                      = 50;

    parameter clk5_output_frequency                = 0;
    parameter clk5_multiply_by                     = 1;
    parameter clk5_divide_by                       = 1;
    parameter clk5_phase_shift                     = "0";
    parameter clk5_duty_cycle                      = 50;

    parameter pfd_min                              = 0;
    parameter pfd_max                              = 0;
    parameter vco_min                              = 0;
    parameter vco_max                              = 0;
    parameter vco_center                           = 0;

    // ADVANCED USE PARAMETERS
    parameter m_initial = 1;
    parameter m = 0;
    parameter n = 1;
    parameter m2 = 1;
    parameter n2 = 1;
    parameter ss = 0;

    parameter c0_high = 1;
    parameter c0_low = 1;
    parameter c0_initial = 1;
    parameter c0_mode = "bypass";
    parameter c0_ph = 0;

    parameter c1_high = 1;
    parameter c1_low = 1;
    parameter c1_initial = 1;
    parameter c1_mode = "bypass";
    parameter c1_ph = 0;

    parameter c2_high = 1;
    parameter c2_low = 1;
    parameter c2_initial = 1;
    parameter c2_mode = "bypass";
    parameter c2_ph = 0;

    parameter c3_high = 1;
    parameter c3_low = 1;
    parameter c3_initial = 1;
    parameter c3_mode = "bypass";
    parameter c3_ph = 0;

    parameter c4_high = 1;
    parameter c4_low = 1;
    parameter c4_initial = 1;
    parameter c4_mode = "bypass";
    parameter c4_ph = 0;

    parameter c5_high = 1;
    parameter c5_low = 1;
    parameter c5_initial = 1;
    parameter c5_mode = "bypass";
    parameter c5_ph = 0;

    parameter m_ph = 0;

    parameter clk0_counter = "c0";
    parameter clk1_counter = "c1";
    parameter clk2_counter = "c2";
    parameter clk3_counter = "c3";
    parameter clk4_counter = "c4";
    parameter clk5_counter = "c5";

    parameter c1_use_casc_in = "off";
    parameter c2_use_casc_in = "off";
    parameter c3_use_casc_in = "off";
    parameter c4_use_casc_in = "off";
    parameter c5_use_casc_in = "off";

    parameter m_test_source = 5;
    parameter c0_test_source = 5;
    parameter c1_test_source = 5;
    parameter c2_test_source = 5;
    parameter c3_test_source = 5;
    parameter c4_test_source = 5;
    parameter c5_test_source = 5;

    // LVDS mode parameters
    parameter enable0_counter = "c0";
    parameter enable1_counter = "c1";
    parameter sclkout0_phase_shift = "0";
    parameter sclkout1_phase_shift = "0";

    parameter vco_multiply_by = 0;
    parameter vco_divide_by = 0;
    parameter vco_post_scale = 1;

    parameter charge_pump_current = 52;
    parameter loop_filter_r = "1.0";
    parameter loop_filter_c = 16;

    parameter pll_compensation_delay = 0;
    parameter simulation_type = "functional";

// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter down_spread                          = "0.0";

    parameter sim_gate_lock_device_behavior        = "off";

    parameter clk0_phase_shift_num = 0;
    parameter clk1_phase_shift_num = 0;
    parameter clk2_phase_shift_num = 0;
    parameter family_name = "StratixII";

    parameter clk0_use_even_counter_mode = "off";
    parameter clk1_use_even_counter_mode = "off";
    parameter clk2_use_even_counter_mode = "off";
    parameter clk3_use_even_counter_mode = "off";
    parameter clk4_use_even_counter_mode = "off";
    parameter clk5_use_even_counter_mode = "off";

    parameter clk0_use_even_counter_value = "off";
    parameter clk1_use_even_counter_value = "off";
    parameter clk2_use_even_counter_value = "off";
    parameter clk3_use_even_counter_value = "off";
    parameter clk4_use_even_counter_value = "off";
    parameter clk5_use_even_counter_value = "off";

// SIMULATION_ONLY_PARAMETERS_END

    parameter scan_chain_mif_file = "";

    // INPUT PORTS
    input [1:0] inclk;
    input fbin;
    input ena;
    input clkswitch;
    input areset;
    input pfdena;
    input scanclk;
    input scanread;
    input scanwrite;
    input scandata;
    input [3:0] testin;

    // OUTPUT PORTS
    output [5:0] clk;
    output [1:0] clkbad;
    output activeclock;
    output locked;
    output clkloss;
    output scandataout;
    output scandone;
    // lvds specific output ports
    output enable0;
    output enable1;
    output [1:0] sclkout;
    // test ports
    output testupout;
    output testdownout;

    // BUFFER INPUTS
    wire inclk0_ipd;
    wire inclk1_ipd;
    wire ena_ipd;
    wire fbin_ipd;
    wire clkswitch_ipd;
    wire areset_ipd;
    wire pfdena_ipd;
    wire scanclk_ipd;
    wire scanread_ipd;
    wire scanwrite_ipd;
    wire scandata_ipd;
    buf (inclk0_ipd, inclk[0]);
    buf (inclk1_ipd, inclk[1]);
    buf (ena_ipd, ena);
    buf (fbin_ipd, fbin);
    buf (clkswitch_ipd, clkswitch);
    buf (areset_ipd, areset);
    buf (pfdena_ipd, pfdena);
    buf (scanclk_ipd, scanclk);
    buf (scanread_ipd, scanread);
    buf (scanwrite_ipd, scanwrite);
    buf (scandata_ipd, scandata);


    // INTERNAL VARIABLES AND NETS
    integer scan_chain_length;
    integer i;
    integer j;
    integer k;
    integer x;
    integer y;
    integer l_index;
    integer gate_count;
    integer egpp_offset;
    integer sched_time;
    integer delay_chain;
    integer low;
    integer high;
    integer initial_delay;
    integer fbk_phase;
    integer fbk_delay;
    integer phase_shift[0:7];
    integer last_phase_shift[0:7];

    integer m_times_vco_period;
    integer new_m_times_vco_period;
    integer refclk_period;
    integer fbclk_period;
    integer high_time;
    integer low_time;
    integer my_rem;
    integer tmp_rem;
    integer rem;
    integer tmp_vco_per;
    integer vco_per;
    integer offset;
    integer temp_offset;
    integer cycles_to_lock;
    integer cycles_to_unlock;
    integer c0_count;
    integer c0_initial_count;
    integer c1_count;
    integer c1_initial_count;
    integer loop_xplier;
    integer loop_initial;
    integer loop_ph;
    integer cycle_to_adjust;
    integer total_pull_back;
    integer pull_back_M;

    time    fbclk_time;
    time    first_fbclk_time;
    time    refclk_time;
    time    next_vco_sched_time;

    reg got_first_refclk;
    reg got_second_refclk;
    reg got_first_fbclk;
    reg refclk_last_value;
    reg fbclk_last_value;
    reg inclk_last_value;
    reg pll_is_locked;
    reg pll_about_to_lock;
    reg locked_tmp;
    reg c0_got_first_rising_edge;
    reg c1_got_first_rising_edge;
    reg vco_c0_last_value;
    reg vco_c1_last_value;
    reg areset_ipd_last_value;
    reg ena_ipd_last_value;
    reg pfdena_ipd_last_value;
    reg inclk_out_of_range;
    reg schedule_vco_last_value;

    reg gate_out;
    reg vco_val;

    reg [31:0] m_initial_val;
    reg [31:0] m_val[0:1];
    reg [31:0] n_val[0:1];
    reg [31:0] m_delay;
    reg [8*6:1] m_mode_val[0:1];
    reg [8*6:1] n_mode_val[0:1];

    reg [31:0] c_high_val[0:5];
    reg [31:0] c_low_val[0:5];
    reg [8*6:1] c_mode_val[0:5];
    reg [31:0] c_initial_val[0:5];
    integer c_ph_val[0:5];

    // temporary registers for reprogramming
    integer c_ph_val_tmp[0:5];
    reg [31:0] c_high_val_tmp[0:5];
    reg [31:0] c_low_val_tmp[0:5];
    reg [8*6:1] c_mode_val_tmp[0:5];

    // hold registers for reprogramming
    integer c_ph_val_hold[0:5];
    reg [31:0] c_high_val_hold[0:5];
    reg [31:0] c_low_val_hold[0:5];
    reg [8*6:1] c_mode_val_hold[0:5];

    // old values
    reg [31:0] m_val_old[0:1];
    reg [31:0] m_val_tmp[0:1];
    reg [31:0] n_val_old[0:1];
    reg [8*6:1] m_mode_val_old[0:1];
    reg [8*6:1] n_mode_val_old[0:1];
    reg [31:0] c_high_val_old[0:5];
    reg [31:0] c_low_val_old[0:5];
    reg [8*6:1] c_mode_val_old[0:5];
    integer c_ph_val_old[0:5];
    integer   m_ph_val_old;
    integer   m_ph_val_tmp;

    integer cp_curr_old;
    integer cp_curr_val;
    integer lfc_old;
    integer lfc_val;
    reg [9*8:1] lfr_val;
    reg [9*8:1] lfr_old;

    reg [31:0] m_hi;
    reg [31:0] m_lo;

    // ph tap orig values (POF)
    integer c_ph_val_orig[0:5];
    integer m_ph_val_orig;

    reg schedule_vco;
    reg stop_vco;
    reg inclk_n;

    reg [7:0] vco_out;
    reg [7:0] vco_tap;
    reg [7:0] vco_out_last_value;
    reg [7:0] vco_tap_last_value;
    wire inclk_c0;
    wire inclk_c1;
    wire inclk_c2;
    wire inclk_c3;
    wire inclk_c4;
    wire inclk_c5;
    reg  inclk_c0_from_vco;
    reg  inclk_c1_from_vco;
    reg  inclk_c2_from_vco;
    reg  inclk_c3_from_vco;
    reg  inclk_c4_from_vco;
    reg  inclk_c5_from_vco;
    reg  inclk_m_from_vco;
    reg inclk_sclkout0_from_vco;
    reg inclk_sclkout1_from_vco;

    wire inclk_m;
    wire [5:0] clk_tmp;

    wire ena_pll;
    wire n_cntr_inclk;
    reg sclkout0_tmp;
    reg sclkout1_tmp;

    reg vco_c0;
    reg vco_c1;

    wire [5:0] clk_out;
    wire sclkout0;
    wire sclkout1;

    wire c0_clk;
    wire c1_clk;
    wire c2_clk;
    wire c3_clk;
    wire c4_clk;
    wire c5_clk;

    reg first_schedule;

    wire enable0_tmp;
    wire enable1_tmp;
    wire enable_0;
    wire enable_1;
    reg c0_tmp;
    reg c1_tmp;

    reg vco_period_was_phase_adjusted;
    reg phase_adjust_was_scheduled;

    wire refclk;
    wire fbclk;
    
    wire pllena_reg;
    wire test_mode_inclk;

    // for external feedback mode

    reg [31:0] ext_fbk_cntr_high;
    reg [31:0] ext_fbk_cntr_low;
    reg [31:0] ext_fbk_cntr_modulus;
    reg [8*2:1] ext_fbk_cntr;
    reg [8*6:1] ext_fbk_cntr_mode;
    integer ext_fbk_cntr_ph;
    integer ext_fbk_cntr_initial;
    integer ext_fbk_cntr_index;

    // variables for clk_switch
    reg clk0_is_bad;
    reg clk1_is_bad;
    reg inclk0_last_value;
    reg inclk1_last_value;
    reg other_clock_value;
    reg other_clock_last_value;
    reg primary_clk_is_bad;
    reg current_clk_is_bad;
    reg external_switch;
    reg active_clock;
    reg clkloss_tmp;
    reg got_curr_clk_falling_edge_after_clkswitch;

    integer clk0_count;
    integer clk1_count;
    integer switch_over_count;

    wire scandataout_tmp;
    reg scandone_tmp;
    reg scandone_tmp_last_value;
    integer quiet_time;
    integer slowest_clk_old;
    integer slowest_clk_new;

    reg reconfig_err;
    reg error;
    time    scanclk_last_rising_edge;
    time    scanread_active_edge;
    reg got_first_scanclk;
    reg got_first_gated_scanclk;
    reg gated_scanclk;
    integer scanclk_period;
    reg scanclk_last_value;
    reg scanread_reg;
    reg scanwrite_reg;
    reg scanwrite_enabled;
    reg scanwrite_last_value;
    reg [173:0] scan_data;
    reg [173:0] tmp_scan_data;
    reg c0_rising_edge_transfer_done;
    reg c1_rising_edge_transfer_done;
    reg c2_rising_edge_transfer_done;
    reg c3_rising_edge_transfer_done;
    reg c4_rising_edge_transfer_done;
    reg c5_rising_edge_transfer_done;
    reg scanread_setup_violation;
    integer index;
    integer scanclk_cycles;
    reg d_msg;

    integer num_output_cntrs;
    reg no_warn;

// LOCAL_PARAMETERS_BEGIN

    parameter GPP_SCAN_CHAIN = 174;
    parameter FAST_SCAN_CHAIN = 75;
    // primary clk is always inclk0
    parameter prim_clk = "inclk0";
    parameter GATE_LOCK_CYCLES = 7;

// LOCAL_PARAMETERS_END

    // internal variables for scaling of multiply_by and divide_by values
    integer i_clk0_mult_by;
    integer i_clk0_div_by;
    integer i_clk1_mult_by;
    integer i_clk1_div_by;
    integer i_clk2_mult_by;
    integer i_clk2_div_by;
    integer i_clk3_mult_by;
    integer i_clk3_div_by;
    integer i_clk4_mult_by;
    integer i_clk4_div_by;
    integer i_clk5_mult_by;
    integer i_clk5_div_by;
    integer max_d_value;
    integer new_multiplier;

    // internal variables for storing the phase shift number.(used in lvds mode only)
    integer i_clk0_phase_shift;
    integer i_clk1_phase_shift;
    integer i_clk2_phase_shift;

    // user to advanced internal signals

    integer   i_m_initial;
    integer   i_m;
    integer   i_n;
    integer   i_m2;
    integer   i_n2;
    integer   i_ss;
    integer   i_c_high[0:5];
    integer   i_c_low[0:5];
    integer   i_c_initial[0:5];
    integer   i_c_ph[0:5];
    reg       [8*6:1] i_c_mode[0:5];

    integer   i_vco_min;
    integer   i_vco_max;
    integer   i_vco_center;
    integer   i_pfd_min;
    integer   i_pfd_max;
    integer   i_m_ph;
    integer   m_ph_val;
    reg [8*2:1] i_clk5_counter;
    reg [8*2:1] i_clk4_counter;
    reg [8*2:1] i_clk3_counter;
    reg [8*2:1] i_clk2_counter;
    reg [8*2:1] i_clk1_counter;
    reg [8*2:1] i_clk0_counter;
    integer   i_charge_pump_current;
    integer   i_loop_filter_r;
    integer   max_neg_abs;
    integer   output_count;
    integer   new_divisor;

    integer loop_filter_c_arr[0:3];
    integer fpll_loop_filter_c_arr[0:3];
    integer charge_pump_curr_arr[0:15];
    reg [9*8:1] loop_filter_r_arr[0:39];

    reg pll_in_test_mode;
    reg pll_is_in_reset;
    reg pll_is_disabled;

    // uppercase to lowercase parameter values
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_operation_mode;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_pll_type;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_qualify_conf_done;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_compensate_clock;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_scan_chain;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_primary_clock;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_gate_lock_signal;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_switch_over_on_lossclk;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_switch_over_type;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_switch_over_on_gated_lock;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_enable_switch_over_counter;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_feedback_source;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_bandwidth_type;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_simulation_type;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_sim_gate_lock_device_behavior;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_enable0_counter;
    reg [8*`STXII_PLL_WORD_LENGTH:1] l_enable1_counter;

    integer current_clock;
    integer ena0_cntr;
    integer ena1_cntr;
    reg is_fast_pll;
    reg ic1_use_casc_in;
    reg ic2_use_casc_in;
    reg ic3_use_casc_in;
    reg ic4_use_casc_in;
    reg ic5_use_casc_in;
    reg op_mode;

    reg init;
    reg tap0_is_active;

    ALTERA_DEVICE_FAMILIES dev ();


    // finds the closest integer fraction of a given pair of numerator and denominator. 
    task find_simple_integer_fraction;
        input numerator;
        input denominator;
        input max_denom;
        output fraction_num; 
        output fraction_div; 
        parameter max_iter = 20;
        
        integer numerator;
        integer denominator;
        integer max_denom;
        integer fraction_num; 
        integer fraction_div; 
        
        integer quotient_array[max_iter-1:0];
        integer int_loop_iter;
        integer int_quot;
        integer m_value;
        integer d_value;
        integer old_m_value;
        integer swap;

        integer loop_iter;
        integer num;
        integer den;
        integer i_max_iter;

    begin      
        loop_iter = 0;
        num = numerator;
        den = denominator;
        i_max_iter = max_iter;
       
        while (loop_iter < i_max_iter)
        begin
            int_quot = num / den;
            quotient_array[loop_iter] = int_quot;
            num = num - (den*int_quot);
            loop_iter=loop_iter+1;
            
            if ((num == 0) || (max_denom != -1) || (loop_iter == i_max_iter)) 
            begin
                // calculate the numerator and denominator if there is a restriction on the
                // max denom value or if the loop is ending
                m_value = 0;
                d_value = 1;
                // get the rounded value at this stage for the remaining fraction
                if (den != 0)
                begin
                    m_value = (2*num/den);
                end
                // calculate the fraction numerator and denominator at this stage
                for (int_loop_iter = loop_iter-1; int_loop_iter >= 0; int_loop_iter=int_loop_iter-1)
                begin
                    if (m_value == 0)
                    begin
                        m_value = quotient_array[int_loop_iter];
                        d_value = 1;
                    end
                    else
                    begin
                        old_m_value = m_value;
                        m_value = quotient_array[int_loop_iter]*m_value + d_value;
                        d_value = old_m_value;
                    end
                end
                // if the denominator is less than the maximum denom_value or if there is no restriction save it
                if ((d_value <= max_denom) || (max_denom == -1))
                begin
                    if ((m_value == 0) || (d_value == 0))
                    begin
                        fraction_num = numerator;
                        fraction_div = denominator;
                    end
                    else
                    begin
                        fraction_num = m_value;
                        fraction_div = d_value;
                    end
                end
                // end the loop if the denomitor has overflown or the numerator is zero (no remainder during this round)
                if (((d_value > max_denom) && (max_denom != -1)) || (num == 0))
                begin
                    i_max_iter = loop_iter;
                end
            end
            // swap the numerator and denominator for the next round
            swap = den;
            den = num;
            num = swap;
        end
    end
    endtask // find_simple_integer_fraction

    // get the absolute value
    function integer abs;
    input value;
    integer value;
    begin
        if (value < 0)
            abs = value * -1;
        else abs = value;
    end
    endfunction

    // find twice the period of the slowest clock
    function integer slowest_clk;
    input C0, C0_mode, C1, C1_mode, C2, C2_mode, C3, C3_mode, C4, C4_mode, C5, C5_mode, refclk, m_mod;
    integer C0, C1, C2, C3, C4, C5;
    reg [8*6:1] C0_mode, C1_mode, C2_mode, C3_mode, C4_mode, C5_mode;
    integer refclk;
    reg [31:0] m_mod;
    integer max_modulus;
    begin
        max_modulus = 1;
        if (C0_mode != "bypass" && C0_mode != "   off")
            max_modulus = C0;
        if (C1 > max_modulus && C1_mode != "bypass" && C1_mode != "   off")
            max_modulus = C1;
        if (C2 > max_modulus && C2_mode != "bypass" && C2_mode != "   off")
            max_modulus = C2;
        if (C3 > max_modulus && C3_mode != "bypass" && C3_mode != "   off")
            max_modulus = C3;
        if (C4 > max_modulus && C4_mode != "bypass" && C4_mode != "   off")
            max_modulus = C4;
        if (C5 > max_modulus && C5_mode != "bypass" && C5_mode != "   off")
            max_modulus = C5;

        if ((2 * refclk) > (refclk * max_modulus *2 / m_mod))
            slowest_clk = 2 * refclk;
        else
            slowest_clk = (refclk * max_modulus *2 / m_mod);
    end
    endfunction

    // count the number of digits in the given integer
    function integer count_digit;
    input X;
    integer X;
    integer count, result;
    begin
        count = 0;
        result = X;
        while (result != 0)
        begin
            result = (result / 10);
            count = count + 1;
        end
        
        count_digit = count;
    end
    endfunction

    // reduce the given huge number(X) to Y significant digits
    function integer scale_num;
    input X, Y;
    integer X, Y;
    integer count;
    integer fac_ten, lc;
    begin
        fac_ten = 1;
        count = count_digit(X);
        
        for (lc = 0; lc < (count-Y); lc = lc + 1)
            fac_ten = fac_ten * 10;

        scale_num = (X / fac_ten);
    end
    endfunction

    // find the greatest common denominator of X and Y
    function integer gcd;
    input X,Y;
    integer X,Y;
    integer L, S, R, G;
    begin
        if (X < Y) // find which is smaller.
        begin
            S = X;
            L = Y;
        end
        else
        begin
            S = Y;
            L = X;
        end

        R = S;
        while ( R > 1)
        begin
            S = L;
            L = R;
            R = S % L;  // divide bigger number by smaller.
                        // remainder becomes smaller number.
        end
        if (R == 0)     // if evenly divisible then L is gcd else it is 1.
            G = L;
        else
            G = R;
        gcd = G;
    end
    endfunction

    // find the least common multiple of A1 to A10
    function integer lcm;
    input A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer M1, M2, M3, M4, M5 , M6, M7, M8, M9, R;
    begin
        M1 = (A1 * A2)/gcd(A1, A2);
        M2 = (M1 * A3)/gcd(M1, A3);
        M3 = (M2 * A4)/gcd(M2, A4);
        M4 = (M3 * A5)/gcd(M3, A5);
        M5 = (M4 * A6)/gcd(M4, A6);
        M6 = (M5 * A7)/gcd(M5, A7);
        M7 = (M6 * A8)/gcd(M6, A8);
        M8 = (M7 * A9)/gcd(M7, A9);
        M9 = (M8 * A10)/gcd(M8, A10);
        if (M9 < 3)
            R = 10;
        else if ((M9 <= 10) && (M9 >= 3))
            R = 4 * M9;
        else if (M9 > 1000)
            R = scale_num(M9, 3);
        else
            R = M9;
        lcm = R; 
    end
    endfunction

    // find the factor of division of the output clock frequency
    // compared to the VCO
    function integer output_counter_value;
    input clk_divide, clk_mult, M, N;
    integer clk_divide, clk_mult, M, N;
    integer R;
    begin
        R = (clk_divide * M)/(clk_mult * N);
        output_counter_value = R;
    end
    endfunction

    // find the mode of each of the PLL counters - bypass, even or odd
    function [8*6:1] counter_mode;
    input duty_cycle;
    input output_counter_value;
    integer duty_cycle;
    integer output_counter_value;
    integer half_cycle_high;
    reg [8*6:1] R;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100;
        if (output_counter_value == 1)
            R = "bypass";
        else if ((half_cycle_high % 2) == 0)
            R = "  even";
        else
            R = "   odd";
        counter_mode = R;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock high
    function integer counter_high;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle;
    integer half_cycle_high;
    integer tmp_counter_high;
    integer mode;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_high = tmp_counter_high + !mode;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock low
    function integer counter_low;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle, counter_h;
    integer half_cycle_high;
    integer mode;
    integer tmp_counter_high;
    integer counter_l, tmp_counter_low;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_h = tmp_counter_high + !mode;
        tmp_counter_low =  output_counter_value - counter_h;
        if (tmp_counter_low == 0)
            counter_l = 1;
        else counter_l = tmp_counter_low;

        counter_low = counter_l;    
    end
    endfunction

    // find the smallest time delay amongst t1 to t10
    function integer mintimedelay;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2)
            m1 = t1;
        else
            m1 = t2;
        if (m1 < t3)
            m2 = m1;
        else
            m2 = t3;
        if (m2 < t4)
            m3 = m2;
        else
            m3 = t4;
        if (m3 < t5)
            m4 = m3;
        else
            m4 = t5;
        if (m4 < t6)
            m5 = m4;
        else
            m5 = t6;
        if (m5 < t7)
            m6 = m5;
        else
            m6 = t7;
        if (m6 < t8)
            m7 = m6;
        else
            m7 = t8;
        if (m7 < t9)
            m8 = m7;
        else
            m8 = t9;
        if (m8 < t10)
            m9 = m8;
        else
            m9 = t10;
        if (m9 > 0)
            mintimedelay = m9;
        else
            mintimedelay = 0;
    end
    endfunction

    // find the numerically largest negative number, and return its absolute value
    function integer maxnegabs;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2) m1 = t1; else m1 = t2;
        if (m1 < t3) m2 = m1; else m2 = t3;
        if (m2 < t4) m3 = m2; else m3 = t4;
        if (m3 < t5) m4 = m3; else m4 = t5;
        if (m4 < t6) m5 = m4; else m5 = t6;
        if (m5 < t7) m6 = m5; else m6 = t7;
        if (m6 < t8) m7 = m6; else m7 = t8;
        if (m7 < t9) m8 = m7; else m8 = t9;
        if (m8 < t10) m9 = m8; else m9 = t10;
        maxnegabs = (m9 < 0) ? 0 - m9 : 0;
    end
    endfunction

    // adjust the given tap_phase by adding the largest negative number (ph_base) 
    function integer ph_adjust;
    input tap_phase, ph_base;
    integer tap_phase, ph_base;
    begin
        ph_adjust = tap_phase + ph_base;
    end
    endfunction

    // find the number of VCO clock cycles to wait initially before the first 
    // rising edge of the output clock
    function integer counter_initial;
    input tap_phase, m, n;
    integer tap_phase, m, n, phase;
    begin
        if (tap_phase < 0) tap_phase = 0 - tap_phase;
        // adding 0.5 for rounding correction (required in order to round
        // to the nearest integer instead of truncating)
        phase = ((tap_phase * m) / (360 * n)) + 0.5;
        counter_initial = phase;
    end
    endfunction

    // find which VCO phase tap to align the rising edge of the output clock to
    function integer counter_ph;
    input tap_phase;
    input m,n;
    integer m,n, phase;
    integer tap_phase;
    begin
    // adding 0.5 for rounding correction
        phase = (tap_phase * m / n) + 0.5;
        counter_ph = (phase % 360) / 45;
    end
    endfunction

    // convert the given string to length 6 by padding with spaces
    function [8*6:1] translate_string;
    input [8*6:1] mode;
    reg [8*6:1] new_mode;
    begin
        if (mode == "bypass")
            new_mode = "bypass";
        else if (mode == "even")
            new_mode = "  even";
        else if (mode == "odd")
            new_mode = "   odd";

        translate_string = new_mode;
    end
    endfunction

    // convert string to integer with sign
    function integer str2int; 
    input [8*16:1] s;

    reg [8*16:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    integer m, magnitude;
    integer sign;

    begin
        sign = 1;
        magnitude = 0;
        reg_s = s;
        for (m=1; m<=16; m=m+1)
        begin
            tmp = reg_s[128:121];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            // Accumulate ascii digits 0-9 only.
            if ((tmp>=48) && (tmp<=57)) 
                magnitude = (magnitude * 10) + digit;
            if (tmp == 45)
                sign = -1;  // Found a '-' character, i.e. number is negative.
        end
        str2int = sign*magnitude;
    end
    endfunction

    // this is for stratixii lvds only
    // convert phase delay to integer
    function integer get_int_phase_shift; 
    input [8*16:1] s;
    input i_phase_shift;
    integer i_phase_shift;

    begin
        if (i_phase_shift != 0)
        begin                   
            get_int_phase_shift = i_phase_shift;
        end       
        else
        begin
            get_int_phase_shift = str2int(s);
        end        
    end
    endfunction

    // calculate the given phase shift (in ps) in terms of degrees
    function integer get_phase_degree; 
    input phase_shift;
    integer phase_shift, result;
    begin
        result = (phase_shift * 360) / inclk0_input_frequency;
        // this is to round up the calculation result
        if ( result > 0 )
            result = result + 1;
        else if ( result < 0 )
            result = result - 1;
        else
            result = 0;

        // assign the rounded up result
        get_phase_degree = result;
    end
    endfunction

    // convert uppercase parameter values to lowercase
    // assumes that the maximum character length of a parameter is 18
    function [8*`STXII_PLL_WORD_LENGTH:1] alpha_tolower;
    input [8*`STXII_PLL_WORD_LENGTH:1] given_string;

    reg [8*`STXII_PLL_WORD_LENGTH:1] return_string;
    reg [8*`STXII_PLL_WORD_LENGTH:1] reg_string;
    reg [8:1] tmp;
    reg [8:1] conv_char;
    integer byte_count;
    begin
        return_string = "                    "; // initialise strings to spaces
        conv_char = "        ";
        reg_string = given_string;
        for (byte_count = `STXII_PLL_WORD_LENGTH; byte_count >= 1; byte_count = byte_count - 1)
        begin
            tmp = reg_string[8*`STXII_PLL_WORD_LENGTH:(8*(`STXII_PLL_WORD_LENGTH-1)+1)];
            reg_string = reg_string << 8;
            if ((tmp >= 65) && (tmp <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
            begin
                conv_char = tmp + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
                return_string = {return_string, conv_char};
            end
            else
                return_string = {return_string, tmp};
        end
    
        alpha_tolower = return_string;
    end
    endfunction

    function integer display_msg;
    input [8*2:1] cntr_name;
    input msg_code;
    integer msg_code;
    begin
        if (msg_code == 1)
            $display ("Warning : %s counter switched from BYPASS mode to enabled. PLL may lose lock.", cntr_name);
        else if (msg_code == 2)
            $display ("Warning : Illegal 1 value for %s counter. Instead, the %s counter should be BYPASSED. Reconfiguration may not work.", cntr_name, cntr_name);
        else if (msg_code == 3)
            $display ("Warning : Illegal value for counter %s in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.", cntr_name);
        else if (msg_code == 4)
            $display ("Warning : %s counter switched from enabled to BYPASS mode. PLL may lose lock.", cntr_name);
        $display ("Time: %0t  Instance: %m", $time);
        display_msg = 1;
    end
    endfunction

    initial
    begin

        // convert string parameter values from uppercase to lowercase,
        // as expected in this model
        l_operation_mode             = alpha_tolower(operation_mode);
        l_pll_type                   = alpha_tolower(pll_type);
        l_qualify_conf_done          = alpha_tolower(qualify_conf_done);
        l_compensate_clock           = alpha_tolower(compensate_clock);
        l_primary_clock              = alpha_tolower(prim_clk);
        l_gate_lock_signal           = alpha_tolower(gate_lock_signal);
        l_switch_over_on_lossclk     = alpha_tolower(switch_over_on_lossclk);
        l_switch_over_on_gated_lock  = alpha_tolower(switch_over_on_gated_lock);
        l_enable_switch_over_counter = alpha_tolower(enable_switch_over_counter);
    if (dev.FEATURE_FAMILY_BASE_CYCLONEII(family_name) == 1)
        l_switch_over_type           = "manual";
    else
        l_switch_over_type           = alpha_tolower(switch_over_type);
        l_feedback_source            = alpha_tolower(feedback_source);
        l_bandwidth_type             = alpha_tolower(bandwidth_type);
        l_simulation_type            = alpha_tolower(simulation_type);
        l_sim_gate_lock_device_behavior     = alpha_tolower(sim_gate_lock_device_behavior);
        l_enable0_counter            = alpha_tolower(enable0_counter);
        l_enable1_counter            = alpha_tolower(enable1_counter);

        if (l_enable0_counter == "c0")
            ena0_cntr = 0;
        else
            ena0_cntr = 1;
        if (l_enable1_counter == "c0")
            ena1_cntr = 0;
        else
            ena1_cntr = 1;

        // initialize charge_pump_current, and loop_filter tables
        loop_filter_c_arr[0] = 57;
        loop_filter_c_arr[1] = 16;
        loop_filter_c_arr[2] = 36;
        loop_filter_c_arr[3] = 5;
        
        fpll_loop_filter_c_arr[0] = 18;
        fpll_loop_filter_c_arr[1] = 13;
        fpll_loop_filter_c_arr[2] = 8;
        fpll_loop_filter_c_arr[3] = 2;
        
        charge_pump_curr_arr[0] = 6;
        charge_pump_curr_arr[1] = 12;
        charge_pump_curr_arr[2] = 30;
        charge_pump_curr_arr[3] = 36;
        charge_pump_curr_arr[4] = 52;
        charge_pump_curr_arr[5] = 57;
        charge_pump_curr_arr[6] = 72;
        charge_pump_curr_arr[7] = 77;
        charge_pump_curr_arr[8] = 92;
        charge_pump_curr_arr[9] = 96;
        charge_pump_curr_arr[10] = 110;
        charge_pump_curr_arr[11] = 114;
        charge_pump_curr_arr[12] = 127;
        charge_pump_curr_arr[13] = 131;
        charge_pump_curr_arr[14] = 144;
        charge_pump_curr_arr[15] = 148;

        loop_filter_r_arr[0] = " 1.000000";
        loop_filter_r_arr[1] = " 1.500000";
        loop_filter_r_arr[2] = " 2.000000";
        loop_filter_r_arr[3] = " 2.500000";
        loop_filter_r_arr[4] = " 3.000000";
        loop_filter_r_arr[5] = " 3.500000";
        loop_filter_r_arr[6] = " 4.000000";
        loop_filter_r_arr[7] = " 4.500000";
        loop_filter_r_arr[8] = " 5.000000";
        loop_filter_r_arr[9] = " 5.500000";
        loop_filter_r_arr[10] = " 6.000000";
        loop_filter_r_arr[11] = " 6.500000";
        loop_filter_r_arr[12] = " 7.000000";
        loop_filter_r_arr[13] = " 7.500000";
        loop_filter_r_arr[14] = " 8.000000";
        loop_filter_r_arr[15] = " 8.500000";
        loop_filter_r_arr[16] = " 9.000000";
        loop_filter_r_arr[17] = " 9.500000";
        loop_filter_r_arr[18] = "10.000000";
        loop_filter_r_arr[19] = "10.500000";
        loop_filter_r_arr[20] = "11.000000";
        loop_filter_r_arr[21] = "11.500000";
        loop_filter_r_arr[22] = "12.000000";
        loop_filter_r_arr[23] = "12.500000";
        loop_filter_r_arr[24] = "13.000000";
        loop_filter_r_arr[25] = "13.500000";
        loop_filter_r_arr[26] = "14.000000";
        loop_filter_r_arr[27] = "14.500000";
        loop_filter_r_arr[28] = "15.000000";
        loop_filter_r_arr[29] = "15.500000";
        loop_filter_r_arr[30] = "16.000000";
        loop_filter_r_arr[31] = "16.500000";
        loop_filter_r_arr[32] = "17.000000";
        loop_filter_r_arr[33] = "17.500000";
        loop_filter_r_arr[34] = "18.000000";
        loop_filter_r_arr[35] = "18.500000";
        loop_filter_r_arr[36] = "19.000000";
        loop_filter_r_arr[37] = "19.500000";
        loop_filter_r_arr[38] = "20.000000";
        loop_filter_r_arr[39] = "20.500000";

        if (m == 0)
        begin
            i_clk5_counter    = "c5" ;
            i_clk4_counter    = "c4" ;
            i_clk3_counter    = "c3" ;
            i_clk2_counter    = "c2" ;
            i_clk1_counter    = "c1" ;
            i_clk0_counter    = "c0" ;
        end
        else begin
            i_clk5_counter    = alpha_tolower(clk5_counter);
            i_clk4_counter    = alpha_tolower(clk4_counter);
            i_clk3_counter    = alpha_tolower(clk3_counter);
            i_clk2_counter    = alpha_tolower(clk2_counter);
            i_clk1_counter    = alpha_tolower(clk1_counter);
            i_clk0_counter    = alpha_tolower(clk0_counter);
        end

        // VCO feedback loop settings for external feedback mode
        // first find which counter is used for feedback
        if (l_operation_mode == "external_feedback")
        begin
            op_mode = 1;
            if (l_feedback_source == "clk0")
                ext_fbk_cntr = i_clk0_counter;
            else if (l_feedback_source == "clk1")
                ext_fbk_cntr = i_clk1_counter;
            else if (l_feedback_source == "clk2")
                ext_fbk_cntr = i_clk2_counter;
            else if (l_feedback_source == "clk3")
                ext_fbk_cntr = i_clk3_counter;
            else if (l_feedback_source == "clk4")
                ext_fbk_cntr = i_clk4_counter;
            else if (l_feedback_source == "clk5")
                ext_fbk_cntr = i_clk5_counter;
            else ext_fbk_cntr = "c0";

            if (ext_fbk_cntr == "c0")
                ext_fbk_cntr_index = 0;
            else if (ext_fbk_cntr == "c1")
                ext_fbk_cntr_index = 1;
            else if (ext_fbk_cntr == "c2")
                ext_fbk_cntr_index = 2;
            else if (ext_fbk_cntr == "c3")
                ext_fbk_cntr_index = 3;
            else if (ext_fbk_cntr == "c4")
                ext_fbk_cntr_index = 4;
            else if (ext_fbk_cntr == "c5")
                ext_fbk_cntr_index = 5;
        end
        else
        begin
            op_mode = 0;
            ext_fbk_cntr_index = 0;
        end

        if (m == 0)
        begin 

            // set the limit of the divide_by value that can be returned by
            // the following function.
            max_d_value = 500;
            
            // scale down the multiply_by and divide_by values provided by the design
            // before attempting to use them in the calculations below
            find_simple_integer_fraction(clk0_multiply_by, clk0_divide_by,
                            max_d_value, i_clk0_mult_by, i_clk0_div_by);
            find_simple_integer_fraction(clk1_multiply_by, clk1_divide_by,
                            max_d_value, i_clk1_mult_by, i_clk1_div_by);
            find_simple_integer_fraction(clk2_multiply_by, clk2_divide_by,
                            max_d_value, i_clk2_mult_by, i_clk2_div_by);
            find_simple_integer_fraction(clk3_multiply_by, clk3_divide_by,
                            max_d_value, i_clk3_mult_by, i_clk3_div_by);
            find_simple_integer_fraction(clk4_multiply_by, clk4_divide_by,
                            max_d_value, i_clk4_mult_by, i_clk4_div_by);
            find_simple_integer_fraction(clk5_multiply_by, clk5_divide_by,
                            max_d_value, i_clk5_mult_by, i_clk5_div_by);

            // convert user parameters to advanced
            if (((l_pll_type == "fast") || (l_pll_type == "lvds")) && (vco_multiply_by != 0) && (vco_divide_by != 0))
            begin
                i_n = vco_divide_by;
                i_m = vco_multiply_by;
            end
            else begin
                i_n = 1;
                i_m = lcm  (i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,
                            i_clk4_mult_by, i_clk5_mult_by,
                            1, 1, 1, 1, inclk0_input_frequency);
            end

            i_c_high[0] = counter_high (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by, i_m, i_n), clk0_duty_cycle);
            i_c_high[1] = counter_high (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by, i_m, i_n), clk1_duty_cycle);
            i_c_high[2] = counter_high (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by, i_m, i_n), clk2_duty_cycle);
            i_c_high[3] = counter_high (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by, i_m, i_n), clk3_duty_cycle);
            i_c_high[4] = counter_high (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);
            i_c_high[5] = counter_high (output_counter_value(i_clk5_div_by,
                                        i_clk5_mult_by,  i_m, i_n), clk5_duty_cycle);

            i_c_low[0]  = counter_low  (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by,  i_m, i_n), clk0_duty_cycle);
            i_c_low[1]  = counter_low  (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by,  i_m, i_n), clk1_duty_cycle);
            i_c_low[2]  = counter_low  (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by,  i_m, i_n), clk2_duty_cycle);
            i_c_low[3]  = counter_low  (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by,  i_m, i_n), clk3_duty_cycle);
            i_c_low[4]  = counter_low  (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);
            i_c_low[5]  = counter_low  (output_counter_value(i_clk5_div_by,
                                        i_clk5_mult_by,  i_m, i_n), clk5_duty_cycle);

            if (l_pll_type == "flvds")
            begin
                // Need to readjust phase shift values when the clock multiply value has been readjusted.
                new_multiplier = clk0_multiply_by / i_clk0_mult_by;
                i_clk0_phase_shift = (clk0_phase_shift_num * new_multiplier);
                i_clk1_phase_shift = (clk1_phase_shift_num * new_multiplier);
                i_clk2_phase_shift = (clk2_phase_shift_num * new_multiplier);
            end
            else
            begin
                i_clk0_phase_shift = get_int_phase_shift(clk0_phase_shift, clk0_phase_shift_num);
                i_clk1_phase_shift = get_int_phase_shift(clk1_phase_shift, clk1_phase_shift_num);
                i_clk2_phase_shift = get_int_phase_shift(clk2_phase_shift, clk2_phase_shift_num);
            end

            max_neg_abs = maxnegabs   ( i_clk0_phase_shift,
                                        i_clk1_phase_shift,
                                        i_clk2_phase_shift,
                                        str2int(clk3_phase_shift),
                                        str2int(clk4_phase_shift),
                                        str2int(clk5_phase_shift),
                                        0, 0, 0, 0);

            i_c_initial[0] = counter_initial(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[1] = counter_initial(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[2] = counter_initial(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[3] = counter_initial(get_phase_degree(ph_adjust(str2int(clk3_phase_shift), max_neg_abs)), i_m, i_n);
            i_c_initial[4] = counter_initial(get_phase_degree(ph_adjust(str2int(clk4_phase_shift), max_neg_abs)), i_m, i_n);
            i_c_initial[5] = counter_initial(get_phase_degree(ph_adjust(str2int(clk5_phase_shift), max_neg_abs)), i_m, i_n);

            i_c_mode[0] = counter_mode(clk0_duty_cycle, output_counter_value(i_clk0_div_by, i_clk0_mult_by,  i_m, i_n));
            i_c_mode[1] = counter_mode(clk1_duty_cycle,output_counter_value(i_clk1_div_by, i_clk1_mult_by,  i_m, i_n));
            i_c_mode[2] = counter_mode(clk2_duty_cycle,output_counter_value(i_clk2_div_by, i_clk2_mult_by,  i_m, i_n));
            i_c_mode[3] = counter_mode(clk3_duty_cycle,output_counter_value(i_clk3_div_by, i_clk3_mult_by,  i_m, i_n));
            i_c_mode[4] = counter_mode(clk4_duty_cycle,output_counter_value(i_clk4_div_by, i_clk4_mult_by,  i_m, i_n));
            i_c_mode[5] = counter_mode(clk5_duty_cycle,output_counter_value(i_clk5_div_by, i_clk5_mult_by,  i_m, i_n));

            i_m_ph    = counter_ph(get_phase_degree(max_neg_abs), i_m, i_n);
            i_m_initial = counter_initial(get_phase_degree(max_neg_abs), i_m, i_n);
            
            i_c_ph[0] = counter_ph(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[1] = counter_ph(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[2] = counter_ph(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[3] = counter_ph(get_phase_degree(ph_adjust(str2int(clk3_phase_shift),max_neg_abs)), i_m, i_n);
            i_c_ph[4] = counter_ph(get_phase_degree(ph_adjust(str2int(clk4_phase_shift),max_neg_abs)), i_m, i_n);
            i_c_ph[5] = counter_ph(get_phase_degree(ph_adjust(str2int(clk5_phase_shift),max_neg_abs)), i_m, i_n);

            // in external feedback mode, need to adjust M value to take
            // into consideration the external feedback counter value
            if (l_operation_mode == "external_feedback")
            begin
                // if there is a negative phase shift, m_initial can only be 1
                if (max_neg_abs > 0)
                    i_m_initial = 1;

                if (i_c_mode[ext_fbk_cntr_index] == "bypass")
                    output_count = 1;
                else
                    output_count = i_c_high[ext_fbk_cntr_index] + i_c_low[ext_fbk_cntr_index];

                new_divisor = gcd(i_m, output_count);
                i_m = i_m / new_divisor;
                i_n = output_count / new_divisor;
            end

        end
        else 
        begin //  m != 0

            i_n = n;
            i_m = m;
            i_c_high[0] = c0_high;
            i_c_high[1] = c1_high;
            i_c_high[2] = c2_high;
            i_c_high[3] = c3_high;
            i_c_high[4] = c4_high;
            i_c_high[5] = c5_high;
            i_c_low[0]  = c0_low;
            i_c_low[1]  = c1_low;
            i_c_low[2]  = c2_low;
            i_c_low[3]  = c3_low;
            i_c_low[4]  = c4_low;
            i_c_low[5]  = c5_low;
            i_c_initial[0] = c0_initial;
            i_c_initial[1] = c1_initial;
            i_c_initial[2] = c2_initial;
            i_c_initial[3] = c3_initial;
            i_c_initial[4] = c4_initial;
            i_c_initial[5] = c5_initial;
            i_c_mode[0] = translate_string(alpha_tolower(c0_mode));
            i_c_mode[1] = translate_string(alpha_tolower(c1_mode));
            i_c_mode[2] = translate_string(alpha_tolower(c2_mode));
            i_c_mode[3] = translate_string(alpha_tolower(c3_mode));
            i_c_mode[4] = translate_string(alpha_tolower(c4_mode));
            i_c_mode[5] = translate_string(alpha_tolower(c5_mode));
            i_c_ph[0]  = c0_ph;
            i_c_ph[1]  = c1_ph;
            i_c_ph[2]  = c2_ph;
            i_c_ph[3]  = c3_ph;
            i_c_ph[4]  = c4_ph;
            i_c_ph[5]  = c5_ph;
            i_m_ph   = m_ph;        // default
            i_m_initial = m_initial;

        end // user to advanced conversion

        refclk_period = inclk0_input_frequency * i_n;

        m_times_vco_period = refclk_period;
        new_m_times_vco_period = refclk_period;

        fbclk_period = 0;
        high_time = 0;
        low_time = 0;
        schedule_vco = 0;
        vco_out[7:0] = 8'b0;
        vco_tap[7:0] = 8'b0;
        fbclk_last_value = 0;
        offset = 0;
        temp_offset = 0;
        got_first_refclk = 0;
        got_first_fbclk = 0;
        fbclk_time = 0;
        first_fbclk_time = 0;
        refclk_time = 0;
        first_schedule = 1;
        sched_time = 0;
        vco_val = 0;
        c0_got_first_rising_edge = 0;
        c1_got_first_rising_edge = 0;
        vco_c0_last_value = 0;
        c0_count = 2;
        c0_initial_count = 1;
        c1_count = 2;
        c1_initial_count = 1;
        c0_tmp = 0;
        c1_tmp = 0;
        gate_count = 0;
        gate_out = 0;
        initial_delay = 0;
        fbk_phase = 0;
        for (i = 0; i <= 7; i = i + 1)
        begin
            phase_shift[i] = 0;
            last_phase_shift[i] = 0;
        end
        fbk_delay = 0;
        inclk_n = 0;
        cycle_to_adjust = 0;
        m_delay = 0;
        vco_c0 = 0;
        vco_c1 = 0;
        total_pull_back = 0;
        pull_back_M = 0;
        vco_period_was_phase_adjusted = 0;
        phase_adjust_was_scheduled = 0;
        ena_ipd_last_value = 0;
        inclk_out_of_range = 0;
        scandone_tmp = 0;
        schedule_vco_last_value = 0;

        // set initial values for counter parameters
        m_initial_val = i_m_initial;
        m_val[0] = i_m;
        n_val[0] = i_n;
        m_ph_val = i_m_ph;
        m_ph_val_orig = i_m_ph;
        m_ph_val_tmp = i_m_ph;
        m_val_tmp[0] = i_m;

        m_val[1] = m2;
        n_val[1] = n2;

        if (m_val[0] == 1)
            m_mode_val[0] = "bypass";
        else m_mode_val[0] = "";
        if (m_val[1] == 1)
            m_mode_val[1] = "bypass";
        if (n_val[0] == 1)
            n_mode_val[0] = "bypass";
        if (n_val[1] == 1)
            n_mode_val[1] = "bypass";

        for (i = 0; i < 6; i=i+1)
        begin
            c_high_val[i] = i_c_high[i];
            c_low_val[i] = i_c_low[i];
            c_initial_val[i] = i_c_initial[i];
            c_mode_val[i] = i_c_mode[i];
            c_ph_val[i] = i_c_ph[i];
            c_high_val_tmp[i] = i_c_high[i];
            c_low_val_tmp[i] = i_c_low[i];
            if (c_mode_val[i] == "bypass")
            begin
                if (l_pll_type == "fast" || l_pll_type == "lvds")
                begin
                    c_high_val[i] = 5'b10000;
                    c_low_val[i] = 5'b10000;
                    c_high_val_tmp[i] = 5'b10000;
                    c_low_val_tmp[i] = 5'b10000;
                end
                else begin
                    c_high_val[i] = 9'b100000000;
                    c_low_val[i] = 9'b100000000;
                    c_high_val_tmp[i] = 9'b100000000;
                    c_low_val_tmp[i] = 9'b100000000;
                end
            end

            c_mode_val_tmp[i] = i_c_mode[i];
            c_ph_val_tmp[i] = i_c_ph[i];

            c_ph_val_orig[i] = i_c_ph[i];
            c_high_val_hold[i] = i_c_high[i];
            c_low_val_hold[i] = i_c_low[i];
            c_mode_val_hold[i] = i_c_mode[i];
        end

        lfc_val = loop_filter_c;
        lfr_val = loop_filter_r;
        cp_curr_val = charge_pump_current;

        i = 0;
        j = 0;
        inclk_last_value = 0;

        ext_fbk_cntr_ph = 0;
        ext_fbk_cntr_initial = 1;

        // initialize clkswitch variables

        clk0_is_bad = 0;
        clk1_is_bad = 0;
        inclk0_last_value = 0;
        inclk1_last_value = 0;
        other_clock_value = 0;
        other_clock_last_value = 0;
        primary_clk_is_bad = 0;
        current_clk_is_bad = 0;
        external_switch = 0;
        if (l_primary_clock == "inclk0")
            current_clock = 0;
        else current_clock = 1;

        active_clock = 0;   // primary_clk is always inclk0
        if (l_pll_type == "fast")
            l_switch_over_type = "manual";

        if (l_switch_over_type == "manual" && clkswitch_ipd === 1'b1)
        begin
            current_clock = 1;
            active_clock = 1;
        end
        clkloss_tmp = 0;
        got_curr_clk_falling_edge_after_clkswitch = 0;
        clk0_count = 0;
        clk1_count = 0;
        switch_over_count = 0;

        // initialize reconfiguration variables
        // quiet_time
        quiet_time = slowest_clk  ( c_high_val[0]+c_low_val[0], c_mode_val[0],
                                    c_high_val[1]+c_low_val[1], c_mode_val[1],
                                    c_high_val[2]+c_low_val[2], c_mode_val[2],
                                    c_high_val[3]+c_low_val[3], c_mode_val[3],
                                    c_high_val[4]+c_low_val[4], c_mode_val[4],
                                    c_high_val[5]+c_low_val[5], c_mode_val[5],
                                    refclk_period, m_val[0]);
        reconfig_err = 0;
        error = 0;
        scanread_active_edge = 0;
        if ((l_pll_type == "fast") || (l_pll_type == "lvds"))
        begin
            scan_chain_length = FAST_SCAN_CHAIN;
            num_output_cntrs = 4;
        end
        else
        begin
            scan_chain_length = GPP_SCAN_CHAIN;
            num_output_cntrs = 6;
        end
        scanread_reg = 0;
        scanwrite_reg = 0;
        scanwrite_enabled = 0;
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        c5_rising_edge_transfer_done = 0;
        got_first_scanclk = 0;
        got_first_gated_scanclk = 0;
        gated_scanclk = 1;
        scanread_setup_violation = 0;
        index = 0;

        // initialize the scan_chain contents
        // CP/LF  bits
        scan_data[11:0] = 12'b0;
        for (i = 0; i <= 3; i = i + 1)
        begin
            if ((l_pll_type == "fast") || (l_pll_type == "lvds"))
            begin
                if (fpll_loop_filter_c_arr[i] == loop_filter_c)
                    scan_data[11:10] = i;
            end
            else begin
                if (loop_filter_c_arr[i] == loop_filter_c)
                    scan_data[11:10] = i;
            end
        end
        for (i = 0; i <= 15; i = i + 1)
        begin
            if (charge_pump_curr_arr[i] == charge_pump_current)
                scan_data[3:0] = i;
        end
        for (i = 0; i <= 39; i = i + 1)
        begin
            if (loop_filter_r_arr[i] == loop_filter_r)
            begin
                if ((i >= 16) && (i <= 23))
                    scan_data[9:4] = i+8;
                else if ((i >= 24) && (i <= 31))
                    scan_data[9:4] = i+16;
                else if (i >= 32)
                    scan_data[9:4] = i+24;
                else
                    scan_data[9:4] = i;
            end
        end

        if (l_pll_type == "fast" || l_pll_type == "lvds")
        begin
            scan_data[21:12] = 10'b0; // M, C3-C0 ph
            // C0-C3 high
            scan_data[25:22] = c_high_val[0];
            scan_data[35:32] = c_high_val[1];
            scan_data[45:42] = c_high_val[2];
            scan_data[55:52] = c_high_val[3];
            // C0-C3 low
            scan_data[30:27] = c_low_val[0];
            scan_data[40:37] = c_low_val[1];
            scan_data[50:47] = c_low_val[2];
            scan_data[60:57] = c_low_val[3];
            // C0-C3 mode
            for (i = 0; i < 4; i = i + 1)
            begin
                if (c_mode_val[i] == "   off" || c_mode_val[i] == "bypass")
                begin
                    scan_data[26 + (10*i)] = 1;
                    if (c_mode_val[i] == "   off")
                        scan_data[31 + (10*i)] = 1;
                    else
                        scan_data[31 + (10*i)] = 0;
                end
                else begin
                    scan_data[26 + (10*i)] = 0;
                    if (c_mode_val[i] == "   odd")
                        scan_data[31 + (10*i)] = 1;
                    else
                        scan_data[31 + (10*i)] = 0;
                end
            end
            // M
            if (m_mode_val[0] == "bypass")
            begin
                scan_data[66] = 1;
                scan_data[71] = 0;
                scan_data[65:62] = 4'b0;
                scan_data[70:67] = 4'b0;
            end
            else begin
                scan_data[66] = 0;       // set BYPASS bit to 0
                scan_data[70:67] = m_val[0]/2;   // set M low
                if (m_val[0] % 2 == 0)
                begin
                    // M is an even no. : set M high = low,
                    // set odd/even bit to 0
                    scan_data[65:62] = scan_data[70:67];
                    scan_data[71] = 0;
                end
                else begin // M is odd : M high = low + 1
                    scan_data[65:62] = (m_val[0]/2) + 1;
                    scan_data[71] = 1;
                end
            end
            // N
            scan_data[73:72] = n_val[0];
            if (n_mode_val[0] == "bypass")
            begin
                scan_data[74] = 1;
                scan_data[73:72] = 2'b0;
            end
        end
        else begin             // PLL type is enhanced/auto
            scan_data[25:12] = 14'b0;

            // C5-C0 high
            scan_data[33:26] = c_high_val[5];
            scan_data[51:44] = c_high_val[4];
            scan_data[69:62] = c_high_val[3];
            scan_data[87:80] = c_high_val[2];
            scan_data[105:98] = c_high_val[1];
            scan_data[123:116] = c_high_val[0];
            // C5-C0 low
            scan_data[42:35] = c_low_val[5];
            scan_data[60:53] = c_low_val[4];
            scan_data[78:71] = c_low_val[3];
            scan_data[96:89] = c_low_val[2];
            scan_data[114:107] = c_low_val[1];
            scan_data[132:125] = c_low_val[0];

            for (i = 5; i >= 0; i = i - 1)
            begin
                if (c_mode_val[i] == "   off" || c_mode_val[i] == "bypass")
                begin
                    scan_data[124 - (18*i)] = 1;
                    if (c_mode_val[i] == "   off")
                        scan_data[133 - (18*i)] = 1;
                    else
                        scan_data[133 - (18*i)] = 0;
                end
                else begin
                    scan_data[124 - (18*i)] = 0;
                    if (c_mode_val[i] == "   odd")
                        scan_data[133 - (18*i)] = 1;
                    else
                        scan_data[133 - (18*i)] = 0;
                end
            end

            scan_data[142:134] = m_val[0];
            scan_data[143] = 0;
            scan_data[152:144] = m_val[1];
            scan_data[153] = 0;
            if (m_mode_val[0] == "bypass")
            begin
                scan_data[143] = 1;
                scan_data[142:134] = 9'b0;
            end
            if (m_mode_val[1] == "bypass")
            begin
                scan_data[153] = 1;
                scan_data[152:144] = 9'b0;
            end

            scan_data[162:154] = n_val[0];
            scan_data[172:164] = n_val[1];
            if (n_mode_val[0] == "bypass")
            begin
                scan_data[163] = 1;
                scan_data[162:154] = 9'b0;
            end
            if (n_mode_val[1] == "bypass")
            begin
                scan_data[173] = 1;
                scan_data[172:164] = 9'b0;
            end
        end

        // now save this counter's parameters
        ext_fbk_cntr_high = c_high_val[ext_fbk_cntr_index];
        ext_fbk_cntr_low = c_low_val[ext_fbk_cntr_index];
        ext_fbk_cntr_ph = c_ph_val[ext_fbk_cntr_index];
        ext_fbk_cntr_initial = c_initial_val[ext_fbk_cntr_index];
        ext_fbk_cntr_mode = c_mode_val[ext_fbk_cntr_index];

        if (ext_fbk_cntr_mode == "bypass")
            ext_fbk_cntr_modulus = 1;
        else
            ext_fbk_cntr_modulus = ext_fbk_cntr_high + ext_fbk_cntr_low;

        l_index = 1;
        stop_vco = 0;
        cycles_to_lock = 0;
        cycles_to_unlock = 0;
        locked_tmp = 0;
        pll_is_locked = 0;
        pll_about_to_lock = 0;
        no_warn = 1'b0;

        // check if pll is in test mode
        if (m_test_source != 5 || c0_test_source != 5 || c1_test_source != 5 || c2_test_source != 5 || c3_test_source != 5 || c4_test_source != 5 || c5_test_source != 5)
            pll_in_test_mode = 1'b1;
        else
            pll_in_test_mode = 1'b0;


        pll_is_in_reset = 0;
        pll_is_disabled = 0;
        if (l_pll_type == "fast" || l_pll_type == "lvds")
            is_fast_pll = 1;
        else is_fast_pll = 0;

        if (c1_use_casc_in == "on")
            ic1_use_casc_in = 1;
        else
            ic1_use_casc_in = 0;
        if (c2_use_casc_in == "on")
            ic2_use_casc_in = 1;
        else
            ic2_use_casc_in = 0;
        if (c3_use_casc_in == "on")
            ic3_use_casc_in = 1;
        else
            ic3_use_casc_in = 0;
        if (c4_use_casc_in == "on")
            ic4_use_casc_in = 1;
        else
            ic4_use_casc_in = 0;
        if (c5_use_casc_in == "on")
            ic5_use_casc_in = 1;
        else
            ic5_use_casc_in = 0;

        tap0_is_active = 1;
        next_vco_sched_time = 0;
    end

    always @(clkswitch_ipd)
    begin
        if (clkswitch_ipd === 1'b1 && l_switch_over_type == "auto")
            external_switch = 1;
        else if (l_switch_over_type == "manual")
        begin
            if (clkswitch_ipd === 1'b1)
            begin
                current_clock = 1;
                active_clock = 1;
                inclk_n = inclk1_ipd;
            end
            else if (clkswitch_ipd === 1'b0)
            begin
                current_clock = 0;
                active_clock = 0;
                inclk_n = inclk0_ipd;
            end
        end
    end

    always @(inclk0_ipd or inclk1_ipd)
    begin
        // save the inclk event value
        if (inclk0_ipd !== inclk0_last_value)
        begin
            if (current_clock != 0)
                other_clock_value = inclk0_ipd;
        end
        if (inclk1_ipd !== inclk1_last_value)
        begin
            if (current_clock != 1)
                other_clock_value = inclk1_ipd;
        end

        // check if either input clk is bad
        if (inclk0_ipd === 1'b1 && inclk0_ipd !== inclk0_last_value)
        begin
            clk0_count = clk0_count + 1;
            clk0_is_bad = 0;
            clk1_count = 0;
            if (clk0_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk1_is_bad = 1;
                if (current_clock == 1)
                    current_clk_is_bad = 1;
            end
        end
        if (inclk1_ipd === 1'b1 && inclk1_ipd !== inclk1_last_value)
        begin
            clk1_count = clk1_count + 1;
            clk1_is_bad = 0;
            clk0_count = 0;
            if (clk1_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk0_is_bad = 1;
                if (current_clock == 0)
                    current_clk_is_bad = 1;
            end
        end

        // check if the bad clk is the primary clock, which is always clk0
        if (clk0_is_bad == 1'b1)
            primary_clk_is_bad = 1;
        else
            primary_clk_is_bad = 0;

        // actual switching -- manual switch
        if ((inclk0_ipd !== inclk0_last_value) && current_clock == 0)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk0_ipd === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_n = inclk0_ipd;
                end
            end
            else inclk_n = inclk0_ipd;
        end
        if ((inclk1_ipd !== inclk1_last_value) && current_clock == 1)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk1_ipd === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_n = inclk1_ipd;
                end
            end
            else inclk_n = inclk1_ipd;
        end

        // actual switching -- automatic switch
        if ((other_clock_value == 1'b1) && (other_clock_value != other_clock_last_value) && (l_switch_over_on_lossclk == "on") && l_enable_switch_over_counter == "on" && primary_clk_is_bad)
            switch_over_count = switch_over_count + 1;

        if ((other_clock_value == 1'b0) && (other_clock_value != other_clock_last_value))
        begin
            if ((external_switch && (got_curr_clk_falling_edge_after_clkswitch || current_clk_is_bad)) || (l_switch_over_on_lossclk == "on" && primary_clk_is_bad && l_pll_type !== "fast" && l_pll_type !== "lvds" && (clkswitch_ipd !== 1'b1) && ((l_enable_switch_over_counter == "off" || switch_over_count == switch_over_counter))))
            begin
                got_curr_clk_falling_edge_after_clkswitch = 0;
                if (current_clock == 0)
                    current_clock = 1;
                else
                    current_clock = 0;
                active_clock = ~active_clock;
                switch_over_count = 0;
                external_switch = 0;
                current_clk_is_bad = 0;
            end
        end

        if (l_switch_over_on_lossclk == "on" && (clkswitch_ipd != 1'b1))
        begin
            if (primary_clk_is_bad)
                clkloss_tmp = 1;
            else
                clkloss_tmp = 0;
        end
        else clkloss_tmp = clkswitch_ipd;

        inclk0_last_value = inclk0_ipd;
        inclk1_last_value = inclk1_ipd;
        other_clock_last_value = other_clock_value;

    end

    and (clkbad[0], clk0_is_bad, 1'b1);
    and (clkbad[1], clk1_is_bad, 1'b1);
    and (activeclock, active_clock, 1'b1);
    and (clkloss, clkloss_tmp, 1'b1);

    MF_pll_reg ena_reg ( .clk(!inclk_n),
                                .ena(1'b1),
                                .d(ena_ipd),
                                .clrn(1'b1),
                                .prn(1'b1),
                                .q(pllena_reg));

    and (test_mode_inclk, inclk_n, pllena_reg);
    assign n_cntr_inclk = (pll_in_test_mode === 1'b1) ? test_mode_inclk : inclk_n;
    assign ena_pll = (pll_in_test_mode === 1'b1) ? pllena_reg : ena_ipd;

    assign inclk_m = (m_test_source == 0) ? n_cntr_inclk : op_mode == 1 ? (l_feedback_source == "clk0" ? clk_tmp[0] :
                        l_feedback_source == "clk1" ? clk_tmp[1] :
                        l_feedback_source == "clk2" ? clk_tmp[2] :
                        l_feedback_source == "clk3" ? clk_tmp[3] :
                        l_feedback_source == "clk4" ? clk_tmp[4] :
                        l_feedback_source == "clk5" ? clk_tmp[5] : 1'b0) :
                        inclk_m_from_vco;


    arm_m_cntr m1 (.clk(inclk_m),
                        .reset(areset_ipd || (!ena_pll) || stop_vco),
                        .cout(fbclk),
                        .initial_value(m_initial_val),
                        .modulus(m_val[0]),
                        .time_delay(m_delay));

    arm_n_cntr n1 (.clk(n_cntr_inclk),
                        .reset(areset_ipd),
                        .cout(refclk),
                        .modulus(n_val[0]));


    always @(vco_out[0])
    begin
        // now schedule the other taps with the appropriate phase-shift
        for (k = 1; k <= 7; k=k+1)
        begin
            phase_shift[k] = (k*tmp_vco_per)/8;
            vco_out[k] <= #(phase_shift[k]) vco_out[0];
        end
    end

    always @(vco_out)
    begin
        // check which VCO TAP has event
        for (x = 0; x <= 7; x = x + 1)
        begin
            if (vco_out[x] !== vco_out_last_value[x])
            begin
                // TAP 'X' has event
                if ((x == 0) && (!pll_is_in_reset) && (!pll_is_disabled) && (stop_vco !== 1'b1))
                begin
                    if (vco_out[0] == 1'b1)
                        tap0_is_active = 1;
                    if (tap0_is_active == 1'b1)
                        vco_tap[0] <= vco_out[0];
                end
                else if (tap0_is_active == 1'b1)
                    vco_tap[x] <= vco_out[x];
                if (stop_vco === 1'b1)
                    vco_out[x] <= 1'b0;
            end
        end
        vco_out_last_value = vco_out;
    end

    always @(vco_tap)
    begin
        // check which VCO TAP has event
        for (x = 0; x <= 7; x = x + 1)
        begin
            if (vco_tap[x] !== vco_tap_last_value[x])
            begin
                if (c_ph_val[0] == x)
                begin
                    inclk_c0_from_vco <= vco_tap[x];
                    if (is_fast_pll == 1'b1)
                    begin
                    if (ena0_cntr == 0)
                        inclk_sclkout0_from_vco <= vco_tap[x];
                    if (ena1_cntr == 0)
                        inclk_sclkout1_from_vco <= vco_tap[x];
                    end
                end
                if (c_ph_val[1] == x)
                begin
                    inclk_c1_from_vco <= vco_tap[x];
                    if (is_fast_pll == 1'b1)
                    begin
                    if (ena0_cntr == 1)
                        inclk_sclkout0_from_vco <= vco_tap[x];
                    if (ena1_cntr == 1)
                        inclk_sclkout1_from_vco <= vco_tap[x];
                    end
                end
                if (c_ph_val[2] == x)
                    inclk_c2_from_vco <= vco_tap[x];
                if (c_ph_val[3] == x)
                    inclk_c3_from_vco <= vco_tap[x];
                if (c_ph_val[4] == x)
                    inclk_c4_from_vco <= vco_tap[x];
                if (c_ph_val[5] == x)
                    inclk_c5_from_vco <= vco_tap[x];
                if (m_ph_val == x)
                    inclk_m_from_vco <= vco_tap[x];
            end
        end
        if (scanwrite_enabled === 1'b1)
        begin
        for (x = 0; x <= 7; x = x + 1)
        begin
            if ((vco_tap[x] === 1'b0) && (vco_tap[x] !== vco_tap_last_value[x]))
            begin
                for (y = 0; y <= 5; y = y + 1)
                begin
                    if (c_ph_val[y] == x)
                        c_ph_val[y] <= c_ph_val_tmp[y];
                end
                if (m_ph_val == x)
                    m_ph_val <= m_ph_val_tmp;
            end
        end
        end

        // reset all counter phase tap values to POF programmed values
        if (areset_ipd === 1'b1)
        begin
            m_ph_val <= m_ph_val_orig;
            m_ph_val_tmp <= m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
            begin
                c_ph_val[i] <= c_ph_val_orig[i];
                c_ph_val_tmp[i] <= c_ph_val_orig[i];
            end
        end

        vco_tap_last_value = vco_tap;
    end

    always @(inclk_sclkout0_from_vco)
    begin
        sclkout0_tmp <= inclk_sclkout0_from_vco;
    end
    always @(inclk_sclkout1_from_vco)
    begin
        sclkout1_tmp <= inclk_sclkout1_from_vco;
    end

    assign inclk_c0 = (c0_test_source == 0) ? n_cntr_inclk : (c0_test_source == 1) ? refclk : inclk_c0_from_vco;

    arm_scale_cntr c0 (.clk(inclk_c0),
                            .reset(areset_ipd || (!ena_pll) || stop_vco),
                            .cout(c0_clk),
                            .high(c_high_val[0]),
                            .low(c_low_val[0]),
                            .initial_value(c_initial_val[0]),
                            .mode(c_mode_val[0]),
                            .ph_tap(c_ph_val[0]));

    always @(posedge c0_clk)
    begin
        if (scanwrite_enabled == 1'b1)
        begin
            c_high_val[0] <= c_high_val_tmp[0];
            c_mode_val[0] <= c_mode_val_tmp[0];
            c0_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge c0_clk)
    begin
        if (c0_rising_edge_transfer_done)
        begin
            c_low_val[0] <= c_low_val_tmp[0];
        end
    end

    assign inclk_c1 = (c1_test_source == 0) ? n_cntr_inclk : (c1_test_source == 2) ? fbclk : (ic1_use_casc_in == 1) ? c0_clk : inclk_c1_from_vco;

    arm_scale_cntr c1 (.clk(inclk_c1),
                            .reset(areset_ipd || (!ena_pll) || stop_vco),
                            .cout(c1_clk),
                            .high(c_high_val[1]),
                            .low(c_low_val[1]),
                            .initial_value(c_initial_val[1]),
                            .mode(c_mode_val[1]),
                            .ph_tap(c_ph_val[1]));

    always @(posedge c1_clk)
    begin
        if (scanwrite_enabled == 1'b1)
        begin
            c_high_val[1] <= c_high_val_tmp[1];
            c_mode_val[1] <= c_mode_val_tmp[1];
            c1_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge c1_clk)
    begin
        if (c1_rising_edge_transfer_done)
        begin
            c_low_val[1] <= c_low_val_tmp[1];
        end
    end

    assign inclk_c2 = (c2_test_source == 0) ? n_cntr_inclk : (ic2_use_casc_in == 1) ? c1_clk : inclk_c2_from_vco;

    arm_scale_cntr c2 (.clk(inclk_c2),
                            .reset(areset_ipd || (!ena_pll) || stop_vco),
                            .cout(c2_clk),
                            .high(c_high_val[2]),
                            .low(c_low_val[2]),
                            .initial_value(c_initial_val[2]),
                            .mode(c_mode_val[2]),
                            .ph_tap(c_ph_val[2]));

    always @(posedge c2_clk)
    begin
        if (scanwrite_enabled == 1'b1)
        begin
            c_high_val[2] <= c_high_val_tmp[2];
            c_mode_val[2] <= c_mode_val_tmp[2];
            c2_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge c2_clk)
    begin
        if (c2_rising_edge_transfer_done)
        begin
            c_low_val[2] <= c_low_val_tmp[2];
        end
    end

    assign inclk_c3 = (c3_test_source == 0) ? n_cntr_inclk : (ic3_use_casc_in == 1) ? c2_clk : inclk_c3_from_vco;
    arm_scale_cntr c3 (.clk(inclk_c3),
                            .reset(areset_ipd || (!ena_pll) || stop_vco),
                            .cout(c3_clk),
                            .high(c_high_val[3]),
                            .low(c_low_val[3]),
                            .initial_value(c_initial_val[3]),
                            .mode(c_mode_val[3]),
                            .ph_tap(c_ph_val[3]));

    always @(posedge c3_clk)
    begin
        if (scanwrite_enabled == 1'b1)
        begin
            c_high_val[3] <= c_high_val_tmp[3];
            c_mode_val[3] <= c_mode_val_tmp[3];
            c3_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge c3_clk)
    begin
        if (c3_rising_edge_transfer_done)
        begin
            c_low_val[3] <= c_low_val_tmp[3];
        end
    end

    assign inclk_c4 = ((c4_test_source == 0) ? n_cntr_inclk : (ic4_use_casc_in == 1) ? c3_clk : inclk_c4_from_vco);
    arm_scale_cntr c4 (.clk(inclk_c4),
                            .reset(areset_ipd || (!ena_pll) || stop_vco),
                            .cout(c4_clk),
                            .high(c_high_val[4]),
                            .low(c_low_val[4]),
                            .initial_value(c_initial_val[4]),
                            .mode(c_mode_val[4]),
                            .ph_tap(c_ph_val[4]));

    always @(posedge c4_clk)
    begin
        if (scanwrite_enabled == 1'b1)
        begin
            c_high_val[4] <= c_high_val_tmp[4];
            c_mode_val[4] <= c_mode_val_tmp[4];
            c4_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge c4_clk)
    begin
        if (c4_rising_edge_transfer_done)
        begin
            c_low_val[4] <= c_low_val_tmp[4];
        end
    end

    assign inclk_c5 = ((c5_test_source == 0) ? n_cntr_inclk : (ic5_use_casc_in == 1) ? c4_clk : inclk_c5_from_vco);
    arm_scale_cntr c5 (.clk(inclk_c5),
                            .reset(areset_ipd || (!ena_pll) || stop_vco),
                            .cout(c5_clk),
                            .high(c_high_val[5]),
                            .low(c_low_val[5]),
                            .initial_value(c_initial_val[5]),
                            .mode(c_mode_val[5]),
                            .ph_tap(c_ph_val[5]));

    always @(posedge c5_clk)
    begin
        if (scanwrite_enabled == 1'b1)
        begin
            c_high_val[5] <= c_high_val_tmp[5];
            c_mode_val[5] <= c_mode_val_tmp[5];
            c5_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge c5_clk)
    begin
        if (c5_rising_edge_transfer_done)
        begin
            c_low_val[5] <= c_low_val_tmp[5];
        end
    end

    always @(vco_tap[c_ph_val[0]] or posedge areset_ipd or negedge ena_pll or stop_vco)
    begin
        if (areset_ipd == 1'b1 || ena_pll == 1'b0 || stop_vco == 1'b1)
        begin
            c0_count = 2;
            c0_initial_count = 1;
            c0_got_first_rising_edge = 0;

        end
        else begin
            if (c0_got_first_rising_edge == 1'b0)
            begin
                if (vco_tap[c_ph_val[0]] == 1'b1 && vco_tap[c_ph_val[0]] != vco_c0_last_value)
                begin
                    if (c0_initial_count == c_initial_val[0])
                        c0_got_first_rising_edge = 1;
                    else
                        c0_initial_count = c0_initial_count + 1;
                end
            end
            else if (vco_tap[c_ph_val[0]] != vco_c0_last_value)
            begin
                c0_count = c0_count + 1;
                if (c0_count == (c_high_val[0] + c_low_val[0]) * 2)
                    c0_count  = 1;
            end
            if (vco_tap[c_ph_val[0]] == 1'b0 && vco_tap[c_ph_val[0]] != vco_c0_last_value)
            begin
                if (c0_count == 1)
                begin
                    c0_tmp = 1;
                    c0_got_first_rising_edge = 0;
                end
                else c0_tmp = 0;
            end
        end
        vco_c0_last_value = vco_tap[c_ph_val[0]];
    end

    always @(vco_tap[c_ph_val[1]] or posedge areset_ipd or negedge ena_pll or stop_vco)
    begin
        if (areset_ipd == 1'b1 || ena_pll == 1'b0 || stop_vco == 1'b1)
        begin
            c1_count = 2;
            c1_initial_count = 1;
            c1_got_first_rising_edge = 0;
        end
        else begin
            if (c1_got_first_rising_edge == 1'b0)
            begin
                if (vco_tap[c_ph_val[1]] == 1'b1 && vco_tap[c_ph_val[1]] != vco_c1_last_value)
                begin
                    if (c1_initial_count == c_initial_val[1])
                        c1_got_first_rising_edge = 1;
                    else
                        c1_initial_count = c1_initial_count + 1;
                end
            end
            else if (vco_tap[c_ph_val[1]] != vco_c1_last_value)
            begin
                c1_count = c1_count + 1;
                if (c1_count == (c_high_val[1] + c_low_val[1]) * 2)
                    c1_count  = 1;
            end
            if (vco_tap[c_ph_val[1]] == 1'b0 && vco_tap[c_ph_val[1]] != vco_c1_last_value)
            begin
                if (c1_count == 1)
                begin
                    c1_tmp = 1;
                    c1_got_first_rising_edge = 0;
                end
                else c1_tmp = 0;
            end
        end
        vco_c1_last_value = vco_tap[c_ph_val[1]];
    end

    assign enable0_tmp = (ena0_cntr == 0) ? c0_tmp : c1_tmp;
    assign enable1_tmp = (ena1_cntr == 0) ? c0_tmp : c1_tmp;

    always @ (inclk_n or ena_pll or areset_ipd)
    begin
        if (areset_ipd == 1'b1 || ena_pll == 1'b0)
        begin
            gate_count = 0;
            gate_out = 0; 
        end
        else if (inclk_n == 1'b1 && inclk_last_value != inclk_n)
        begin
            gate_count = gate_count + 1;
            if (l_sim_gate_lock_device_behavior == "on")
            begin
                if (gate_count == gate_lock_counter)
                    gate_out = 1;
            end
            else begin
                if (gate_count == GATE_LOCK_CYCLES)
                    gate_out = 1;
            end
        end
        inclk_last_value = inclk_n;
    end

    assign locked = (l_gate_lock_signal == "yes") ? gate_out && locked_tmp : locked_tmp;

    always @(posedge scanread_ipd)
    begin
        scanread_active_edge = $time;
    end

    always @ (scanclk_ipd)
    begin
        if (scanclk_ipd === 1'b0 && scanclk_last_value === 1'b1)
        begin
            // enable scanwrite on falling edge
            scanwrite_enabled <= scanwrite_reg;
        end
        if (scanread_reg === 1'b1)
            gated_scanclk <= scanclk_ipd && scanread_reg;
        else
            gated_scanclk <= 1'b1;
        if (scanclk_ipd === 1'b1 && scanclk_last_value === 1'b0)
        begin
            // register scanread and scanwrite
            scanread_reg <= scanread_ipd;
            scanwrite_reg <= scanwrite_ipd;

            if (got_first_scanclk)
                scanclk_period = $time - scanclk_last_rising_edge;
            else begin
                got_first_scanclk = 1;
            end
            // reset got_first_scanclk on falling edge of scanread_reg
            if (scanread_ipd == 1'b0 && scanread_reg == 1'b1)
            begin
                got_first_scanclk = 0;
                got_first_gated_scanclk = 0;
            end

            scanclk_last_rising_edge = $time;
        end
        scanclk_last_value = scanclk_ipd;
    end

    always @(posedge gated_scanclk)
    begin
        if ($time > 0)
        begin
        if (!got_first_gated_scanclk)
        begin
            got_first_gated_scanclk = 1;
//            if ($time - scanread_active_edge < scanclk_period)
//            begin
//                scanread_setup_violation = 1;
//                $display("Warning : SCANREAD must go high at least one cycle before SCANDATA is read in.");
//                $display ("Time: %0t  Instance: %m", $time);
//            end
        end
        for (j = scan_chain_length-1; j >= 1; j = j - 1)
        begin
            scan_data[j] = scan_data[j - 1];
        end
        scan_data[0] <= scandata_ipd;
        end
    end

    assign scandataout_tmp = (l_pll_type == "fast" || l_pll_type == "lvds") ? scan_data[FAST_SCAN_CHAIN-1] : scan_data[GPP_SCAN_CHAIN-1];

    always @(posedge scandone_tmp)
    begin
            if (reconfig_err == 1'b0)
            begin
                $display("NOTE : %s PLL Reprogramming completed with the following values (Values in parantheses are original values) : ", family_name);
                $display ("Time: %0t  Instance: %m", $time);

                $display("               N modulus =   %0d (%0d) ", n_val[0], n_val_old[0]);
                $display("               M modulus =   %0d (%0d) ", m_val[0], m_val_old[0]);
                $display("               M ph_tap =    %0d (%0d) ", m_ph_val, m_ph_val_old);
                if (ss > 0)
                begin
                    $display(" M2 modulus =   %0d (%0d) ", m_val[1], m_val_old[1]);
                    $display(" N2 modulus =   %0d (%0d) ", n_val[1], n_val_old[1]);
                end

                for (i = 0; i < num_output_cntrs; i=i+1)
                begin
                    $display("              C%0d  high = %0d (%0d),       C%0d  low = %0d (%0d),       C%0d  mode = %s (%s),       C%0d  phase tap = %0d (%0d)", i, c_high_val[i], c_high_val_old[i], i, c_low_val_tmp[i], c_low_val_old[i], i, c_mode_val[i], c_mode_val_old[i], i, c_ph_val[i], c_ph_val_old[i]);
                end

                // display Charge pump and loop filter values
                $display ("               Charge Pump Current (uA) =   %0d (%0d) ", cp_curr_val, cp_curr_old);
                $display ("               Loop Filter Capacitor (pF) =   %0d (%0d) ", lfc_val, lfc_old);
                $display ("               Loop Filter Resistor (Kohm) =   %s (%s) ", lfr_val, lfr_old);
            end
            else begin
                $display("Warning : Errors were encountered during PLL reprogramming. Please refer to error/warning messages above.");
                $display ("Time: %0t  Instance: %m", $time);
            end
    end

    always @(scanwrite_enabled)
    begin
        if (scanwrite_enabled === 1'b0 && scanwrite_last_value === 1'b1)
        begin
            // falling edge : deassert scandone
            scandone_tmp <= #(1.5*scanclk_period) 1'b0;
            // reset counter transfer flags
            c0_rising_edge_transfer_done = 0;
            c1_rising_edge_transfer_done = 0;
            c2_rising_edge_transfer_done = 0;
            c3_rising_edge_transfer_done = 0;
            c4_rising_edge_transfer_done = 0;
            c5_rising_edge_transfer_done = 0;
        end
        if (scanwrite_enabled === 1'b1 && scanwrite_last_value !== scanwrite_enabled)
        begin

            $display ("NOTE : %s PLL Reprogramming initiated ....", family_name);
            $display ("Time: %0t  Instance: %m", $time);

            error = 0;
            reconfig_err = 0;
            scanread_setup_violation = 0;

            // make temp. copy of scan_data for processing
            tmp_scan_data = scan_data;

            // save old values
            cp_curr_old = cp_curr_val;
            lfc_old = lfc_val;
            lfr_old = lfr_val;

            // CP
            // Bits 0-3 : all values are legal
            cp_curr_val = charge_pump_curr_arr[scan_data[3:0]];

            // LF Resistance : bits 4-9
            // values from 010000 - 010111, 100000 - 100111, 
            //             110000- 110111 are illegal
            if (((tmp_scan_data[9:4] >= 6'b010000) && (tmp_scan_data[9:4] <= 6'b010111)) || 
                ((tmp_scan_data[9:4] >= 6'b100000) && (tmp_scan_data[9:4] <= 6'b100111)) ||
                ((tmp_scan_data[9:4] >= 6'b110000) && (tmp_scan_data[9:4] <= 6'b110111)))
            begin
                $display ("Illegal bit settings for Loop Filter Resistance. Legal bit values range from 000000 to 001111, 011000 to 011111, 101000 to 101111 and 111000 to 111111. Reconfiguration may not work.");
                $display ("Time: %0t  Instance: %m", $time);
                reconfig_err = 1;
            end
            else begin
                i = scan_data[9:4];
                if (i >= 56 )
                    i = i - 24;
                else if ((i >= 40) && (i <= 47))
                    i = i - 16;
                else if ((i >= 24) && (i <= 31))
                    i = i - 8;
                lfr_val = loop_filter_r_arr[i];
            end

            // LF Capacitance : bits 10,11 : all values are legal
            if ((l_pll_type == "fast") || (l_pll_type == "lvds"))
                lfc_val = fpll_loop_filter_c_arr[scan_data[11:10]];
            else
                lfc_val = loop_filter_c_arr[scan_data[11:10]];

            // save old values for display info.
            for (i=0; i<=1; i=i+1)
            begin
                m_val_old[i] = m_val[i];
                n_val_old[i] = n_val[i];
                m_mode_val_old[i] = m_mode_val[i];
                n_mode_val_old[i] = n_mode_val[i];
            end
            m_ph_val_old = m_ph_val;
            for (i=0; i<=5; i=i+1)
            begin
                c_high_val_old[i] = c_high_val[i];
                c_low_val_old[i] = c_low_val[i];
                c_ph_val_old[i] = c_ph_val[i];
                c_mode_val_old[i] = c_mode_val[i];
            end

            // first the M counter phase : bit order same for fast and GPP
            if (scan_data[12] == 1'b0)
            begin
                // do nothing
            end
            else if (scan_data[12] === 1'b1 && scan_data[13] === 1'b1)
            begin
                m_ph_val_tmp = m_ph_val_tmp + 1;
                if (m_ph_val_tmp > 7)
                    m_ph_val_tmp = 0;
            end
            else if (scan_data[12] === 1'b1 && scan_data[13] === 1'b0)
            begin
                m_ph_val_tmp = m_ph_val_tmp - 1;
                if (m_ph_val_tmp < 0)
                    m_ph_val_tmp = 7;
            end
            else 
            begin
                $display ("Warning : Illegal bit settings for M counter phase tap. Reconfiguration may not work.");
                $display ("Time: %0t  Instance: %m", $time);
                reconfig_err = 1;
            end

            // read the fast PLL bits.
            if (l_pll_type == "fast" || l_pll_type == "lvds")
            begin
                // C3-C0 phase bits
                for (i = 3; i >= 0; i=i-1)
                begin
                    if (tmp_scan_data[14] == 1'b0)
                    begin
                        // do nothing
                    end
                    else if (tmp_scan_data[14] === 1'b1)
                    begin
                        if (tmp_scan_data[15] === 1'b1)
                        begin
                            c_ph_val_tmp[i] = c_ph_val_tmp[i] + 1;
                            if (c_ph_val_tmp[i] > 7)
                                c_ph_val_tmp[i] = 0;
                        end
                        else if (tmp_scan_data[15] === 1'b0)
                        begin
                            c_ph_val_tmp[i] = c_ph_val_tmp[i] - 1;
                            if (c_ph_val_tmp[i] < 0)
                                c_ph_val_tmp[i] = 7;
                        end
                    end
                    tmp_scan_data = tmp_scan_data >> 2;
                end
                // C0-C3 counter moduli
                tmp_scan_data = scan_data;
                for (i = 0; i < 4; i=i+1)
                begin
                    if (tmp_scan_data[26] == 1'b1)
                    begin
                        c_mode_val_tmp[i] = "bypass";
                        if (tmp_scan_data[31] === 1'b1)
                        begin
                            c_mode_val_tmp[i] = "   off";
                            $display("Warning : The specified bit settings will turn OFF the C%0d counter. It cannot be turned on unless the part is re-initialized.", i);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                    end
                    else if (tmp_scan_data[31] == 1'b1)
                        c_mode_val_tmp[i] = "   odd";
                    else
                        c_mode_val_tmp[i] = "  even";
                    if (tmp_scan_data[25:22] === 4'b0000)
                        c_high_val_tmp[i] = 5'b10000;
                    else
                        c_high_val_tmp[i] = {1'b0, tmp_scan_data[25:22]};
                    if (tmp_scan_data[30:27] === 4'b0000)
                        c_low_val_tmp[i] = 5'b10000;
                    else
                        c_low_val_tmp[i] = {1'b0, tmp_scan_data[30:27]};

                    tmp_scan_data = tmp_scan_data >> 10;
                end
                // M
                error = 0;
                // some temporary storage
                if (scan_data[65:62] == 4'b0000)
                    m_hi = 5'b10000;
                else
                    m_hi = {1'b0, scan_data[65:62]};

                if (scan_data[70:67] == 4'b0000)
                    m_lo = 5'b10000;
                else
                    m_lo = {1'b0, scan_data[70:67]};

                m_val_tmp[0] = m_hi + m_lo;
                if (scan_data[66] === 1'b1)
                begin
                    if (scan_data[71] === 1'b1)
                    begin
                        // this will turn off the M counter : error
                        reconfig_err = 1;
                        error = 1;
                        $display ("The specified bit settings will turn OFF the M counter. This is illegal. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    else begin
                        // M counter is being bypassed
                        if (m_mode_val[0] !== "bypass")
                        begin
                            // Mode is switched : give warning
                            d_msg = display_msg(" M", 4);
                        end
                        m_val_tmp[0] = 32'b1;
                        m_mode_val[0] = "bypass";
                    end
                end
                else begin
                    if (m_mode_val[0] === "bypass")
                    begin
                        // Mode is switched : give warning
                        d_msg = display_msg(" M", 1);
                    end
                    m_mode_val[0] = "";
                    if (scan_data[71] === 1'b1)
                    begin
                        // odd : check for duty cycle, if not 50% -- error
                        if (m_hi - m_lo !== 1)
                        begin
                            reconfig_err = 1;
                            $display ("Warning : The M counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                    end
                    else begin // even mode
                        if (m_hi !== m_lo)
                        begin
                            reconfig_err = 1;
                            $display ("Warning : The M counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                    end
                end

                // N
                error = 0;
                n_val[0] = {1'b0, scan_data[73:72]};
                if (scan_data[74] !== 1'b1)
                begin
                    if (scan_data[73:72] == 2'b01)
                    begin
                        reconfig_err = 1;
                        error = 1;
                        // Cntr value is illegal : give warning
                        d_msg = display_msg(" N", 2);
                    end
                    else if (scan_data[73:72] == 2'b00)
                        n_val[0] = 3'b100;
                    if (error == 1'b0)
                    begin
                        if (n_mode_val[0] === "bypass")
                        begin
                            // Mode is switched : give warning
                            d_msg = display_msg(" N", 1);
                        end
                        n_mode_val[0] = "";
                    end
                end
                else if (scan_data[74] == 1'b1)     // bypass
                begin
                    if (scan_data[72] !== 1'b0)
                    begin
                        reconfig_err = 1;
                        error = 1;
                        // Cntr value is illegal : give warning
                        d_msg = display_msg(" N", 3);
                    end
                    else begin
                        if (n_mode_val[0] != "bypass")
                        begin
                            // Mode is switched : give warning
                            d_msg = display_msg(" N", 4);
                        end
                        n_val[0] = 2'b01;
                        n_mode_val[0] = "bypass";
                    end
                end
            end
            else begin      // pll type is auto or enhanced
                for (i = 0; i < 6; i=i+1)
                begin
                    if (tmp_scan_data[124] == 1'b1)
                    begin
                        c_mode_val_tmp[i] = "bypass";
                        if (tmp_scan_data[133] === 1'b1)
                        begin
                            c_mode_val_tmp[i] = "   off";
                            $display("Warning : The specified bit settings will turn OFF the C%0d counter. It cannot be turned on unless the part is re-initialized.", i);
                            $display ("Time: %0t  Instance: %m", $time);
                        end
                    end
                    else if (tmp_scan_data[133] == 1'b1)
                        c_mode_val_tmp[i] = "   odd";
                    else
                        c_mode_val_tmp[i] = "  even";
                    if (tmp_scan_data[123:116] === 8'b00000000)
                        c_high_val_tmp[i] = 9'b100000000;
                    else
                        c_high_val_tmp[i] = {1'b0, tmp_scan_data[123:116]};
                    if (tmp_scan_data[132:125] === 8'b00000000)
                        c_low_val_tmp[i] = 9'b100000000;
                    else
                        c_low_val_tmp[i] = {1'b0, tmp_scan_data[132:125]};

                    tmp_scan_data = tmp_scan_data << 18;
                end

                // the phase_taps
                tmp_scan_data = scan_data;
                for (i = 0; i < 6; i=i+1)
                begin
                    if (tmp_scan_data[14] == 1'b0)
                    begin
                        // do nothing
                    end
                    else if (tmp_scan_data[14] === 1'b1)
                    begin
                        if (tmp_scan_data[15] === 1'b1)
                        begin
                            c_ph_val_tmp[i] = c_ph_val_tmp[i] + 1;
                            if (c_ph_val_tmp[i] > 7)
                                c_ph_val_tmp[i] = 0;
                        end
                        else if (tmp_scan_data[15] === 1'b0)
                        begin
                            c_ph_val_tmp[i] = c_ph_val_tmp[i] - 1;
                            if (c_ph_val_tmp[i] < 0)
                                c_ph_val_tmp[i] = 7;
                        end
                    end
                    tmp_scan_data = tmp_scan_data >> 2;
                end
                ext_fbk_cntr_high = c_high_val[ext_fbk_cntr_index];
                ext_fbk_cntr_low = c_low_val[ext_fbk_cntr_index];
                ext_fbk_cntr_ph = c_ph_val[ext_fbk_cntr_index];
                ext_fbk_cntr_mode = c_mode_val[ext_fbk_cntr_index];

                // cntrs M/M2
                tmp_scan_data = scan_data;
                for (i=0; i<2; i=i+1)
                begin
                    if (i == 0 || (i == 1 && ss > 0))
                    begin
                        error = 0;
                        m_val_tmp[i] = {1'b0, tmp_scan_data[142:134]};
                        if (tmp_scan_data[143] !== 1'b1)
                        begin
                            if (tmp_scan_data[142:134] == 9'b000000001)
                            begin
                                reconfig_err = 1;
                                error = 1;
                                // Cntr value is illegal : give warning
                                if (i == 0)
                                    d_msg = display_msg(" M", 2);
                                else
                                    d_msg = display_msg("M2", 2);
                            end
                            else if (tmp_scan_data[142:134] == 9'b000000000)
                                m_val_tmp[i] = 10'b1000000000;
                            if (error == 1'b0)
                            begin
                                if (m_mode_val[i] === "bypass")
                                begin
                                    // Mode is switched : give warning
                                    if (i == 0)
                                        d_msg = display_msg(" M", 1);
                                    else
                                        d_msg = display_msg("M2", 1);
                                end
                                m_mode_val[i] = "";
                            end
                        end
                        else if (tmp_scan_data[143] == 1'b1)
                        begin
                            if (tmp_scan_data[134] !== 1'b0)
                            begin
                                reconfig_err = 1;
                                error = 1;
                                // Cntr value is illegal : give warning
                                if (i == 0)
                                    d_msg = display_msg(" M", 3);
                                else
                                    d_msg = display_msg("M2", 3);
                            end
                            else begin
                                if (m_mode_val[i] !== "bypass")
                                begin
                                    // Mode is switched: give warning
                                    if (i == 0)
                                        d_msg = display_msg(" M", 4);
                                    else
                                        d_msg = display_msg("M2", 4);
                                end
                                m_val_tmp[i] = 10'b0000000001;
                                m_mode_val[i] = "bypass";
                            end
                        end
                    end
                    tmp_scan_data = tmp_scan_data >> 10;
                end
                if (ss > 0)
                begin
                    if (m_mode_val[0] != m_mode_val[1])
                    begin
                        reconfig_err = 1;
                        error = 1;
                        $display ("Warning : Incompatible modes for M/M2 counters. Either both should be BYASSED or both NON-BYPASSED. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end

                // cntrs N/N2
                tmp_scan_data = scan_data;
                for (i=0; i<2; i=i+1)
                begin
                    if (i == 0 || (i == 1 && ss > 0))
                    begin
                        error = 0;
                        n_val[i] = 0;
                        n_val[i] = {1'b0, tmp_scan_data[162:154]};
                        if (tmp_scan_data[163] !== 1'b1)
                        begin
                            if (tmp_scan_data[162:154] == 9'b000000001)
                            begin
                                reconfig_err = 1;
                                error = 1;
                                // Cntr value is illegal : give warning
                                if (i == 0)
                                    d_msg = display_msg(" N", 2);
                                else
                                    d_msg = display_msg("N2", 2);
                            end
                            else if (tmp_scan_data[162:154] == 9'b000000000)
                                n_val[i] = 10'b1000000000;
                            if (error == 1'b0)
                            begin
                                if (n_mode_val[i] === "bypass")
                                begin
                                    // Mode is switched : give warning
                                    if (i == 0)
                                        d_msg = display_msg(" N", 1);
                                    else
                                        d_msg = display_msg("N2", 1);
                                end
                                n_mode_val[i] = "";
                            end
                        end
                        else if (tmp_scan_data[163] == 1'b1)     // bypass
                        begin
                            if (tmp_scan_data[154] !== 1'b0)
                            begin
                                reconfig_err = 1;
                                error = 1;
                                // Cntr value is illegal : give warning
                                if (i == 0)
                                    d_msg = display_msg(" N", 3);
                                else
                                    d_msg = display_msg("N2", 3);
                            end
                            else begin
                                if (n_mode_val[i] != "bypass")
                                begin
                                    // Mode is switched : give warning
                                    if (i == 0)
                                        d_msg = display_msg(" N", 4);
                                    else
                                        d_msg = display_msg("N2", 4);
                                end
                                n_val[i] = 10'b0000000001;
                                n_mode_val[i] = "bypass";
                            end
                        end
                    end
                    tmp_scan_data = tmp_scan_data >> 10;
                end
                if (ss > 0)
                begin
                    if (n_mode_val[0] != n_mode_val[1])
                    begin
                        reconfig_err = 1;
                        error = 1;
                        $display ("Warning : Incompatible modes for N/N2 counters. Either both should be BYASSED or both NON-BYPASSED. Reconfiguration may not work.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end
            end
            
            slowest_clk_old = slowest_clk  ( c_high_val[0]+c_low_val[0], c_mode_val[0],
                                        c_high_val[1]+c_low_val[1], c_mode_val[1],
                                        c_high_val[2]+c_low_val[2], c_mode_val[2],
                                        c_high_val[3]+c_low_val[3], c_mode_val[3],
                                        c_high_val[4]+c_low_val[4], c_mode_val[4],
                                        c_high_val[5]+c_low_val[5], c_mode_val[5],
                                        refclk_period, m_val[0]);

            slowest_clk_new = slowest_clk  ( c_high_val_tmp[0]+c_low_val_tmp[0], c_mode_val_tmp[0],
                                        c_high_val_tmp[1]+c_low_val_tmp[1], c_mode_val_tmp[1],
                                        c_high_val_tmp[2]+c_low_val_tmp[2], c_mode_val_tmp[2],
                                        c_high_val_tmp[3]+c_low_val_tmp[3], c_mode_val_tmp[3],
                                        c_high_val_tmp[4]+c_low_val_tmp[4], c_mode_val_tmp[4],
                                        c_high_val_tmp[5]+c_low_val_tmp[5], c_mode_val_tmp[5],
                                        refclk_period, m_val_tmp[0]);

            quiet_time = (slowest_clk_new > slowest_clk_old) ? slowest_clk_new : slowest_clk_old;
                                        
            // get quiet time in terms of scanclk cycles
            my_rem = quiet_time % scanclk_period;
            scanclk_cycles = quiet_time/scanclk_period;
            if (my_rem != 0)
                scanclk_cycles = scanclk_cycles + 1;

            scandone_tmp <= #((scanclk_cycles+0.5) * scanclk_period) 1'b1;
        end

        scanwrite_last_value = scanwrite_enabled;
    end

    always @(schedule_vco or areset_ipd or ena_pll)
    begin
        sched_time = 0;
    
        for (i = 0; i <= 7; i=i+1)
            last_phase_shift[i] = phase_shift[i];
     
        cycle_to_adjust = 0;
        l_index = 1;
        m_times_vco_period = new_m_times_vco_period;
    
        // give appropriate messages
        // if areset was asserted
        if (areset_ipd === 1'b1 && areset_ipd_last_value !== areset_ipd)
        begin
            $display (" Note : %s PLL was reset", family_name);
            $display ("Time: %0t  Instance: %m", $time);
            // reset lock parameters
            locked_tmp = 0;
            pll_is_locked = 0;
            pll_about_to_lock = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
            pll_is_in_reset = 1;
            tap0_is_active = 0;
            for (x = 0; x <= 7; x=x+1)
                vco_tap[x] <= 1'b0;
        end
    
        // areset deasserted : note time
        // note it as refclk_time to prevent false triggering
        // of stop_vco after areset
        if (areset_ipd === 1'b0 && areset_ipd_last_value === 1'b1 && pll_is_in_reset === 1'b1)
        begin
            refclk_time = $time;
            pll_is_in_reset = 0;
            if ((ena_pll === 1'b1) && (stop_vco !== 1'b1) && (next_vco_sched_time <= $time))
                schedule_vco = ~ schedule_vco;
        end

        // if ena was deasserted
        if (ena_pll == 1'b0 && ena_ipd_last_value !== ena_pll)
        begin
            $display (" Note : %s PLL is disabled", family_name);
            $display ("Time: %0t  Instance: %m", $time);
            pll_is_disabled = 1;
            tap0_is_active = 0;
            for (x = 0; x <= 7; x=x+1)
                vco_tap[x] <= 1'b0;
        end

        if (ena_pll == 1'b1 && ena_ipd_last_value !== ena_pll)
        begin
            $display (" Note : %s PLL is enabled", family_name);
            $display ("Time: %0t  Instance: %m", $time);
            pll_is_disabled = 0;
            if ((areset_ipd !== 1'b1) && (stop_vco !== 1'b1) && (next_vco_sched_time < $time))
                schedule_vco = ~ schedule_vco;
        end
    
        // illegal value on areset_ipd
        if (areset_ipd === 1'bx && (areset_ipd_last_value === 1'b0 || areset_ipd_last_value === 1'b1))
        begin
            $display("Warning : Illegal value 'X' detected on ARESET input");
            $display ("Time: %0t  Instance: %m", $time);
        end
    
        if (areset_ipd == 1'b1 || ena_pll == 1'b0 || stop_vco == 1'b1)
        begin
   
            // reset lock parameters
            locked_tmp = 0;
            pll_is_locked = 0;
            pll_about_to_lock = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
    
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = 0;
            got_first_fbclk = 0;
            fbclk_time = 0;
            first_fbclk_time = 0;
            fbclk_period = 0;
    
            vco_period_was_phase_adjusted = 0;
            phase_adjust_was_scheduled = 0;
        end
 
        if ( ($time == 0 && first_schedule == 1'b1) || (schedule_vco !== schedule_vco_last_value && (stop_vco !== 1'b1) && (ena_pll === 1'b1) && (areset_ipd !== 1'b1)) )
        begin
            // calculate loop_xplier : this will be different from m_val in ext. fbk mode
            loop_xplier = m_val[0];
            loop_initial = i_m_initial - 1;
            loop_ph = m_ph_val;
    
            if (op_mode == 1)
            begin
                if (ext_fbk_cntr_mode == "bypass")
                    ext_fbk_cntr_modulus = 1;
                else
                    ext_fbk_cntr_modulus = ext_fbk_cntr_high + ext_fbk_cntr_low;

                loop_xplier = m_val[0] * (ext_fbk_cntr_modulus);
                loop_ph = ext_fbk_cntr_ph;
                loop_initial = ext_fbk_cntr_initial - 1 + ((i_m_initial - 1) * ext_fbk_cntr_modulus);
            end
    
            // convert initial value to delay
            initial_delay = (loop_initial * m_times_vco_period)/loop_xplier;
    
            // convert loop ph_tap to delay
            rem = m_times_vco_period % loop_xplier;
            vco_per = m_times_vco_period/loop_xplier;
            if (rem != 0)
                vco_per = vco_per + 1;
            fbk_phase = (loop_ph * vco_per)/8;
    
            if (op_mode == 1)
            begin
                pull_back_M = (i_m_initial - 1) * (ext_fbk_cntr_modulus) * (m_times_vco_period/loop_xplier);
    
                while (pull_back_M > refclk_period)
                    pull_back_M = pull_back_M - refclk_period;
            end
            else begin
                pull_back_M = initial_delay + fbk_phase;
            end
    
            total_pull_back = pull_back_M;
            if (l_simulation_type == "timing")
                total_pull_back = total_pull_back + pll_compensation_delay;
    
            while (total_pull_back > refclk_period)
                total_pull_back = total_pull_back - refclk_period;
    
            if (total_pull_back > 0)
                offset = refclk_period - total_pull_back;
            else
                offset = 0;
    
            if (op_mode == 1)
            begin
                fbk_delay = pull_back_M;
                if (l_simulation_type == "timing")
                    fbk_delay = fbk_delay + pll_compensation_delay;
            end
            else begin
                fbk_delay = total_pull_back - fbk_phase;
                if (fbk_delay < 0)
                begin
                    offset = offset - fbk_phase;
                    fbk_delay = total_pull_back;
                end
            end
    
            // assign m_delay
            m_delay = fbk_delay;
    
            for (i = 1; i <= loop_xplier; i=i+1)
            begin
                // adjust cycles
                tmp_vco_per = m_times_vco_period/loop_xplier;
                if (rem != 0 && l_index <= rem)
                begin
                    tmp_rem = (loop_xplier * l_index) % rem;
                    cycle_to_adjust = (loop_xplier * l_index) / rem;
                    if (tmp_rem != 0)
                        cycle_to_adjust = cycle_to_adjust + 1;
                end
                if (cycle_to_adjust == i)
                begin
                    tmp_vco_per = tmp_vco_per + 1;
                    l_index = l_index + 1;
                end
    
                // calculate high and low periods
                high_time = tmp_vco_per/2;
                if (tmp_vco_per % 2 != 0)
                    high_time = high_time + 1;
                low_time = tmp_vco_per - high_time;
    
                // schedule the rising and falling egdes
                for (j=0; j<=1; j=j+1)
                begin
                    vco_val = ~vco_val;
                    if (vco_val == 1'b0)
                        sched_time = sched_time + high_time;
                    else
                        sched_time = sched_time + low_time;
    
                    // schedule tap 0
                    vco_out[0] <= #(sched_time) vco_val;

                end
            end
            if (first_schedule)
            begin
                vco_val = ~vco_val;
                if (vco_val == 1'b0)
                    sched_time = sched_time + high_time;
                else
                    sched_time = sched_time + low_time;
                // schedule tap 0
                vco_out[0] <= #(sched_time) vco_val;
                first_schedule = 0;
            end

            schedule_vco <= #(sched_time) ~schedule_vco;
            next_vco_sched_time = $time + sched_time;

            if (vco_period_was_phase_adjusted)
            begin
                m_times_vco_period = refclk_period;
                new_m_times_vco_period = refclk_period;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 1;
    
                tmp_vco_per = m_times_vco_period/loop_xplier;
                for (k = 0; k <= 7; k=k+1)
                    phase_shift[k] = (k*tmp_vco_per)/8;
            end
        end
    
        areset_ipd_last_value = areset_ipd;
        ena_ipd_last_value = ena_pll;
        schedule_vco_last_value = schedule_vco;
    
    end

    always @(pfdena_ipd)
    begin
        if (pfdena_ipd === 1'b0)
        begin
            if (pll_is_locked)
                locked_tmp = 1'bx;
            pll_is_locked = 0;
            cycles_to_lock = 0;
            $display (" Note : %s PFDENA was deasserted", family_name);
            $display ("Time: %0t  Instance: %m", $time);
        end
        else if (pfdena_ipd === 1'b1 && pfdena_ipd_last_value === 1'b0)
        begin
            // PFD was disabled, now enabled again
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = $time;
        end
        pfdena_ipd_last_value = pfdena_ipd;
    end

    always @(negedge refclk or negedge fbclk)
    begin
        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    always @(posedge refclk or posedge fbclk)
    begin
        if (refclk == 1'b1 && refclk_last_value !== refclk && areset_ipd === 1'b0)
        begin
            if (! got_first_refclk)
            begin
                got_first_refclk = 1;
            end else
            begin
                got_second_refclk = 1;
                refclk_period = $time - refclk_time;

                // check if incoming freq. will cause VCO range to be
                // exceeded
                if ((vco_max != 0 && vco_min != 0) && (pfdena_ipd === 1'b1) &&
                    ((refclk_period/loop_xplier > vco_max) ||
                    (refclk_period/loop_xplier < vco_min)) )
                begin
                    if (pll_is_locked == 1'b1)
                    begin
                        $display ("Warning : Input clock freq. is not within VCO range. PLL may lose lock");
                        $display ("Time: %0t  Instance: %m", $time);
                        if (inclk_out_of_range === 1'b1)
                        begin
                            // unlock
                            pll_is_locked = 0;
                            locked_tmp = 0;
                            pll_about_to_lock = 0;
                            cycles_to_lock = 0;
                            $display ("Note : %s PLL lost lock", family_name);
                            $display ("Time: %0t  Instance: %m", $time);
                            vco_period_was_phase_adjusted = 0;
                            phase_adjust_was_scheduled = 0;
                        end
                    end
                    else begin
                        if (no_warn == 1'b0)
                        begin
                            $display ("Warning : Input clock freq. is not within VCO range. PLL may not lock");
                            $display ("Time: %0t  Instance: %m", $time);
                            no_warn = 1'b1;
                        end
                    end
                    inclk_out_of_range = 1;
                end
                else begin
                    inclk_out_of_range = 0;
                end

            end
            if (stop_vco == 1'b1)
            begin
                stop_vco = 0;
                schedule_vco = ~schedule_vco;
            end
            refclk_time = $time;
        end

        if (fbclk == 1'b1 && fbclk_last_value !== fbclk)
        begin
            if (scanwrite_enabled === 1'b1)
            begin
                m_val[0] <= m_val_tmp[0];
                m_val[1] <= m_val_tmp[1];
            end
            if (!got_first_fbclk)
            begin
                got_first_fbclk = 1;
                first_fbclk_time = $time;
            end
            else
                fbclk_period = $time - fbclk_time;

            // need refclk_period here, so initialized to proper value above
            if ( ( ($time - refclk_time > 1.5 * refclk_period) && pfdena_ipd === 1'b1 && pll_is_locked === 1'b1) || ( ($time - refclk_time > 5 * refclk_period) && pfdena_ipd === 1'b1) )
            begin
                stop_vco = 1;
                // reset
                got_first_refclk = 0;
                got_first_fbclk = 0;
                got_second_refclk = 0;
                if (pll_is_locked == 1'b1)
                begin
                    pll_is_locked = 0;
                    locked_tmp = 0;
                    $display ("Note : %s PLL lost lock due to loss of input clock", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
                end
                pll_about_to_lock = 0;
                cycles_to_lock = 0;
                cycles_to_unlock = 0;
                first_schedule = 1;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 0;
                tap0_is_active = 0;
                for (x = 0; x <= 7; x=x+1)
                    vco_tap[x] <= 1'b0;
            end
            else if (!pll_is_locked && ($time - refclk_time > 2 * refclk_period) && pfdena_ipd === 1'b1)
            begin
                inclk_out_of_range = 1;
            end
            fbclk_time = $time;
        end

        if (got_second_refclk && pfdena_ipd === 1'b1 && (!inclk_out_of_range))
        begin
            // now we know actual incoming period
            if (abs(fbclk_time - refclk_time) <= 5 || (got_first_fbclk && abs(refclk_period - abs(fbclk_time - refclk_time)) <= 5))
            begin
                // considered in phase
                if (cycles_to_lock == valid_lock_multiplier - 1)
                    pll_about_to_lock <= 1;
                if (cycles_to_lock == valid_lock_multiplier)
                begin
                    if (pll_is_locked === 1'b0)
                    begin
                        $display (" Note : %s PLL locked to incoming clock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    pll_is_locked = 1;
                    locked_tmp = 1;
                    cycles_to_unlock = 0;
                end
                // increment lock counter only if the second part of the above
                // time check is not true
                if (!(abs(refclk_period - abs(fbclk_time - refclk_time)) <= 5))
                begin
                    cycles_to_lock = cycles_to_lock + 1;
                end

                // adjust m_times_vco_period
                new_m_times_vco_period = refclk_period;

            end else
            begin
                // if locked, begin unlock
                if (pll_is_locked)
                begin
                    cycles_to_unlock = cycles_to_unlock + 1;
                    if (cycles_to_unlock == invalid_lock_multiplier)
                    begin
                        pll_is_locked = 0;
                        locked_tmp = 0;
                        pll_about_to_lock = 0;
                        cycles_to_lock = 0;
                        $display ("Note : %s PLL lost lock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        vco_period_was_phase_adjusted = 0;
                        phase_adjust_was_scheduled = 0;
                    end
                end
                if (abs(refclk_period - fbclk_period) <= 2)
                begin
                    // frequency is still good
                    if ($time == fbclk_time && (!phase_adjust_was_scheduled))
                    begin
                        if (abs(fbclk_time - refclk_time) > refclk_period/2)
                        begin
                            new_m_times_vco_period = m_times_vco_period + (refclk_period - abs(fbclk_time - refclk_time));
                            vco_period_was_phase_adjusted = 1;
                        end else
                        begin
                            new_m_times_vco_period = m_times_vco_period - abs(fbclk_time - refclk_time);
                            vco_period_was_phase_adjusted = 1;
                        end
                    end
                end else
                begin
                    new_m_times_vco_period = refclk_period;
                    phase_adjust_was_scheduled = 0;
                end
            end
        end

        if (reconfig_err == 1'b1)
        begin
            locked_tmp = 0;
        end

        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    assign clk_tmp[0] = i_clk0_counter == "c0" ? c0_clk : i_clk0_counter == "c1" ? c1_clk : i_clk0_counter == "c2" ? c2_clk : i_clk0_counter == "c3" ? c3_clk : i_clk0_counter == "c4" ? c4_clk : i_clk0_counter == "c5" ? c5_clk : 1'b0;
    assign clk_tmp[1] = i_clk1_counter == "c0" ? c0_clk : i_clk1_counter == "c1" ? c1_clk : i_clk1_counter == "c2" ? c2_clk : i_clk1_counter == "c3" ? c3_clk : i_clk1_counter == "c4" ? c4_clk : i_clk1_counter == "c5" ? c5_clk : 1'b0;
    assign clk_tmp[2] = i_clk2_counter == "c0" ? c0_clk : i_clk2_counter == "c1" ? c1_clk : i_clk2_counter == "c2" ? c2_clk : i_clk2_counter == "c3" ? c3_clk : i_clk2_counter == "c4" ? c4_clk : i_clk2_counter == "c5" ? c5_clk : 1'b0;
    assign clk_tmp[3] = i_clk3_counter == "c0" ? c0_clk : i_clk3_counter == "c1" ? c1_clk : i_clk3_counter == "c2" ? c2_clk : i_clk3_counter == "c3" ? c3_clk : i_clk3_counter == "c4" ? c4_clk : i_clk3_counter == "c5" ? c5_clk : 1'b0;
    assign clk_tmp[4] = i_clk4_counter == "c0" ? c0_clk : i_clk4_counter == "c1" ? c1_clk : i_clk4_counter == "c2" ? c2_clk : i_clk4_counter == "c3" ? c3_clk : i_clk4_counter == "c4" ? c4_clk : i_clk4_counter == "c5" ? c5_clk : 1'b0;
    assign clk_tmp[5] = i_clk5_counter == "c0" ? c0_clk : i_clk5_counter == "c1" ? c1_clk : i_clk5_counter == "c2" ? c2_clk : i_clk5_counter == "c3" ? c3_clk : i_clk5_counter == "c4" ? c4_clk : i_clk5_counter == "c5" ? c5_clk : 1'b0;

    assign clk_out[0] = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode === 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? clk_tmp[0] : 1'bx;
    assign clk_out[1] = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode === 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? clk_tmp[1] : 1'bx;
    assign clk_out[2] = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode === 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? clk_tmp[2] : 1'bx;
    assign clk_out[3] = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode === 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? clk_tmp[3] : 1'bx;
    assign clk_out[4] = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode === 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? clk_tmp[4] : 1'bx;
    assign clk_out[5] = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode === 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? clk_tmp[5] : 1'bx;

    assign sclkout0 = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode == 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? sclkout0_tmp : 1'bx;

    assign sclkout1 = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode == 1'b1) || (pll_about_to_lock == 1'b1 && !reconfig_err) ? sclkout1_tmp : 1'bx;

    assign enable_0 = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode == 1'b1) || pll_about_to_lock == 1'b1 ? enable0_tmp : 1'bx;
    assign enable_1 = (areset_ipd === 1'b1 || ena_pll === 1'b0 || pll_in_test_mode == 1'b1) || pll_about_to_lock == 1'b1 ? enable1_tmp : 1'bx;


    // ACCELERATE OUTPUTS
    and (clk[0], 1'b1, clk_out[0]);
    and (clk[1], 1'b1, clk_out[1]);
    and (clk[2], 1'b1, clk_out[2]);
    and (clk[3], 1'b1, clk_out[3]);
    and (clk[4], 1'b1, clk_out[4]);
    and (clk[5], 1'b1, clk_out[5]);

    and (sclkout[0], 1'b1, sclkout0);
    and (sclkout[1], 1'b1, sclkout1);

    and (enable0, 1'b1, enable_0);
    and (enable1, 1'b1, enable_1);

    and (scandataout, 1'b1, scandataout_tmp);
    and (scandone, 1'b1, scandone_tmp);

endmodule // MF_stratixii_pll

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : ttn_m_cntr
//
// Description : Simulation model for the M counter. This is the
//               loop feedback counter for the Stratix III PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module ttn_m_cntr   ( clk,
                            reset,
                            cout,
                            initial_value,
                            modulus,
                            time_delay);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] initial_value;
    input [31:0] modulus;
    input [31:0] time_delay;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
            cout_tmp <= tmp_cout;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'b1 && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
                cout_tmp <= #(time_delay) tmp_cout;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                    cout_tmp <= #(time_delay) tmp_cout;
                end
            end
        end
        end
        clk_last_value = clk;

//        cout_tmp <= #(time_delay) tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // ttn_m_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : ttn_n_cntr
//
// Description : Simulation model for the N counter. This is the
//               input clock divide counter for the Stratix III PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module ttn_n_cntr   ( clk,
                            reset,
                            cout,
                            modulus);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] modulus;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk == 1 && clk_last_value !== clk && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                end
            end
        end
        clk_last_value = clk;

    end

    assign cout = tmp_cout;

endmodule // ttn_n_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : ttn_scale_cntr
//
// Description : Simulation model for the output scale-down counters.
//               This is a common model for the C0-C9
//               output counters of the Stratix III PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module ttn_scale_cntr   ( clk,
                                reset,
                                cout,
                                high,
                                low,
                                initial_value,
                                mode,
                                ph_tap);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] high;
    input [31:0] low;
    input [31:0] initial_value;
    input [8*6:1] mode;
    input [31:0] ph_tap;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg init;
    integer count;
    integer output_shift_count;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 0;
        tmp_cout = 0;
        output_shift_count = 1;
    end

    always @(clk or reset)
    begin
        if (init !== 1'b1)
        begin
            clk_last_value = 0;
            init = 1'b1;
        end
        if (reset)
        begin
            count = 1;
            output_shift_count = 1;
            tmp_cout = 0;
            first_rising_edge = 0;
        end
        else if (clk_last_value !== clk)
        begin
            if (mode == "   off")
                tmp_cout = 0;
            else if (mode == "bypass")
            begin
                tmp_cout = clk;
                first_rising_edge = 1;
            end
            else if (first_rising_edge == 0)
            begin
                if (clk == 1)
                begin
                    if (output_shift_count == initial_value)
                    begin
                        tmp_cout = clk;
                        first_rising_edge = 1;
                    end
                    else
                        output_shift_count = output_shift_count + 1;
                end
            end
            else if (output_shift_count < initial_value)
            begin
                if (clk == 1)
                    output_shift_count = output_shift_count + 1;
            end
            else
            begin
                count = count + 1;
                if (mode == "  even" && (count == (high*2) + 1))
                    tmp_cout = 0;
                else if (mode == "   odd" && (count == (high*2)))
                    tmp_cout = 0;
                else if (count == (high + low)*2 + 1)
                begin
                    tmp_cout = 1;
                    count = 1;        // reset count
                end
            end
        end
        clk_last_value = clk;
        cout_tmp <= tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // ttn_scale_cntr


//////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_stratixiii_pll
//
// Description : Behavioral model for StratixIII pll.
// 
// Limitations : Does not support Spread Spectrum and Bandwidth.
//
// Outputs     : Up to 10 output clocks, each defined by its own set of
//               parameters. Locked output (active high) indicates when the
//               PLL locks. clkbad and activeclock are used for
//               clock switchover to indicate which input clock has gone
//               bad, when the clock switchover initiates and which input
//               clock is being used as the reference, respectively.
//               scandataout is the data output of the serial scan chain.
//
// New Features : The list below outlines key new features in Stratix III:
//                1. Dynamic Phase Reconfiguration
//                2. Dynamic PLL Reconfiguration (different protocol)
//                3. More output counters
//////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps
`define STXIII_PLL_WORD_LENGTH 18

module MF_stratixiii_pll (inclk,
                    fbin,
                    fbout,
                    clkswitch,
                    areset,
                    pfdena,
                    scanclk,
                    scandata,
                    scanclkena,
                    configupdate,
                    clk,
                    phasecounterselect,
                    phaseupdown,
                    phasestep,
                    clkbad,
                    activeclock,
                    locked,
                    scandataout,
                    scandone,
                    phasedone,
                    vcooverrange,
                    vcounderrange
                    );

    parameter operation_mode                       = "normal";
    parameter pll_type                             = "auto"; // auto,fast(left_right),enhanced(top_bottom)
    parameter compensate_clock                     = "clock0";


    parameter inclk0_input_frequency               = 0;
    parameter inclk1_input_frequency               = 0;

    parameter self_reset_on_loss_lock        = "off";
    parameter switch_over_type                     = "auto";

    parameter switch_over_counter                  = 1;
    parameter enable_switch_over_counter           = "off";
    parameter dpa_multiply_by = 0;
    parameter dpa_divide_by = 0;
    parameter dpa_divider = 0;       // 0, 1, 2, 4

    parameter bandwidth                            = 0;
    parameter bandwidth_type                       = "auto";
    parameter use_dc_coupling                      = "false";

    parameter lock_high = 0; // 0 .. 4095
    parameter lock_low = 0;  // 0 .. 7
    parameter lock_window_ui = "0.05"; // "0.05", "0.1", "0.15", "0.2"
    parameter test_bypass_lock_detect              = "off";
    
    parameter clk0_output_frequency                = 0;
    parameter clk0_multiply_by                     = 0;
    parameter clk0_divide_by                       = 0;
    parameter clk0_phase_shift                     = "0";
    parameter clk0_duty_cycle                      = 50;

    parameter clk1_output_frequency                = 0;
    parameter clk1_multiply_by                     = 0;
    parameter clk1_divide_by                       = 0;
    parameter clk1_phase_shift                     = "0";
    parameter clk1_duty_cycle                      = 50;

    parameter clk2_output_frequency                = 0;
    parameter clk2_multiply_by                     = 0;
    parameter clk2_divide_by                       = 0;
    parameter clk2_phase_shift                     = "0";
    parameter clk2_duty_cycle                      = 50;

    parameter clk3_output_frequency                = 0;
    parameter clk3_multiply_by                     = 0;
    parameter clk3_divide_by                       = 0;
    parameter clk3_phase_shift                     = "0";
    parameter clk3_duty_cycle                      = 50;

    parameter clk4_output_frequency                = 0;
    parameter clk4_multiply_by                     = 0;
    parameter clk4_divide_by                       = 0;
    parameter clk4_phase_shift                     = "0";
    parameter clk4_duty_cycle                      = 50;

    parameter clk5_output_frequency                = 0;
    parameter clk5_multiply_by                     = 0;
    parameter clk5_divide_by                       = 0;
    parameter clk5_phase_shift                     = "0";
    parameter clk5_duty_cycle                      = 50;
    
    parameter clk6_output_frequency                = 0;
    parameter clk6_multiply_by                     = 0;
    parameter clk6_divide_by                       = 0;
    parameter clk6_phase_shift                     = "0";
    parameter clk6_duty_cycle                      = 50;
    
    parameter clk7_output_frequency                = 0;
    parameter clk7_multiply_by                     = 0;
    parameter clk7_divide_by                       = 0;
    parameter clk7_phase_shift                     = "0";
    parameter clk7_duty_cycle                      = 50;
    
    parameter clk8_output_frequency                = 0;
    parameter clk8_multiply_by                     = 0;
    parameter clk8_divide_by                       = 0;
    parameter clk8_phase_shift                     = "0";
    parameter clk8_duty_cycle                      = 50;
    
    parameter clk9_output_frequency                = 0;
    parameter clk9_multiply_by                     = 0;
    parameter clk9_divide_by                       = 0;
    parameter clk9_phase_shift                     = "0";
    parameter clk9_duty_cycle                      = 50;
    

    parameter pfd_min                              = 0;
    parameter pfd_max                              = 0;
    parameter vco_min                              = 0;
    parameter vco_max                              = 0;
    parameter vco_center                           = 0;

    // ADVANCED USE PARAMETERS
    parameter m_initial = 1;
    parameter m = 0;
    parameter n = 1;

    parameter c0_high = 1;
    parameter c0_low = 1;
    parameter c0_initial = 1;
    parameter c0_mode = "bypass";
    parameter c0_ph = 0;

    parameter c1_high = 1;
    parameter c1_low = 1;
    parameter c1_initial = 1;
    parameter c1_mode = "bypass";
    parameter c1_ph = 0;

    parameter c2_high = 1;
    parameter c2_low = 1;
    parameter c2_initial = 1;
    parameter c2_mode = "bypass";
    parameter c2_ph = 0;

    parameter c3_high = 1;
    parameter c3_low = 1;
    parameter c3_initial = 1;
    parameter c3_mode = "bypass";
    parameter c3_ph = 0;

    parameter c4_high = 1;
    parameter c4_low = 1;
    parameter c4_initial = 1;
    parameter c4_mode = "bypass";
    parameter c4_ph = 0;

    parameter c5_high = 1;
    parameter c5_low = 1;
    parameter c5_initial = 1;
    parameter c5_mode = "bypass";
    parameter c5_ph = 0;
    
    parameter c6_high = 1;
    parameter c6_low = 1;
    parameter c6_initial = 1;
    parameter c6_mode = "bypass";
    parameter c6_ph = 0;
    
    parameter c7_high = 1;
    parameter c7_low = 1;
    parameter c7_initial = 1;
    parameter c7_mode = "bypass";
    parameter c7_ph = 0;
    
    parameter c8_high = 1;
    parameter c8_low = 1;
    parameter c8_initial = 1;
    parameter c8_mode = "bypass";
    parameter c8_ph = 0;
    
    parameter c9_high = 1;
    parameter c9_low = 1;
    parameter c9_initial = 1;
    parameter c9_mode = "bypass";
    parameter c9_ph = 0;
    

    parameter m_ph = 0;

    parameter clk0_counter = "unused";
    parameter clk1_counter = "unused";
    parameter clk2_counter = "unused";
    parameter clk3_counter = "unused";
    parameter clk4_counter = "unused";
    parameter clk5_counter = "unused";
    parameter clk6_counter = "unused";
    parameter clk7_counter = "unused";
    parameter clk8_counter = "unused";
    parameter clk9_counter = "unused";

    parameter c1_use_casc_in = "off";
    parameter c2_use_casc_in = "off";
    parameter c3_use_casc_in = "off";
    parameter c4_use_casc_in = "off";
    parameter c5_use_casc_in = "off";
    parameter c6_use_casc_in = "off";
    parameter c7_use_casc_in = "off";
    parameter c8_use_casc_in = "off";
    parameter c9_use_casc_in = "off";

    parameter m_test_source  = -1;
    parameter c0_test_source = -1;
    parameter c1_test_source = -1;
    parameter c2_test_source = -1;
    parameter c3_test_source = -1;
    parameter c4_test_source = -1;
    parameter c5_test_source = -1;
    parameter c6_test_source = -1;
    parameter c7_test_source = -1;
    parameter c8_test_source = -1;
    parameter c9_test_source = -1;

    parameter vco_multiply_by = 0;
    parameter vco_divide_by = 0;
    parameter vco_post_scale = 1; // 1 .. 2
    parameter vco_frequency_control = "auto";
    parameter vco_phase_shift_step = 0;
    
    parameter charge_pump_current = 10;
    parameter loop_filter_r = "1.0";    // "1.0", "2.0", "4.0", "6.0", "8.0", "12.0", "16.0", "20.0"
    parameter loop_filter_c = 0;        // 0 , 2 , 4

    parameter pll_compensation_delay = 0;
    parameter simulation_type = "functional";

// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter down_spread                          = "0.0";
    parameter lock_c = 4;

    parameter sim_gate_lock_device_behavior        = "off";

    parameter clk0_phase_shift_num = 0;
    parameter clk1_phase_shift_num = 0;
    parameter clk2_phase_shift_num = 0;
    parameter clk3_phase_shift_num = 0;
    parameter clk4_phase_shift_num = 0;
    parameter family_name = "StratixIII";

    parameter clk0_use_even_counter_mode = "off";
    parameter clk1_use_even_counter_mode = "off";
    parameter clk2_use_even_counter_mode = "off";
    parameter clk3_use_even_counter_mode = "off";
    parameter clk4_use_even_counter_mode = "off";
    parameter clk5_use_even_counter_mode = "off";
    parameter clk6_use_even_counter_mode = "off";
    parameter clk7_use_even_counter_mode = "off";
    parameter clk8_use_even_counter_mode = "off";
    parameter clk9_use_even_counter_mode = "off";

    parameter clk0_use_even_counter_value = "off";
    parameter clk1_use_even_counter_value = "off";
    parameter clk2_use_even_counter_value = "off";
    parameter clk3_use_even_counter_value = "off";
    parameter clk4_use_even_counter_value = "off";
    parameter clk5_use_even_counter_value = "off";
    parameter clk6_use_even_counter_value = "off";
    parameter clk7_use_even_counter_value = "off";
    parameter clk8_use_even_counter_value = "off";
    parameter clk9_use_even_counter_value = "off";

    // TEST ONLY
    
    parameter init_block_reset_a_count = 1;
    parameter init_block_reset_b_count = 1;

// SIMULATION_ONLY_PARAMETERS_END
    
// LOCAL_PARAMETERS_BEGIN

    parameter phase_counter_select_width = 4;
    parameter lock_window = 5;
    parameter inclk0_freq = inclk0_input_frequency;
    parameter inclk1_freq = inclk1_input_frequency;
   
parameter charge_pump_current_bits = 0;
parameter lock_window_ui_bits = 0;
parameter loop_filter_c_bits = 0;
parameter loop_filter_r_bits = 0;
parameter test_counter_c0_delay_chain_bits = 0;
parameter test_counter_c1_delay_chain_bits = 0;
parameter test_counter_c2_delay_chain_bits = 0;
parameter test_counter_c3_delay_chain_bits = 0;
parameter test_counter_c4_delay_chain_bits = 0;
parameter test_counter_c5_delay_chain_bits = 0;
    parameter test_counter_c6_delay_chain_bits = 0;
    parameter test_counter_c7_delay_chain_bits = 0;
    parameter test_counter_c8_delay_chain_bits = 0;
    parameter test_counter_c9_delay_chain_bits = 0;
parameter test_counter_m_delay_chain_bits = 0;
parameter test_counter_n_delay_chain_bits = 0;
parameter test_feedback_comp_delay_chain_bits = 0;
parameter test_input_comp_delay_chain_bits = 0;
parameter test_volt_reg_output_mode_bits = 0;
parameter test_volt_reg_output_voltage_bits = 0;
parameter test_volt_reg_test_mode = "false";
parameter vco_range_detector_high_bits = -1;
parameter vco_range_detector_low_bits = -1;
parameter scan_chain_mif_file = ""; 

    parameter test_counter_c3_sclk_delay_chain_bits  = -1;
    parameter test_counter_c4_sclk_delay_chain_bits  = -1;
    parameter test_counter_c5_lden_delay_chain_bits  = -1;
    parameter test_counter_c6_lden_delay_chain_bits  = -1;

parameter auto_settings = "true";

// LOCAL_PARAMETERS_END
 
    // INPUT PORTS
    input [1:0] inclk;
    input fbin;
    input clkswitch;
    input areset;
    input pfdena;
    input [phase_counter_select_width - 1:0] phasecounterselect;
    input phaseupdown;
    input phasestep;
    input scanclk;
    input scanclkena;
    input scandata;
    input configupdate;

    // OUTPUT PORTS
    output [9:0] clk;
    output [1:0] clkbad;
    output activeclock;
    output locked;
    output scandataout;
    output scandone;
    output fbout;
    output phasedone;
    output vcooverrange;
    output vcounderrange;
    
        

    // INTERNAL VARIABLES AND NETS
    reg [8*6:1] clk_num[0:9];
    integer scan_chain_length;
    integer i;
    integer j;
    integer k;
    integer x;
    integer y;
    integer l_index;
    integer gate_count;
    integer egpp_offset;
    integer sched_time;
    integer delay_chain;
    integer low;
    integer high;
    integer initial_delay;
    integer fbk_phase;
    integer fbk_delay;
    integer phase_shift[0:7];
    integer last_phase_shift[0:7];

    integer m_times_vco_period;
    integer new_m_times_vco_period;
    integer refclk_period;
    integer fbclk_period;
    integer high_time;
    integer low_time;
    integer my_rem;
    integer tmp_rem;
    integer rem;
    integer tmp_vco_per;
    integer vco_per;
    integer offset;
    integer temp_offset;
    integer cycles_to_lock;
    integer cycles_to_unlock;
    integer loop_xplier;
    integer loop_initial;
    integer loop_ph;
    integer cycle_to_adjust;
    integer total_pull_back;
    integer pull_back_M;

    time    fbclk_time;
    time    first_fbclk_time;
    time    refclk_time;

    reg switch_clock;

    reg [31:0] real_lock_high;

    reg got_first_refclk;
    reg got_second_refclk;
    reg got_first_fbclk;
    reg refclk_last_value;
    reg fbclk_last_value;
    reg inclk_last_value;
    reg pll_is_locked;
    reg locked_tmp;
    reg areset_last_value;
    reg pfdena_last_value;
    reg inclk_out_of_range;
    reg schedule_vco_last_value;
    
    // Test bypass lock detect
    reg pfd_locked;
    integer cycles_pfd_low, cycles_pfd_high;

    reg gate_out;
    reg vco_val;

    reg [31:0] m_initial_val;
    reg [31:0] m_val[0:1];
    reg [31:0] n_val[0:1];
    reg [31:0] m_delay;
    reg [8*6:1] m_mode_val[0:1];
    reg [8*6:1] n_mode_val[0:1];

    reg [31:0] c_high_val[0:9];
    reg [31:0] c_low_val[0:9];
    reg [8*6:1] c_mode_val[0:9];
    reg [31:0] c_initial_val[0:9];
    integer c_ph_val[0:9];

    reg [31:0] c_val; // placeholder for c_high,c_low values

    // VCO Frequency Range control
    reg vco_over, vco_under;
   
    // temporary registers for reprogramming
    integer c_ph_val_tmp[0:9];
    reg [31:0] c_high_val_tmp[0:9];
    reg [31:0] c_hval[0:9];
    reg [31:0] c_low_val_tmp[0:9];
    reg [31:0] c_lval[0:9];
    reg [8*6:1] c_mode_val_tmp[0:9];

    // hold registers for reprogramming
    integer c_ph_val_hold[0:9];
    reg [31:0] c_high_val_hold[0:9];
    reg [31:0] c_low_val_hold[0:9];
    reg [8*6:1] c_mode_val_hold[0:9];

    // old values
    reg [31:0] m_val_old[0:1];
    reg [31:0] m_val_tmp[0:1];
    reg [31:0] n_val_old[0:1];
    reg [8*6:1] m_mode_val_old[0:1];
    reg [8*6:1] n_mode_val_old[0:1];
    reg [31:0] c_high_val_old[0:9];
    reg [31:0] c_low_val_old[0:9];
    reg [8*6:1] c_mode_val_old[0:9];
    integer c_ph_val_old[0:9];
    integer   m_ph_val_old;
    integer   m_ph_val_tmp;

    integer cp_curr_old;
    integer cp_curr_val;
    integer lfc_old;
    integer lfc_val;
    integer vco_cur;
    integer vco_old;
    reg [9*8:1] lfr_val;
    reg [9*8:1] lfr_old;
    reg [1:2] lfc_val_bit_setting, lfc_val_old_bit_setting;
    reg vco_val_bit_setting, vco_val_old_bit_setting;
    reg [3:7] lfr_val_bit_setting, lfr_val_old_bit_setting;
    reg [14:16] cp_curr_bit_setting, cp_curr_old_bit_setting;
    
    // Setting on  - display real values
    // Setting off - display only bits
    reg pll_reconfig_display_full_setting;

    reg [7:0] m_hi;
    reg [7:0] m_lo;
    reg [7:0] n_hi;
    reg [7:0] n_lo;

    // ph tap orig values (POF)
    integer c_ph_val_orig[0:9];
    integer m_ph_val_orig;

    reg schedule_vco;
    reg stop_vco;
    reg inclk_n;
    reg inclk_man;
    reg inclk_es;

    reg [7:0] vco_out;
    reg [7:0] vco_tap;
    reg [7:0] vco_out_last_value;
    reg [7:0] vco_tap_last_value;
    wire inclk_c0;
    wire inclk_c1;
    wire inclk_c2;
    wire inclk_c3;
    wire inclk_c4;
    wire inclk_c5;
    wire inclk_c6;
    wire inclk_c7;
    wire inclk_c8;
    wire inclk_c9;
    
    wire  inclk_c0_from_vco;
    wire  inclk_c1_from_vco;
    wire  inclk_c2_from_vco;
    wire  inclk_c3_from_vco;
    wire  inclk_c4_from_vco;
    wire  inclk_c5_from_vco;
    wire  inclk_c6_from_vco;
    wire  inclk_c7_from_vco;
    wire  inclk_c8_from_vco;
    wire  inclk_c9_from_vco;
    
    wire  inclk_m_from_vco;

    wire inclk_m;
    wire [9:0] clk_tmp, clk_out_pfd;


    wire [9:0] clk_out;

    wire c0_clk;
    wire c1_clk;
    wire c2_clk;
    wire c3_clk;
    wire c4_clk;
    wire c5_clk;
    wire c6_clk;
    wire c7_clk;
    wire c8_clk;
    wire c9_clk;

    reg first_schedule;

    reg vco_period_was_phase_adjusted;
    reg phase_adjust_was_scheduled;

    wire refclk;
    wire fbclk;
    
    wire pllena_reg;
    wire test_mode_inclk;
 
    // Self Reset
    wire reset_self;

    // Clock Switchover
    reg clk0_is_bad;
    reg clk1_is_bad;
    reg inclk0_last_value;
    reg inclk1_last_value;
    reg other_clock_value;
    reg other_clock_last_value;
    reg primary_clk_is_bad;
    reg current_clk_is_bad;
    reg external_switch;
    reg active_clock;
    reg got_curr_clk_falling_edge_after_clkswitch;

    integer clk0_count;
    integer clk1_count;
    integer switch_over_count;

    wire scandataout_tmp;
    reg scandata_in, scandata_out; // hold scan data in negative-edge triggered ff (on either side on chain)
    reg scandone_tmp;
    reg initiate_reconfig;
    integer quiet_time;
    integer slowest_clk_old;
    integer slowest_clk_new;

    reg reconfig_err;
    reg error;
    time    scanclk_last_rising_edge;
    time    scanread_active_edge;
    reg got_first_scanclk;
    reg got_first_gated_scanclk;
    reg gated_scanclk;
    integer scanclk_period;
    reg scanclk_last_value;
    wire update_conf_latches;
    reg  update_conf_latches_reg;
    reg [-1:232] scan_data;
    reg scanclkena_reg; // register scanclkena on negative edge of scanclk
    reg c0_rising_edge_transfer_done;
    reg c1_rising_edge_transfer_done;
    reg c2_rising_edge_transfer_done;
    reg c3_rising_edge_transfer_done;
    reg c4_rising_edge_transfer_done;
    reg c5_rising_edge_transfer_done;
    reg c6_rising_edge_transfer_done;
    reg c7_rising_edge_transfer_done;
    reg c8_rising_edge_transfer_done;
    reg c9_rising_edge_transfer_done;
    reg scanread_setup_violation;
    integer index;
    integer scanclk_cycles;
    reg d_msg;

    integer num_output_cntrs;
    reg no_warn;
    
    // Phase reconfig
    
    reg [3:0] phasecounterselect_reg;
    reg phaseupdown_reg;
    reg phasestep_reg;
    integer select_counter;
    integer phasestep_high_count;
    reg update_phase;
    

// LOCAL_PARAMETERS_BEGIN

    parameter SCAN_CHAIN = 144;
    parameter GPP_SCAN_CHAIN  = 234;
    parameter FAST_SCAN_CHAIN = 180;
    // primary clk is always inclk0
    parameter num_phase_taps = 8;

// LOCAL_PARAMETERS_END


    // internal variables for scaling of multiply_by and divide_by values
    integer i_clk0_mult_by;
    integer i_clk0_div_by;
    integer i_clk1_mult_by;
    integer i_clk1_div_by;
    integer i_clk2_mult_by;
    integer i_clk2_div_by;
    integer i_clk3_mult_by;
    integer i_clk3_div_by;
    integer i_clk4_mult_by;
    integer i_clk4_div_by;
    integer i_clk5_mult_by;
    integer i_clk5_div_by;
    integer i_clk6_mult_by;
    integer i_clk6_div_by;
    integer i_clk7_mult_by;
    integer i_clk7_div_by;
    integer i_clk8_mult_by;
    integer i_clk8_div_by;
    integer i_clk9_mult_by;
    integer i_clk9_div_by;
    integer max_d_value;
    integer new_multiplier;

    // internal variables for storing the phase shift number.(used in lvds mode only)
    integer i_clk0_phase_shift;
    integer i_clk1_phase_shift;
    integer i_clk2_phase_shift;
    integer i_clk3_phase_shift;
    integer i_clk4_phase_shift;

    // user to advanced internal signals

    integer   i_m_initial;
    integer   i_m;
    integer   i_n;
    integer   i_c_high[0:9];
    integer   i_c_low[0:9];
    integer   i_c_initial[0:9];
    integer   i_c_ph[0:9];
    reg       [8*6:1] i_c_mode[0:9];

    integer   i_vco_min;
    integer   i_vco_max;
    integer   i_vco_min_no_division;
    integer   i_vco_max_no_division;
    integer   i_vco_center;
    integer   i_pfd_min;
    integer   i_pfd_max;
    integer   i_m_ph;
    integer   m_ph_val;
    reg [8*2:1] i_clk9_counter;
    reg [8*2:1] i_clk8_counter;
    reg [8*2:1] i_clk7_counter;
    reg [8*2:1] i_clk6_counter;
    reg [8*2:1] i_clk5_counter;
    reg [8*2:1] i_clk4_counter;
    reg [8*2:1] i_clk3_counter;
    reg [8*2:1] i_clk2_counter;
    reg [8*2:1] i_clk1_counter;
    reg [8*2:1] i_clk0_counter;
    integer   i_charge_pump_current;
    integer   i_loop_filter_r;
    integer   max_neg_abs;
    integer   output_count;
    integer   new_divisor;

    integer loop_filter_c_arr[0:3];
    integer fpll_loop_filter_c_arr[0:3];
    integer charge_pump_curr_arr[0:15];

    reg pll_in_test_mode;
    reg pll_is_in_reset;
    reg pll_has_just_been_reconfigured;

    // uppercase to lowercase parameter values
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_operation_mode;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_pll_type;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_compensate_clock;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_scan_chain;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_switch_over_type;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_bandwidth_type;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_simulation_type;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_sim_gate_lock_device_behavior;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_vco_frequency_control;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_enable_switch_over_counter;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] l_self_reset_on_loss_lock;
    


    integer current_clock;
    integer current_clock_man;
    reg is_fast_pll;
    reg ic1_use_casc_in;
    reg ic2_use_casc_in;
    reg ic3_use_casc_in;
    reg ic4_use_casc_in;
    reg ic5_use_casc_in;
    reg ic6_use_casc_in;
    reg ic7_use_casc_in;
    reg ic8_use_casc_in;
    reg ic9_use_casc_in;

    reg init;
    reg tap0_is_active;

    real inclk0_period, last_inclk0_period,inclk1_period, last_inclk1_period;
    real last_inclk0_edge,last_inclk1_edge,diff_percent_period;
    reg first_inclk0_edge_detect,first_inclk1_edge_detect;



    // finds the closest integer fraction of a given pair of numerator and denominator. 
    task find_simple_integer_fraction;
        input numerator;
        input denominator;
        input max_denom;
        output fraction_num; 
        output fraction_div; 
        parameter max_iter = 20;
        
        integer numerator;
        integer denominator;
        integer max_denom;
        integer fraction_num; 
        integer fraction_div; 
        
        integer quotient_array[max_iter-1:0];
        integer int_loop_iter;
        integer int_quot;
        integer m_value;
        integer d_value;
        integer old_m_value;
        integer swap;

        integer loop_iter;
        integer num;
        integer den;
        integer i_max_iter;

    begin      
        loop_iter = 0;
        num = (numerator == 0) ? 1 : numerator;
        den = (denominator == 0) ? 1 : denominator;
        i_max_iter = max_iter;
       
        while (loop_iter < i_max_iter)
        begin
            int_quot = num / den;
            quotient_array[loop_iter] = int_quot;
            num = num - (den*int_quot);
            loop_iter=loop_iter+1;
            
            if ((num == 0) || (max_denom != -1) || (loop_iter == i_max_iter)) 
            begin
                // calculate the numerator and denominator if there is a restriction on the
                // max denom value or if the loop is ending
                m_value = 0;
                d_value = 1;
                // get the rounded value at this stage for the remaining fraction
                if (den != 0)
                begin
                    m_value = (2*num/den);
                end
                // calculate the fraction numerator and denominator at this stage
                for (int_loop_iter = loop_iter-1; int_loop_iter >= 0; int_loop_iter=int_loop_iter-1)
                begin
                    if (m_value == 0)
                    begin
                        m_value = quotient_array[int_loop_iter];
                        d_value = 1;
                    end
                    else
                    begin
                        old_m_value = m_value;
                        m_value = quotient_array[int_loop_iter]*m_value + d_value;
                        d_value = old_m_value;
                    end
                end
                // if the denominator is less than the maximum denom_value or if there is no restriction save it
                if ((d_value <= max_denom) || (max_denom == -1))
                begin
                    fraction_num = m_value;
                    fraction_div = d_value;
                end
                // end the loop if the denomitor has overflown or the numerator is zero (no remainder during this round)
                if (((d_value > max_denom) && (max_denom != -1)) || (num == 0))
                begin
                    i_max_iter = loop_iter;
                end
            end
            // swap the numerator and denominator for the next round
            swap = den;
            den = num;
            num = swap;
        end
    end
    endtask // find_simple_integer_fraction

    // get the absolute value
    function integer abs;
    input value;
    integer value;
    begin
        if (value < 0)
            abs = value * -1;
        else abs = value;
    end
    endfunction

    // find twice the period of the slowest clock
    function integer slowest_clk;
    input C0, C0_mode, C1, C1_mode, C2, C2_mode, C3, C3_mode, C4, C4_mode, C5, C5_mode, C6, C6_mode, C7, C7_mode, C8, C8_mode, C9, C9_mode, refclk, m_mod;
    integer C0, C1, C2, C3, C4, C5, C6, C7, C8, C9;
    reg [8*6:1] C0_mode, C1_mode, C2_mode, C3_mode, C4_mode, C5_mode, C6_mode, C7_mode, C8_mode, C9_mode;
    integer refclk;
    reg [31:0] m_mod;
    integer max_modulus;
    begin
        max_modulus = 1;
        if (C0_mode != "bypass" && C0_mode != "   off")
            max_modulus = C0;
        if (C1 > max_modulus && C1_mode != "bypass" && C1_mode != "   off")
            max_modulus = C1;
        if (C2 > max_modulus && C2_mode != "bypass" && C2_mode != "   off")
            max_modulus = C2;
        if (C3 > max_modulus && C3_mode != "bypass" && C3_mode != "   off")
            max_modulus = C3;
        if (C4 > max_modulus && C4_mode != "bypass" && C4_mode != "   off")
            max_modulus = C4;
        if (C5 > max_modulus && C5_mode != "bypass" && C5_mode != "   off")
            max_modulus = C5;
        if (C6 > max_modulus && C6_mode != "bypass" && C6_mode != "   off")
            max_modulus = C6;
        if (C7 > max_modulus && C7_mode != "bypass" && C7_mode != "   off")
            max_modulus = C7;
        if (C8 > max_modulus && C8_mode != "bypass" && C8_mode != "   off")
            max_modulus = C8;
        if (C9 > max_modulus && C9_mode != "bypass" && C9_mode != "   off")
            max_modulus = C9;

        slowest_clk = (refclk * max_modulus *2 / m_mod);
    end
    endfunction

    // count the number of digits in the given integer
    function integer count_digit;
    input X;
    integer X;
    integer count, result;
    begin
        count = 0;
        result = X;
        while (result != 0)
        begin
            result = (result / 10);
            count = count + 1;
        end
        
        count_digit = count;
    end
    endfunction

    // reduce the given huge number(X) to Y significant digits
    function integer scale_num;
    input X, Y;
    integer X, Y;
    integer count;
    integer fac_ten, lc;
    begin
        fac_ten = 1;
        count = count_digit(X);
        
        for (lc = 0; lc < (count-Y); lc = lc + 1)
            fac_ten = fac_ten * 10;

        scale_num = (X / fac_ten);
    end
    endfunction

    // find the greatest common denominator of X and Y
    function integer gcd;
    input X,Y;
    integer X,Y;
    integer L, S, R, G;
    begin
        if (X < Y) // find which is smaller.
        begin
            S = X;
            L = Y;
        end
        else
        begin
            S = Y;
            L = X;
        end

        R = S;
        while ( R > 1)
        begin
            S = L;
            L = R;
            R = S % L;  // divide bigger number by smaller.
                        // remainder becomes smaller number.
        end
        if (R == 0)     // if evenly divisible then L is gcd else it is 1.
            G = L;
        else
            G = R;
        gcd = G;
    end
    endfunction

    // find the least common multiple of A1 to A10
    function integer lcm;
    input A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer M1, M2, M3, M4, M5 , M6, M7, M8, M9, R;
    begin
        M1 = (A1 * A2)/gcd(A1, A2);
        M2 = (M1 * A3)/gcd(M1, A3);
        M3 = (M2 * A4)/gcd(M2, A4);
        M4 = (M3 * A5)/gcd(M3, A5);
        M5 = (M4 * A6)/gcd(M4, A6);
        M6 = (M5 * A7)/gcd(M5, A7);
        M7 = (M6 * A8)/gcd(M6, A8);
        M8 = (M7 * A9)/gcd(M7, A9);
        M9 = (M8 * A10)/gcd(M8, A10);
        if (M9 < 3)
            R = 10;
        else if ((M9 <= 10) && (M9 >= 3))
            R = 4 * M9;
        else if (M9 > 1000)
            R = scale_num(M9, 3);
        else
            R = M9;
        lcm = R; 
    end
    endfunction

    // find the M and N values for Manual phase based on the following 5 criterias:
    // 1. The PFD frequency (i.e. Fin / N) must be in the range 5 MHz to 720 MHz
    // 2. The VCO frequency (i.e. Fin * M / N) must be in the range 300 MHz to 1300 MHz
    // 3. M is less than 512
    // 4. N is less than 512
    // 5. It's the smallest M/N which satisfies all the above constraints, and is within 2ps
    //    of the desired vco-phase-shift-step
    task find_m_and_n_4_manual_phase;
        input inclock_period;
        input vco_phase_shift_step;
        input clk0_mult, clk1_mult, clk2_mult, clk3_mult, clk4_mult;
        input clk5_mult, clk6_mult, clk7_mult, clk8_mult, clk9_mult;
        input clk0_div,  clk1_div,  clk2_div,  clk3_div,  clk4_div;
        input clk5_div,  clk6_div,  clk7_div,  clk8_div,  clk9_div;
        input clk0_used,  clk1_used,  clk2_used,  clk3_used,  clk4_used;
        input clk5_used,  clk6_used,  clk7_used,  clk8_used,  clk9_used;
        output m; 
        output n; 

        parameter max_m = 511;
        parameter max_n = 511;
        parameter max_pfd = 720;
        parameter min_pfd = 5;
        parameter max_vco = 1600; // max vco frequency. (in mHz)
        parameter min_vco = 300;  // min vco frequency. (in mHz)
        parameter max_offset = 0.004;
        
        reg[160:1] clk0_used,  clk1_used,  clk2_used,  clk3_used,  clk4_used;
        reg[160:1] clk5_used,  clk6_used,  clk7_used,  clk8_used,  clk9_used;
        
        integer inclock_period;
        integer vco_phase_shift_step;
        integer clk0_mult, clk1_mult, clk2_mult, clk3_mult, clk4_mult;
        integer clk5_mult, clk6_mult, clk7_mult, clk8_mult, clk9_mult;
        integer clk0_div,  clk1_div,  clk2_div,  clk3_div,  clk4_div;
        integer clk5_div,  clk6_div,  clk7_div,  clk8_div,  clk9_div;
        integer m; 
        integer n;
        integer pre_m;
        integer pre_n;
        integer m_out;
        integer n_out;
        integer closest_vco_step_value;
        
        integer vco_period;
        integer pfd_freq;
        integer vco_freq;
        integer vco_ps_step_value;
        real    clk0_div_factor_real;
        real    clk1_div_factor_real;
        real    clk2_div_factor_real;
        real    clk3_div_factor_real;
        real    clk4_div_factor_real;
        real    clk5_div_factor_real;
        real    clk6_div_factor_real;
        real    clk7_div_factor_real;
        real    clk8_div_factor_real;
        real    clk9_div_factor_real;
        real    clk0_div_factor_diff;
        real    clk1_div_factor_diff;
        real    clk2_div_factor_diff;
        real    clk3_div_factor_diff;
        real    clk4_div_factor_diff;
        real    clk5_div_factor_diff;
        real    clk6_div_factor_diff;
        real    clk7_div_factor_diff;
        real    clk8_div_factor_diff;
        real    clk9_div_factor_diff;
        integer clk0_div_factor_int;
        integer clk1_div_factor_int;
        integer clk2_div_factor_int;
        integer clk3_div_factor_int;
        integer clk4_div_factor_int;
        integer clk5_div_factor_int;
        integer clk6_div_factor_int;
        integer clk7_div_factor_int;
        integer clk8_div_factor_int;
        integer clk9_div_factor_int;
    begin

        vco_period = vco_phase_shift_step * 8;

        pre_m = 0;
        pre_n = 0;
        closest_vco_step_value = 0;

        begin : LOOP_1
                for (n_out = 1; n_out < max_n; n_out = n_out +1)
                begin
                    for (m_out = 1; m_out < max_m; m_out = m_out +1)
                    begin
                        clk0_div_factor_real = (clk0_div * m_out * 1.0 ) / (clk0_mult * n_out);
                        clk1_div_factor_real = (clk1_div * m_out * 1.0) / (clk1_mult * n_out);
                        clk2_div_factor_real = (clk2_div * m_out * 1.0) / (clk2_mult * n_out);
                        clk3_div_factor_real = (clk3_div * m_out * 1.0) / (clk3_mult * n_out);
                        clk4_div_factor_real = (clk4_div * m_out * 1.0) / (clk4_mult * n_out);
                        clk5_div_factor_real = (clk5_div * m_out * 1.0) / (clk5_mult * n_out);
                        clk6_div_factor_real = (clk6_div * m_out * 1.0) / (clk6_mult * n_out);
                        clk7_div_factor_real = (clk7_div * m_out * 1.0) / (clk7_mult * n_out);
                        clk8_div_factor_real = (clk8_div * m_out * 1.0) / (clk8_mult * n_out);
                        clk9_div_factor_real = (clk9_div * m_out * 1.0) / (clk9_mult * n_out);
        
                        clk0_div_factor_int = clk0_div_factor_real;
                        clk1_div_factor_int = clk1_div_factor_real;
                        clk2_div_factor_int = clk2_div_factor_real;
                        clk3_div_factor_int = clk3_div_factor_real;
                        clk4_div_factor_int = clk4_div_factor_real;
                        clk5_div_factor_int = clk5_div_factor_real;
                        clk6_div_factor_int = clk6_div_factor_real;
                        clk7_div_factor_int = clk7_div_factor_real;
                        clk8_div_factor_int = clk8_div_factor_real;
                        clk9_div_factor_int = clk9_div_factor_real;
                        
                        clk0_div_factor_diff = (clk0_div_factor_real - clk0_div_factor_int < 0) ? (clk0_div_factor_real - clk0_div_factor_int) * -1.0 : clk0_div_factor_real - clk0_div_factor_int;
                        clk1_div_factor_diff = (clk1_div_factor_real - clk1_div_factor_int < 0) ? (clk1_div_factor_real - clk1_div_factor_int) * -1.0 : clk1_div_factor_real - clk1_div_factor_int;
                        clk2_div_factor_diff = (clk2_div_factor_real - clk2_div_factor_int < 0) ? (clk2_div_factor_real - clk2_div_factor_int) * -1.0 : clk2_div_factor_real - clk2_div_factor_int;
                        clk3_div_factor_diff = (clk3_div_factor_real - clk3_div_factor_int < 0) ? (clk3_div_factor_real - clk3_div_factor_int) * -1.0 : clk3_div_factor_real - clk3_div_factor_int;
                        clk4_div_factor_diff = (clk4_div_factor_real - clk4_div_factor_int < 0) ? (clk4_div_factor_real - clk4_div_factor_int) * -1.0 : clk4_div_factor_real - clk4_div_factor_int;
                        clk5_div_factor_diff = (clk5_div_factor_real - clk5_div_factor_int < 0) ? (clk5_div_factor_real - clk5_div_factor_int) * -1.0 : clk5_div_factor_real - clk5_div_factor_int;
                        clk6_div_factor_diff = (clk6_div_factor_real - clk6_div_factor_int < 0) ? (clk6_div_factor_real - clk6_div_factor_int) * -1.0 : clk6_div_factor_real - clk6_div_factor_int;
                        clk7_div_factor_diff = (clk7_div_factor_real - clk7_div_factor_int < 0) ? (clk7_div_factor_real - clk7_div_factor_int) * -1.0 : clk7_div_factor_real - clk7_div_factor_int;
                        clk8_div_factor_diff = (clk8_div_factor_real - clk8_div_factor_int < 0) ? (clk8_div_factor_real - clk8_div_factor_int) * -1.0 : clk8_div_factor_real - clk8_div_factor_int;
                        clk9_div_factor_diff = (clk9_div_factor_real - clk9_div_factor_int < 0) ? (clk9_div_factor_real - clk9_div_factor_int) * -1.0 : clk9_div_factor_real - clk9_div_factor_int;
                        
        
                        if (((clk0_div_factor_diff < max_offset) || (clk0_used == "unused")) &&
                            ((clk1_div_factor_diff < max_offset) || (clk1_used == "unused")) &&
                            ((clk2_div_factor_diff < max_offset) || (clk2_used == "unused")) &&
                            ((clk3_div_factor_diff < max_offset) || (clk3_used == "unused")) &&
                            ((clk4_div_factor_diff < max_offset) || (clk4_used == "unused")) &&
                            ((clk5_div_factor_diff < max_offset) || (clk5_used == "unused")) &&
                            ((clk6_div_factor_diff < max_offset) || (clk6_used == "unused")) &&
                            ((clk7_div_factor_diff < max_offset) || (clk7_used == "unused")) &&
                            ((clk8_div_factor_diff < max_offset) || (clk8_used == "unused")) &&
                            ((clk9_div_factor_diff < max_offset) || (clk9_used == "unused")) )
                        begin                
                            if ((m_out != 0) && (n_out != 0))
                            begin
                                pfd_freq = 1000000 / (inclock_period * n_out);
                                vco_freq = (1000000 * m_out) / (inclock_period * n_out);
                                vco_ps_step_value = (inclock_period * n_out) / (8 * m_out);
                
                                if ( (m_out < max_m) && (n_out < max_n) && (pfd_freq >= min_pfd) && (pfd_freq <= max_pfd) &&
                                    (vco_freq >= min_vco) && (vco_freq <= max_vco) )
                                begin
                                    if (abs(vco_ps_step_value - vco_phase_shift_step) <= 2)
                                    begin
                                        pre_m = m_out;
                                        pre_n = n_out;
                                        disable LOOP_1;
                                    end
                                    else
                                    begin
                                        if ((closest_vco_step_value == 0) || (abs(vco_ps_step_value - vco_phase_shift_step) < abs(closest_vco_step_value - vco_phase_shift_step)))
                                        begin
                                            pre_m = m_out;
                                            pre_n = n_out;
                                            closest_vco_step_value = vco_ps_step_value;
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
        end
        
        if ((pre_m != 0) && (pre_n != 0))
        begin
            find_simple_integer_fraction(pre_m, pre_n,
                        max_n, m, n);
        end
        else
        begin
            n = 1;
            m = lcm  (clk0_mult, clk1_mult, clk2_mult, clk3_mult,
                    clk4_mult, clk5_mult, clk6_mult,
                    clk7_mult, clk8_mult, clk9_mult, inclock_period);           
        end
    end
    endtask // find_m_and_n_4_manual_phase

    // find the factor of division of the output clock frequency
    // compared to the VCO
    function integer output_counter_value;
    input clk_divide, clk_mult, M, N;
    integer clk_divide, clk_mult, M, N;
    real r;
    integer r_int;
    begin
        r = (clk_divide * M * 1.0)/(clk_mult * N);
        r_int = r;
        output_counter_value = r_int;
    end
    endfunction

    // find the mode of each of the PLL counters - bypass, even or odd
    function [8*6:1] counter_mode;
    input duty_cycle;
    input output_counter_value;
    integer duty_cycle;
    integer output_counter_value;
    integer half_cycle_high;
    reg [8*6:1] R;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        if (output_counter_value == 1)
            R = "bypass";
        else if ((half_cycle_high % 2) == 0)
            R = "  even";
        else
            R = "   odd";
        counter_mode = R;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock high
    function integer counter_high;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle;
    integer half_cycle_high;
    integer tmp_counter_high;
    integer mode;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_high = tmp_counter_high + !mode;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock low
    function integer counter_low;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle, counter_h;
    integer half_cycle_high;
    integer mode;
    integer tmp_counter_high;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_h = tmp_counter_high + !mode;
        counter_low =  output_counter_value - counter_h;
    end
    endfunction

    // find the smallest time delay amongst t1 to t10
    function integer mintimedelay;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2)
            m1 = t1;
        else
            m1 = t2;
        if (m1 < t3)
            m2 = m1;
        else
            m2 = t3;
        if (m2 < t4)
            m3 = m2;
        else
            m3 = t4;
        if (m3 < t5)
            m4 = m3;
        else
            m4 = t5;
        if (m4 < t6)
            m5 = m4;
        else
            m5 = t6;
        if (m5 < t7)
            m6 = m5;
        else
            m6 = t7;
        if (m6 < t8)
            m7 = m6;
        else
            m7 = t8;
        if (m7 < t9)
            m8 = m7;
        else
            m8 = t9;
        if (m8 < t10)
            m9 = m8;
        else
            m9 = t10;
        if (m9 > 0)
            mintimedelay = m9;
        else
            mintimedelay = 0;
    end
    endfunction

    // find the numerically largest negative number, and return its absolute value
    function integer maxnegabs;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2) m1 = t1; else m1 = t2;
        if (m1 < t3) m2 = m1; else m2 = t3;
        if (m2 < t4) m3 = m2; else m3 = t4;
        if (m3 < t5) m4 = m3; else m4 = t5;
        if (m4 < t6) m5 = m4; else m5 = t6;
        if (m5 < t7) m6 = m5; else m6 = t7;
        if (m6 < t8) m7 = m6; else m7 = t8;
        if (m7 < t9) m8 = m7; else m8 = t9;
        if (m8 < t10) m9 = m8; else m9 = t10;
        maxnegabs = (m9 < 0) ? 0 - m9 : 0;
    end
    endfunction

    // adjust the given tap_phase by adding the largest negative number (ph_base) 
    function integer ph_adjust;
    input tap_phase, ph_base;
    integer tap_phase, ph_base;
    begin
        ph_adjust = tap_phase + ph_base;
    end
    endfunction

    // find the number of VCO clock cycles to wait initially before the first 
    // rising edge of the output clock
    function integer counter_initial;
    input tap_phase, m, n;
    integer tap_phase, m, n, phase;
    begin
        if (tap_phase < 0) tap_phase = 0 - tap_phase;
        // adding 0.5 for rounding correction (required in order to round
        // to the nearest integer instead of truncating)
        phase = ((tap_phase * m) / (360.0 * n)) + 0.6;
        counter_initial = phase;
    end
    endfunction

    // find which VCO phase tap to align the rising edge of the output clock to
    function integer counter_ph;
    input tap_phase;
    input m,n;
    integer m,n, phase;
    integer tap_phase;
    begin
    // adding 0.5 for rounding correction
        phase = (tap_phase * m / n) + 0.5;
        counter_ph = (phase % 360) / 45.0;

        if (counter_ph == 8)
            counter_ph = 0;
    end
    endfunction

    // convert the given string to length 6 by padding with spaces
    function [8*6:1] translate_string;
    input [8*6:1] mode;
    reg [8*6:1] new_mode;
    begin
        if (mode == "bypass")
            new_mode = "bypass";
        else if (mode == "even")
            new_mode = "  even";
        else if (mode == "odd")
            new_mode = "   odd";

        translate_string = new_mode;
    end
    endfunction

    // convert string to integer with sign
    function integer str2int; 
    input [8*16:1] s;

    reg [8*16:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    integer m, magnitude;
    integer sign;

    begin
        sign = 1;
        magnitude = 0;
        reg_s = s;
        for (m=1; m<=16; m=m+1)
        begin
            tmp = reg_s[128:121];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            // Accumulate ascii digits 0-9 only.
            if ((tmp>=48) && (tmp<=57)) 
                magnitude = (magnitude * 10) + digit;
            if (tmp == 45)
                sign = -1;  // Found a '-' character, i.e. number is negative.
        end
        str2int = sign*magnitude;
    end
    endfunction

    // this is for stratixiii lvds only
    // convert phase delay to integer
    function integer get_int_phase_shift; 
    input [8*16:1] s;
    input i_phase_shift;
    integer i_phase_shift;

    begin
        if (i_phase_shift != 0)
        begin                   
            get_int_phase_shift = i_phase_shift;
        end       
        else
        begin
            get_int_phase_shift = str2int(s);
        end        
    end
    endfunction

    // calculate the given phase shift (in ps) in terms of degrees
    function integer get_phase_degree; 
    input phase_shift;
    integer phase_shift, result;
    begin
        result = (phase_shift * 360) / inclk0_freq;
        // this is to round up the calculation result
        if ( result > 0 )
            result = result + 1;
        else if ( result < 0 )
            result = result - 1;
        else
            result = 0;

        // assign the rounded up result
        get_phase_degree = result;
    end
    endfunction

    // convert uppercase parameter values to lowercase
    // assumes that the maximum character length of a parameter is 18
    function [8*`STXIII_PLL_WORD_LENGTH:1] alpha_tolower;
    input [8*`STXIII_PLL_WORD_LENGTH:1] given_string;

    reg [8*`STXIII_PLL_WORD_LENGTH:1] return_string;
    reg [8*`STXIII_PLL_WORD_LENGTH:1] reg_string;
    reg [8:1] tmp;
    reg [8:1] conv_char;
    integer byte_count;
    begin
        return_string = "                    "; // initialise strings to spaces
        conv_char = "        ";
        reg_string = given_string;
        for (byte_count = `STXIII_PLL_WORD_LENGTH; byte_count >= 1; byte_count = byte_count - 1)
        begin
            tmp = reg_string[8*`STXIII_PLL_WORD_LENGTH:(8*(`STXIII_PLL_WORD_LENGTH-1)+1)];
            reg_string = reg_string << 8;
            if ((tmp >= 65) && (tmp <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
            begin
                conv_char = tmp + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
                return_string = {return_string, conv_char};
            end
            else
                return_string = {return_string, tmp};
        end
    
        alpha_tolower = return_string;
    end
    endfunction

    function integer display_msg;
    input [8*2:1] cntr_name;
    input msg_code;
    integer msg_code;
    begin
        if (msg_code == 1)
            $display ("Warning : %s counter switched from BYPASS mode to enabled. PLL may lose lock.", cntr_name);
        else if (msg_code == 2)
            $display ("Warning : Illegal 1 value for %s counter. Instead, the %s counter should be BYPASSED. Reconfiguration may not work.", cntr_name, cntr_name);
        else if (msg_code == 3)
            $display ("Warning : Illegal value for counter %s in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.", cntr_name);
        else if (msg_code == 4)
            $display ("Warning : %s counter switched from enabled to BYPASS mode. PLL may lose lock.", cntr_name);
        $display ("Time: %0t  Instance: %m", $time);
        display_msg = 1;
    end
    endfunction

    initial
    begin
        scandata_out = 1'b0;
        first_inclk0_edge_detect = 1'b0;
        first_inclk1_edge_detect = 1'b0;
        pll_reconfig_display_full_setting = 1'b0;
        initiate_reconfig = 1'b0;
    switch_over_count = 0;
        // convert string parameter values from uppercase to lowercase,
        // as expected in this model
        l_operation_mode             = alpha_tolower(operation_mode);
        l_pll_type                   = alpha_tolower(pll_type);
        l_compensate_clock           = alpha_tolower(compensate_clock);
        l_switch_over_type           = alpha_tolower(switch_over_type);
        l_bandwidth_type             = alpha_tolower(bandwidth_type);
        l_simulation_type            = alpha_tolower(simulation_type);
        l_sim_gate_lock_device_behavior = alpha_tolower(sim_gate_lock_device_behavior);
        l_vco_frequency_control      = alpha_tolower(vco_frequency_control);
        l_enable_switch_over_counter = alpha_tolower(enable_switch_over_counter);
        l_self_reset_on_loss_lock    = alpha_tolower(self_reset_on_loss_lock);
    
        real_lock_high = (l_sim_gate_lock_device_behavior == "on") ? lock_high : 0;    
        // initialize charge_pump_current, and loop_filter tables
        loop_filter_c_arr[0] = 0;
        loop_filter_c_arr[1] = 0;
        loop_filter_c_arr[2] = 0;
        loop_filter_c_arr[3] = 0;
        
        fpll_loop_filter_c_arr[0] = 0;
        fpll_loop_filter_c_arr[1] = 0;
        fpll_loop_filter_c_arr[2] = 0;
        fpll_loop_filter_c_arr[3] = 0;
        
        charge_pump_curr_arr[0] = 0;
        charge_pump_curr_arr[1] = 0;
        charge_pump_curr_arr[2] = 0;
        charge_pump_curr_arr[3] = 0;
        charge_pump_curr_arr[4] = 0;
        charge_pump_curr_arr[5] = 0;
        charge_pump_curr_arr[6] = 0;
        charge_pump_curr_arr[7] = 0;
        charge_pump_curr_arr[8] = 0;
        charge_pump_curr_arr[9] = 0;
        charge_pump_curr_arr[10] = 0;
        charge_pump_curr_arr[11] = 0;
        charge_pump_curr_arr[12] = 0;
        charge_pump_curr_arr[13] = 0;
        charge_pump_curr_arr[14] = 0;
        charge_pump_curr_arr[15] = 0;

        i_vco_max = vco_max;
        i_vco_min = vco_min; 

        if(vco_post_scale == 1)
        begin
            i_vco_max_no_division = vco_max * 2;
            i_vco_min_no_division = vco_min * 2;    
        end
        else
        begin
            i_vco_max_no_division = vco_max;
            i_vco_min_no_division = vco_min;    
        end


        if (m == 0)
        begin
            i_clk9_counter    = "c9";
            i_clk8_counter    = "c8";
            i_clk7_counter    = "c7";
            i_clk6_counter    = "c6";
            i_clk5_counter    = "c5" ;
            i_clk4_counter    = "c4" ;
            i_clk3_counter    = "c3" ;
            i_clk2_counter    = "c2" ;
            i_clk1_counter    = "c1" ;
            i_clk0_counter    = "c0" ;
        end
        else begin
            i_clk9_counter    = alpha_tolower(clk9_counter);
            i_clk8_counter    = alpha_tolower(clk8_counter);
            i_clk7_counter    = alpha_tolower(clk7_counter);
            i_clk6_counter    = alpha_tolower(clk6_counter);
            i_clk5_counter    = alpha_tolower(clk5_counter);
            i_clk4_counter    = alpha_tolower(clk4_counter);
            i_clk3_counter    = alpha_tolower(clk3_counter);
            i_clk2_counter    = alpha_tolower(clk2_counter);
            i_clk1_counter    = alpha_tolower(clk1_counter);
            i_clk0_counter    = alpha_tolower(clk0_counter);
        end

        if (m == 0)
        begin 

            // set the limit of the divide_by value that can be returned by
            // the following function.
            max_d_value = 500;
            
            // scale down the multiply_by and divide_by values provided by the design
            // before attempting to use them in the calculations below
            find_simple_integer_fraction(clk0_multiply_by, clk0_divide_by,
                            max_d_value, i_clk0_mult_by, i_clk0_div_by);
            find_simple_integer_fraction(clk1_multiply_by, clk1_divide_by,
                            max_d_value, i_clk1_mult_by, i_clk1_div_by);
            find_simple_integer_fraction(clk2_multiply_by, clk2_divide_by,
                            max_d_value, i_clk2_mult_by, i_clk2_div_by);
            find_simple_integer_fraction(clk3_multiply_by, clk3_divide_by,
                            max_d_value, i_clk3_mult_by, i_clk3_div_by);
            find_simple_integer_fraction(clk4_multiply_by, clk4_divide_by,
                            max_d_value, i_clk4_mult_by, i_clk4_div_by);
            find_simple_integer_fraction(clk5_multiply_by, clk5_divide_by,
                            max_d_value, i_clk5_mult_by, i_clk5_div_by);
            find_simple_integer_fraction(clk6_multiply_by, clk6_divide_by,
                            max_d_value, i_clk6_mult_by, i_clk6_div_by);
            find_simple_integer_fraction(clk7_multiply_by, clk7_divide_by,
                            max_d_value, i_clk7_mult_by, i_clk7_div_by);
            find_simple_integer_fraction(clk8_multiply_by, clk8_divide_by,
                            max_d_value, i_clk8_mult_by, i_clk8_div_by);
            find_simple_integer_fraction(clk9_multiply_by, clk9_divide_by,
                            max_d_value, i_clk9_mult_by, i_clk9_div_by);

            // convert user parameters to advanced
            if (l_vco_frequency_control == "manual_phase")
            begin
                find_m_and_n_4_manual_phase(inclk0_freq, vco_phase_shift_step,
                            i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,i_clk4_mult_by,
                i_clk5_mult_by,
                i_clk6_mult_by, i_clk7_mult_by,
                i_clk8_mult_by, i_clk9_mult_by,
                            i_clk0_div_by, i_clk1_div_by,
                            i_clk2_div_by, i_clk3_div_by,i_clk4_div_by,
                i_clk5_div_by,
                i_clk6_div_by, i_clk7_div_by,
                i_clk8_div_by, i_clk9_div_by,
                            clk0_counter, clk1_counter,
                            clk2_counter, clk3_counter,clk4_counter,
                clk5_counter,
                clk6_counter, clk7_counter,
                clk8_counter, clk9_counter,
                            i_m, i_n);
            end
            else if (((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right")) && (vco_multiply_by != 0) && (vco_divide_by != 0))
            begin
                i_n = vco_divide_by;
                i_m = vco_multiply_by;
            end
            else begin
                i_n = 1;
                if (((l_pll_type == "fast") || (l_pll_type == "left_right")) && (l_compensate_clock == "lvdsclk"))
                    i_m = i_clk0_mult_by;
                else
                    i_m = lcm  (i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,i_clk4_mult_by,
                i_clk5_mult_by,
                i_clk6_mult_by, i_clk7_mult_by,
                i_clk8_mult_by, i_clk9_mult_by,
                            inclk0_freq);
            end

            i_c_high[0] = counter_high (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by, i_m, i_n), clk0_duty_cycle);
            i_c_high[1] = counter_high (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by, i_m, i_n), clk1_duty_cycle);
            i_c_high[2] = counter_high (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by, i_m, i_n), clk2_duty_cycle);
            i_c_high[3] = counter_high (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by, i_m, i_n), clk3_duty_cycle);
            i_c_high[4] = counter_high (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);
            i_c_high[5] = counter_high (output_counter_value(i_clk5_div_by,
                                        i_clk5_mult_by,  i_m, i_n), clk5_duty_cycle);
            i_c_high[6] = counter_high (output_counter_value(i_clk6_div_by,
                                        i_clk6_mult_by,  i_m, i_n), clk6_duty_cycle);
            i_c_high[7] = counter_high (output_counter_value(i_clk7_div_by,
                                        i_clk7_mult_by,  i_m, i_n), clk7_duty_cycle);
            i_c_high[8] = counter_high (output_counter_value(i_clk8_div_by,
                                        i_clk8_mult_by,  i_m, i_n), clk8_duty_cycle);
            i_c_high[9] = counter_high (output_counter_value(i_clk9_div_by,
                                        i_clk9_mult_by,  i_m, i_n), clk9_duty_cycle);

            i_c_low[0]  = counter_low  (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by,  i_m, i_n), clk0_duty_cycle);
            i_c_low[1]  = counter_low  (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by,  i_m, i_n), clk1_duty_cycle);
            i_c_low[2]  = counter_low  (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by,  i_m, i_n), clk2_duty_cycle);
            i_c_low[3]  = counter_low  (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by,  i_m, i_n), clk3_duty_cycle);
            i_c_low[4]  = counter_low  (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);
            i_c_low[5]  = counter_low  (output_counter_value(i_clk5_div_by,
                                        i_clk5_mult_by,  i_m, i_n), clk5_duty_cycle);
            i_c_low[6]  = counter_low  (output_counter_value(i_clk6_div_by,
                                        i_clk6_mult_by,  i_m, i_n), clk6_duty_cycle);
            i_c_low[7]  = counter_low  (output_counter_value(i_clk7_div_by,
                                        i_clk7_mult_by,  i_m, i_n), clk7_duty_cycle);
            i_c_low[8]  = counter_low  (output_counter_value(i_clk8_div_by,
                                        i_clk8_mult_by,  i_m, i_n), clk8_duty_cycle);
            i_c_low[9]  = counter_low  (output_counter_value(i_clk9_div_by,
                                        i_clk9_mult_by,  i_m, i_n), clk9_duty_cycle);

            if (l_pll_type == "flvds")
            begin
                // Need to readjust phase shift values when the clock multiply value has been readjusted.
                new_multiplier = clk0_multiply_by / i_clk0_mult_by;
                i_clk0_phase_shift = (clk0_phase_shift_num * new_multiplier);
                i_clk1_phase_shift = (clk1_phase_shift_num * new_multiplier);
                i_clk2_phase_shift = (clk2_phase_shift_num * new_multiplier);
                i_clk3_phase_shift = 0;
                i_clk4_phase_shift = 0;
            end
            else
            begin
                i_clk0_phase_shift = get_int_phase_shift(clk0_phase_shift, clk0_phase_shift_num);
                i_clk1_phase_shift = get_int_phase_shift(clk1_phase_shift, clk1_phase_shift_num);
                i_clk2_phase_shift = get_int_phase_shift(clk2_phase_shift, clk2_phase_shift_num);
                i_clk3_phase_shift = get_int_phase_shift(clk3_phase_shift, clk3_phase_shift_num);
                i_clk4_phase_shift = get_int_phase_shift(clk4_phase_shift, clk4_phase_shift_num);
            end

            max_neg_abs = maxnegabs   ( i_clk0_phase_shift,
                                        i_clk1_phase_shift,
                                        i_clk2_phase_shift,
                                        i_clk3_phase_shift,
                                        i_clk4_phase_shift,
                                            str2int(clk5_phase_shift),
                                            str2int(clk6_phase_shift),
                                            str2int(clk7_phase_shift),
                                            str2int(clk8_phase_shift),
                                            str2int(clk9_phase_shift)
                                        );

            i_c_initial[0] = counter_initial(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[1] = counter_initial(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[2] = counter_initial(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[3] = counter_initial(get_phase_degree(ph_adjust(i_clk3_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[4] = counter_initial(get_phase_degree(ph_adjust(i_clk4_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[5] = counter_initial(get_phase_degree(ph_adjust(str2int(clk5_phase_shift), max_neg_abs)), i_m, i_n);
            i_c_initial[6] = counter_initial(get_phase_degree(ph_adjust(str2int(clk6_phase_shift), max_neg_abs)), i_m, i_n);
            i_c_initial[7] = counter_initial(get_phase_degree(ph_adjust(str2int(clk7_phase_shift), max_neg_abs)), i_m, i_n);
            i_c_initial[8] = counter_initial(get_phase_degree(ph_adjust(str2int(clk8_phase_shift), max_neg_abs)), i_m, i_n);
            i_c_initial[9] = counter_initial(get_phase_degree(ph_adjust(str2int(clk9_phase_shift), max_neg_abs)), i_m, i_n);

            i_c_mode[0] = counter_mode(clk0_duty_cycle,output_counter_value(i_clk0_div_by, i_clk0_mult_by,  i_m, i_n));
            i_c_mode[1] = counter_mode(clk1_duty_cycle,output_counter_value(i_clk1_div_by, i_clk1_mult_by,  i_m, i_n));
            i_c_mode[2] = counter_mode(clk2_duty_cycle,output_counter_value(i_clk2_div_by, i_clk2_mult_by,  i_m, i_n));
            i_c_mode[3] = counter_mode(clk3_duty_cycle,output_counter_value(i_clk3_div_by, i_clk3_mult_by,  i_m, i_n));
            i_c_mode[4] = counter_mode(clk4_duty_cycle,output_counter_value(i_clk4_div_by, i_clk4_mult_by,  i_m, i_n));
            i_c_mode[5] = counter_mode(clk5_duty_cycle,output_counter_value(i_clk5_div_by, i_clk5_mult_by,  i_m, i_n));
            i_c_mode[6] = counter_mode(clk6_duty_cycle,output_counter_value(i_clk6_div_by, i_clk6_mult_by,  i_m, i_n));
            i_c_mode[7] = counter_mode(clk7_duty_cycle,output_counter_value(i_clk7_div_by, i_clk7_mult_by,  i_m, i_n));
            i_c_mode[8] = counter_mode(clk8_duty_cycle,output_counter_value(i_clk8_div_by, i_clk8_mult_by,  i_m, i_n));
            i_c_mode[9] = counter_mode(clk9_duty_cycle,output_counter_value(i_clk9_div_by, i_clk9_mult_by,  i_m, i_n));

            i_m_ph    = counter_ph(get_phase_degree(max_neg_abs), i_m, i_n);
            i_m_initial = counter_initial(get_phase_degree(max_neg_abs), i_m, i_n);
            
            i_c_ph[0] = counter_ph(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[1] = counter_ph(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[2] = counter_ph(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[3] = counter_ph(get_phase_degree(ph_adjust(i_clk3_phase_shift,max_neg_abs)), i_m, i_n);
            i_c_ph[4] = counter_ph(get_phase_degree(ph_adjust(i_clk4_phase_shift,max_neg_abs)), i_m, i_n);
            i_c_ph[5] = counter_ph(get_phase_degree(ph_adjust(str2int(clk5_phase_shift),max_neg_abs)), i_m, i_n);
            i_c_ph[6] = counter_ph(get_phase_degree(ph_adjust(str2int(clk6_phase_shift),max_neg_abs)), i_m, i_n);
            i_c_ph[7] = counter_ph(get_phase_degree(ph_adjust(str2int(clk7_phase_shift),max_neg_abs)), i_m, i_n);
            i_c_ph[8] = counter_ph(get_phase_degree(ph_adjust(str2int(clk8_phase_shift),max_neg_abs)), i_m, i_n);
            i_c_ph[9] = counter_ph(get_phase_degree(ph_adjust(str2int(clk9_phase_shift),max_neg_abs)), i_m, i_n);


        end
        else 
        begin //  m != 0

            i_n = n;
            i_m = m;
            i_c_high[0] = c0_high;
            i_c_high[1] = c1_high;
            i_c_high[2] = c2_high;
            i_c_high[3] = c3_high;
            i_c_high[4] = c4_high;
            i_c_high[5] = c5_high;
            i_c_high[6] = c6_high;
            i_c_high[7] = c7_high;
            i_c_high[8] = c8_high;
            i_c_high[9] = c9_high;
            i_c_low[0]  = c0_low;
            i_c_low[1]  = c1_low;
            i_c_low[2]  = c2_low;
            i_c_low[3]  = c3_low;
            i_c_low[4]  = c4_low;
            i_c_low[5]  = c5_low;
            i_c_low[6]  = c6_low;
            i_c_low[7]  = c7_low;
            i_c_low[8]  = c8_low;
            i_c_low[9]  = c9_low;
            i_c_initial[0] = c0_initial;
            i_c_initial[1] = c1_initial;
            i_c_initial[2] = c2_initial;
            i_c_initial[3] = c3_initial;
            i_c_initial[4] = c4_initial;
            i_c_initial[5] = c5_initial;
            i_c_initial[6] = c6_initial;
            i_c_initial[7] = c7_initial;
            i_c_initial[8] = c8_initial;
            i_c_initial[9] = c9_initial;
            i_c_mode[0] = translate_string(alpha_tolower(c0_mode));
            i_c_mode[1] = translate_string(alpha_tolower(c1_mode));
            i_c_mode[2] = translate_string(alpha_tolower(c2_mode));
            i_c_mode[3] = translate_string(alpha_tolower(c3_mode));
            i_c_mode[4] = translate_string(alpha_tolower(c4_mode));
            i_c_mode[5] = translate_string(alpha_tolower(c5_mode));
            i_c_mode[6] = translate_string(alpha_tolower(c6_mode));
            i_c_mode[7] = translate_string(alpha_tolower(c7_mode));
            i_c_mode[8] = translate_string(alpha_tolower(c8_mode));
            i_c_mode[9] = translate_string(alpha_tolower(c9_mode));
            i_c_ph[0]  = c0_ph;
            i_c_ph[1]  = c1_ph;
            i_c_ph[2]  = c2_ph;
            i_c_ph[3]  = c3_ph;
            i_c_ph[4]  = c4_ph;
            i_c_ph[5]  = c5_ph;
            i_c_ph[6]  = c6_ph;
            i_c_ph[7]  = c7_ph;
            i_c_ph[8]  = c8_ph;
            i_c_ph[9]  = c9_ph;
            i_m_ph   = m_ph;        // default
            i_m_initial = m_initial;

        end // user to advanced conversion
        
        switch_clock = 1'b0;

        refclk_period = inclk0_freq * i_n;

        m_times_vco_period = refclk_period;
        new_m_times_vco_period = refclk_period;

        fbclk_period = 0;
        high_time = 0;
        low_time = 0;
        schedule_vco = 0;
        vco_out[7:0] = 8'b0;
        vco_tap[7:0] = 8'b0;
        fbclk_last_value = 0;
        offset = 0;
        temp_offset = 0;
        got_first_refclk = 0;
        got_first_fbclk = 0;
        fbclk_time = 0;
        first_fbclk_time = 0;
        refclk_time = 0;
        first_schedule = 1;
        sched_time = 0;
        vco_val = 0;
        gate_count = 0;
        gate_out = 0;
        initial_delay = 0;
        fbk_phase = 0;
        for (i = 0; i <= 7; i = i + 1)
        begin
            phase_shift[i] = 0;
            last_phase_shift[i] = 0;
        end
        fbk_delay = 0;
        inclk_n = 0;
        inclk_es = 0;
        inclk_man = 0;
        cycle_to_adjust = 0;
        m_delay = 0;
        total_pull_back = 0;
        pull_back_M = 0;
        vco_period_was_phase_adjusted = 0;
        phase_adjust_was_scheduled = 0;
        inclk_out_of_range = 0;
        scandone_tmp = 1'b0;
        schedule_vco_last_value = 0;


        if ((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right"))
        begin
            scan_chain_length = FAST_SCAN_CHAIN;
            num_output_cntrs = 7;
        end
        else
        begin
            scan_chain_length = GPP_SCAN_CHAIN;
            num_output_cntrs = 10;
        end
        
        phasestep_high_count = 0;
        update_phase = 0;
        // set initial values for counter parameters
        m_initial_val = i_m_initial;
        m_val[0] = i_m;
        n_val[0] = i_n;
        m_ph_val = i_m_ph;
        m_ph_val_orig = i_m_ph;
        m_ph_val_tmp = i_m_ph;
        m_val_tmp[0] = i_m;


        if (m_val[0] == 1)
            m_mode_val[0] = "bypass";
        else m_mode_val[0] = "";
        if (m_val[1] == 1)
            m_mode_val[1] = "bypass";
        if (n_val[0] == 1)
            n_mode_val[0] = "bypass";
        if (n_val[1] == 1)
            n_mode_val[1] = "bypass";

        for (i = 0; i < 10; i=i+1)
        begin
            c_high_val[i] = i_c_high[i];
            c_low_val[i] = i_c_low[i];
            c_initial_val[i] = i_c_initial[i];
            c_mode_val[i] = i_c_mode[i];
            c_ph_val[i] = i_c_ph[i];
            c_high_val_tmp[i] = i_c_high[i];
            c_hval[i] = i_c_high[i];
            c_low_val_tmp[i] = i_c_low[i];
            c_lval[i] = i_c_low[i];
            if (c_mode_val[i] == "bypass")
            begin
                if (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right")
                begin
                    c_high_val[i] = 5'b10000;
                    c_low_val[i] = 5'b10000;
                    c_high_val_tmp[i] = 5'b10000;
                    c_low_val_tmp[i] = 5'b10000;
                end
                else begin
                    c_high_val[i] = 9'b100000000;
                    c_low_val[i] = 9'b100000000;
                    c_high_val_tmp[i] = 9'b100000000;
                    c_low_val_tmp[i] = 9'b100000000;
                end
            end

            c_mode_val_tmp[i] = i_c_mode[i];
            c_ph_val_tmp[i] = i_c_ph[i];

            c_ph_val_orig[i] = i_c_ph[i];
            c_high_val_hold[i] = i_c_high[i];
            c_low_val_hold[i] = i_c_low[i];
            c_mode_val_hold[i] = i_c_mode[i];
        end

        lfc_val = loop_filter_c;
        lfr_val = loop_filter_r;
        cp_curr_val = charge_pump_current;
        vco_cur = vco_post_scale;

        i = 0;
        j = 0;
        inclk_last_value = 0;

    
        // initialize clkswitch variables

        clk0_is_bad = 0;
        clk1_is_bad = 0;
        inclk0_last_value = 0;
        inclk1_last_value = 0;
        other_clock_value = 0;
        other_clock_last_value = 0;
        primary_clk_is_bad = 0;
        current_clk_is_bad = 0;
        external_switch = 0;
        current_clock = 0;
        current_clock_man = 0;

        active_clock = 0;   // primary_clk is always inclk0
        if (l_pll_type == "fast" || (l_pll_type == "left_right"))
            l_switch_over_type = "manual";

        if (l_switch_over_type == "manual" && clkswitch === 1'b1)
        begin
            current_clock_man = 1;
            active_clock = 1;
        end
        got_curr_clk_falling_edge_after_clkswitch = 0;
        clk0_count = 0;
        clk1_count = 0;

        // initialize reconfiguration variables
        // quiet_time
        quiet_time = slowest_clk  ( c_high_val[0]+c_low_val[0], c_mode_val[0],
                                    c_high_val[1]+c_low_val[1], c_mode_val[1],
                                    c_high_val[2]+c_low_val[2], c_mode_val[2],
                                    c_high_val[3]+c_low_val[3], c_mode_val[3],
                                    c_high_val[4]+c_low_val[4], c_mode_val[4],
                                    c_high_val[5]+c_low_val[5], c_mode_val[5],
                                    c_high_val[6]+c_low_val[6], c_mode_val[6],
                                    c_high_val[7]+c_low_val[7], c_mode_val[7],
                                    c_high_val[8]+c_low_val[8], c_mode_val[8],
                                    c_high_val[9]+c_low_val[9], c_mode_val[9],
                                    refclk_period, m_val[0]);
        reconfig_err = 0;
        error = 0;
        
        
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        c5_rising_edge_transfer_done = 0;
        c6_rising_edge_transfer_done = 0;
        c7_rising_edge_transfer_done = 0;
        c8_rising_edge_transfer_done = 0;
        c9_rising_edge_transfer_done = 0;
        got_first_scanclk = 0;
        got_first_gated_scanclk = 0;
        gated_scanclk = 1;
        scanread_setup_violation = 0;
        index = 0;

        vco_over  = 1'b0;
        vco_under = 1'b0;
        
        // Initialize the scan chain 
        
        // LF unused : bit 1
        scan_data[-1:0] = 2'b00;
        // LF Capacitance : bits 1,2 : all values are legal
        scan_data[1:2] = loop_filter_c_bits;
        // LF Resistance : bits 3-7
        scan_data[3:7] = loop_filter_r_bits;
        
        // VCO post scale
        if(vco_post_scale == 1)
        begin
            scan_data[8] = 1'b1;
            vco_val_old_bit_setting = 1'b1;
        end
        else
        begin
            scan_data[8] = 1'b0;
            vco_val_old_bit_setting = 1'b0;
        end
            
        scan_data[9:13] = 5'b00000;
        // CP
        // Bit 8 : CRBYPASS
        // Bit 9-13 : unused
        // Bits 14-16 : all values are legal                 
                scan_data[14:16] = charge_pump_current_bits;
        // store as old values
        
        cp_curr_old_bit_setting = charge_pump_current_bits;
        lfc_val_old_bit_setting = loop_filter_c_bits;
        lfr_val_old_bit_setting = loop_filter_r_bits;
            
        // C counters (start bit 53) bit 1:mode(bypass),bit 2-9:high,bit 10:mode(odd/even),bit 11-18:low
        for (i = 0; i < num_output_cntrs; i = i + 1)
        begin
            // 1. Mode - bypass
            if (c_mode_val[i] == "bypass")
            begin
                scan_data[53 + i*18 + 0] = 1'b1;
                if (c_mode_val[i] == "   odd")
                    scan_data[53 + i*18 + 9] = 1'b1;
                else
                    scan_data[53 + i*18 + 9] = 1'b0;
            end
            else
            begin
                scan_data[53 + i*18 + 0] = 1'b0;
                // 3. Mode - odd/even
                if (c_mode_val[i] == "   odd")
                    scan_data[53 + i*18 + 9] = 1'b1;
                else
                    scan_data[53 + i*18 + 9] = 1'b0;
            end
            // 2. Hi
            c_val = c_high_val[i];
            for (j = 1; j <= 8; j = j + 1)
                scan_data[53 + i*18 + j]  = c_val[8 - j];
   
            // 4. Low
            c_val = c_low_val[i];
            for (j = 10; j <= 17; j = j + 1)
                scan_data[53 + i*18 + j] = c_val[17 - j];
        end
            
        // M counter
        // 1. Mode - bypass (bit 17)
        if (m_mode_val[0] == "bypass")
                scan_data[17] = 1'b1;
        else
                scan_data[17] = 1'b0;  // set bypass bit to 0
       
        // 2. High (bit 18-25)
        // 3. Mode - odd/even (bit 26)
        if (m_val[0] % 2 == 0)
        begin
            // M is an even no. : set M high = low,
            // set odd/even bit to 0
                scan_data[18:25] = m_val[0]/2;
                scan_data[26] = 1'b0;
        end
        else 
        begin 
            // M is odd : M high = low + 1
                scan_data[18:25] = m_val[0]/2 + 1;
                scan_data[26] = 1'b1;
        end
        // 4. Low (bit 27-34)
            scan_data[27:34] = m_val[0]/2;

        
        // N counter
        // 1. Mode - bypass (bit 35)
        if (n_mode_val[0] == "bypass")
                scan_data[35] = 1'b1;
        else 
                scan_data[35] = 1'b0;  // set bypass bit to 0
        // 2. High (bit 36-43)
        // 3. Mode - odd/even (bit 44)
        if (n_val[0] % 2 == 0)
        begin
            // N is an even no. : set N high = low,
            // set odd/even bit to 0
                scan_data[36:43] = n_val[0]/2;
                scan_data[44] = 1'b0;
        end
        else 
        begin // N is odd : N high = N low + 1
                scan_data[36:43] = n_val[0]/2 + 1;
                scan_data[44] = 1'b1;
        end
        // 4. Low (bit 45-52)
                scan_data[45:52] = n_val[0]/2;


        l_index = 1;
        stop_vco = 0;
        cycles_to_lock = 0;
        cycles_to_unlock = 0;
        locked_tmp = 0;
        pll_is_locked = 0;
        no_warn = 1'b0;
        
        pfd_locked = 1'b0;
        cycles_pfd_high = 0;
        cycles_pfd_low  = 0;

        // check if pll is in test mode
        if (m_test_source != -1 || c0_test_source != -1 || c1_test_source != -1 || c2_test_source != -1 || c3_test_source != -1 || c4_test_source != -1 || c5_test_source != -1 || c6_test_source != -1 || c7_test_source != -1 || c8_test_source != -1 || c9_test_source != -1)
            pll_in_test_mode = 1'b1;
        else
            pll_in_test_mode = 1'b0;

        pll_is_in_reset = 0;
        pll_has_just_been_reconfigured = 0;
        if (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right")
            is_fast_pll = 1;
        else is_fast_pll = 0;

        if (c1_use_casc_in == "on")
            ic1_use_casc_in = 1;
        else
            ic1_use_casc_in = 0;
        if (c2_use_casc_in == "on")
            ic2_use_casc_in = 1;
        else
            ic2_use_casc_in = 0;
        if (c3_use_casc_in == "on")
            ic3_use_casc_in = 1;
        else
            ic3_use_casc_in = 0;
        if (c4_use_casc_in == "on")
            ic4_use_casc_in = 1;
        else
            ic4_use_casc_in = 0;
        if (c5_use_casc_in == "on")
            ic5_use_casc_in = 1;
        else
            ic5_use_casc_in = 0;
        if (c6_use_casc_in == "on")
            ic6_use_casc_in = 1;
        else
            ic6_use_casc_in = 0;
        if (c7_use_casc_in == "on")
            ic7_use_casc_in = 1;
        else
            ic7_use_casc_in = 0;
        if (c8_use_casc_in == "on")
            ic8_use_casc_in = 1;
        else
            ic8_use_casc_in = 0;
        if (c9_use_casc_in == "on")
            ic9_use_casc_in = 1;
        else
            ic9_use_casc_in = 0;

        tap0_is_active = 1;
        
// To display clock mapping       
    case( i_clk0_counter)
            "c0" : clk_num[0] = "  clk0";
            "c1" : clk_num[0] = "  clk1";
            "c2" : clk_num[0] = "  clk2";
            "c3" : clk_num[0] = "  clk3";
            "c4" : clk_num[0] = "  clk4";
            "c5" : clk_num[0] = "  clk5";
            "c6" : clk_num[0] = "  clk6";
            "c7" : clk_num[0] = "  clk7";
            "c8" : clk_num[0] = "  clk8";
            "c9" : clk_num[0] = "  clk9";
            default:clk_num[0] = "unused";
    endcase
    
        case( i_clk1_counter)
            "c0" : clk_num[1] = "  clk0";
            "c1" : clk_num[1] = "  clk1";
            "c2" : clk_num[1] = "  clk2";
            "c3" : clk_num[1] = "  clk3";
            "c4" : clk_num[1] = "  clk4";
            "c5" : clk_num[1] = "  clk5";
            "c6" : clk_num[1] = "  clk6";
            "c7" : clk_num[1] = "  clk7";
            "c8" : clk_num[1] = "  clk8";
            "c9" : clk_num[1] = "  clk9";
            default:clk_num[1] = "unused";
    endcase
        
    case( i_clk2_counter)
            "c0" : clk_num[2] = "  clk0";
            "c1" : clk_num[2] = "  clk1";
            "c2" : clk_num[2] = "  clk2";
            "c3" : clk_num[2] = "  clk3";
            "c4" : clk_num[2] = "  clk4";
            "c5" : clk_num[2] = "  clk5";
            "c6" : clk_num[2] = "  clk6";
            "c7" : clk_num[2] = "  clk7";
            "c8" : clk_num[2] = "  clk8";
            "c9" : clk_num[2] = "  clk9";
            default:clk_num[2] = "unused";
    endcase
        
    case( i_clk3_counter)
            "c0" : clk_num[3] = "  clk0";
            "c1" : clk_num[3] = "  clk1";
            "c2" : clk_num[3] = "  clk2";
            "c3" : clk_num[3] = "  clk3";
            "c4" : clk_num[3] = "  clk4";
            "c5" : clk_num[3] = "  clk5";
            "c6" : clk_num[3] = "  clk6";
            "c7" : clk_num[3] = "  clk7";
            "c8" : clk_num[3] = "  clk8";
            "c9" : clk_num[3] = "  clk9";
            default:clk_num[3] = "unused";
    endcase
        
    case( i_clk4_counter)
            "c0" : clk_num[4] = "  clk0";
            "c1" : clk_num[4] = "  clk1";
            "c2" : clk_num[4] = "  clk2";
            "c3" : clk_num[4] = "  clk3";
            "c4" : clk_num[4] = "  clk4";
            "c5" : clk_num[4] = "  clk5";
            "c6" : clk_num[4] = "  clk6";
            "c7" : clk_num[4] = "  clk7";
            "c8" : clk_num[4] = "  clk8";
            "c9" : clk_num[4] = "  clk9";
            default:clk_num[4] = "unused";
    endcase
        
    case( i_clk5_counter)
            "c0" : clk_num[5] = "  clk0";
            "c1" : clk_num[5] = "  clk1";
            "c2" : clk_num[5] = "  clk2";
            "c3" : clk_num[5] = "  clk3";
            "c4" : clk_num[5] = "  clk4";
            "c5" : clk_num[5] = "  clk5";
            "c6" : clk_num[5] = "  clk6";
            "c7" : clk_num[5] = "  clk7";
            "c8" : clk_num[5] = "  clk8";
            "c9" : clk_num[5] = "  clk9";
            default:clk_num[5] = "unused";
    endcase
        
    case( i_clk6_counter)
            "c0" : clk_num[6] = "  clk0";
            "c1" : clk_num[6] = "  clk1";
            "c2" : clk_num[6] = "  clk2";
            "c3" : clk_num[6] = "  clk3";
            "c4" : clk_num[6] = "  clk4";
            "c5" : clk_num[6] = "  clk5";
            "c6" : clk_num[6] = "  clk6";
            "c7" : clk_num[6] = "  clk7";
            "c8" : clk_num[6] = "  clk8";
            "c9" : clk_num[6] = "  clk9";
            default:clk_num[6] = "unused";
    endcase
    
    case( i_clk7_counter)
            "c0" : clk_num[7] = "  clk0";
            "c1" : clk_num[7] = "  clk1";
            "c2" : clk_num[7] = "  clk2";
            "c3" : clk_num[7] = "  clk3";
            "c4" : clk_num[7] = "  clk4";
            "c5" : clk_num[7] = "  clk5";
            "c6" : clk_num[7] = "  clk6";
            "c7" : clk_num[7] = "  clk7";
            "c8" : clk_num[7] = "  clk8";
            "c9" : clk_num[7] = "  clk9";
            default:clk_num[7] = "unused";
    endcase
        
    case( i_clk8_counter)
            "c0" : clk_num[8] = "  clk0";
            "c1" : clk_num[8] = "  clk1";
            "c2" : clk_num[8] = "  clk2";
            "c3" : clk_num[8] = "  clk3";
            "c4" : clk_num[8] = "  clk4";
            "c5" : clk_num[8] = "  clk5";
            "c6" : clk_num[8] = "  clk6";
            "c7" : clk_num[8] = "  clk7";
            "c8" : clk_num[8] = "  clk8";
            "c9" : clk_num[8] = "  clk9";
            default:clk_num[8] = "unused";
    endcase
        
    case( i_clk9_counter)
            "c0" : clk_num[9] = "  clk0";
            "c1" : clk_num[9] = "  clk1";
            "c2" : clk_num[9] = "  clk2";
            "c3" : clk_num[9] = "  clk3";
            "c4" : clk_num[9] = "  clk4";
            "c5" : clk_num[9] = "  clk5";
            "c6" : clk_num[9] = "  clk6";
            "c7" : clk_num[9] = "  clk7";
            "c8" : clk_num[9] = "  clk8";
            "c9" : clk_num[9] = "  clk9";
            default:clk_num[9] = "unused";
    endcase

        end


// Clock Switchover

always @(clkswitch)
begin
    if (clkswitch === 1'b1 && l_switch_over_type == "auto")
        external_switch = 1;
    else if (l_switch_over_type == "manual") 
    begin
        if(clkswitch === 1'b1)
            switch_clock = 1'b1;
        else
            switch_clock = 1'b0;
    end
end


always @(posedge inclk[0])
begin
// Determine the inclk0 frequency
    if (first_inclk0_edge_detect == 1'b0)
        begin
            first_inclk0_edge_detect = 1'b1;
        end
    else
        begin
            last_inclk0_period = inclk0_period;
            inclk0_period = $realtime - last_inclk0_edge;
        end
    last_inclk0_edge = $realtime;

end

always @(posedge inclk[1])
begin
// Determine the inclk1 frequency
    if (first_inclk1_edge_detect == 1'b0)
        begin
            first_inclk1_edge_detect = 1'b1;
        end
    else
        begin
            last_inclk1_period = inclk1_period;
            inclk1_period = $realtime - last_inclk1_edge;
        end
    last_inclk1_edge = $realtime;

end

    always @(inclk[0] or inclk[1])
    begin
        if(switch_clock == 1'b1)
        begin
                if(current_clock_man == 0)
                begin
                    current_clock_man = 1;
                    active_clock = 1;
                end
                else
                begin
                    current_clock_man = 0;
                    active_clock = 0;
                end
                switch_clock = 1'b0;
            end

        if (current_clock_man == 0)
            inclk_man = inclk[0];
        else
            inclk_man = inclk[1];


        // save the inclk event value
        if (inclk[0] !== inclk0_last_value)
        begin
            if (current_clock != 0)
                other_clock_value = inclk[0];
        end
        if (inclk[1] !== inclk1_last_value)
        begin
            if (current_clock != 1)
                other_clock_value = inclk[1];
        end

        // check if either input clk is bad
        if (inclk[0] === 1'b1 && inclk[0] !== inclk0_last_value)
        begin
            clk0_count = clk0_count + 1;
            clk0_is_bad = 0;
            clk1_count = 0;
            if (clk0_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk1_is_bad = 1;
                if (current_clock == 1)
                    current_clk_is_bad = 1;
            end
        end
        if (inclk[1] === 1'b1 && inclk[1] !== inclk1_last_value)
        begin
            clk1_count = clk1_count + 1;
            clk1_is_bad = 0;
            clk0_count = 0;
            if (clk1_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk0_is_bad = 1;
                if (current_clock == 0)
                    current_clk_is_bad = 1;
            end
        end

        // check if the bad clk is the primary clock, which is always clk0
        if (clk0_is_bad == 1'b1)
            primary_clk_is_bad = 1;
        else
            primary_clk_is_bad = 0;

        // actual switching -- manual switch
        if ((inclk[0] !== inclk0_last_value) && current_clock == 0)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk[0] === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_es = inclk[0];
                end
            end
            else inclk_es = inclk[0];
        end
        if ((inclk[1] !== inclk1_last_value) && current_clock == 1)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk[1] === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_es = inclk[1];
                end
            end
            else inclk_es = inclk[1];
        end

        // actual switching -- automatic switch
        if ((other_clock_value == 1'b1) && (other_clock_value != other_clock_last_value) && l_enable_switch_over_counter == "on" && primary_clk_is_bad)
            switch_over_count = switch_over_count + 1;
        
        if ((other_clock_value == 1'b0) && (other_clock_value != other_clock_last_value))
        begin
            if ((external_switch && (got_curr_clk_falling_edge_after_clkswitch || current_clk_is_bad)) || (primary_clk_is_bad && (clkswitch !== 1'b1) && ((l_enable_switch_over_counter == "off" || switch_over_count == switch_over_counter))))
            begin
                if (areset === 1'b0)
                begin
                    if ((inclk0_period > inclk1_period) && (inclk1_period != 0))
                        diff_percent_period = (( inclk0_period - inclk1_period ) * 100) / inclk1_period;
                    else if (inclk0_period != 0)
                        diff_percent_period = (( inclk1_period - inclk0_period ) * 100) / inclk0_period;

                    if((diff_percent_period > 20)&& (l_switch_over_type == "auto"))
                    begin
                        $display ("Warning : The input clock frequencies specified for the specified PLL are too far apart for auto-switch-over feature to work properly. Please make sure that the clock frequencies are 20 percent apart for correct functionality.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end

                got_curr_clk_falling_edge_after_clkswitch = 0;
                if (current_clock == 0)
                    current_clock = 1;
                else
                    current_clock = 0;
                    
                active_clock = ~active_clock;
                switch_over_count = 0;
                external_switch = 0;
                current_clk_is_bad = 0;
            end
            else if(l_switch_over_type == "auto")
                begin
                    if(current_clock == 0 && clk0_is_bad == 1'b1 && clk1_is_bad == 1'b0 )
                        begin
                            current_clock = 1;
                            active_clock = ~active_clock;
                        end 
                
                    if(current_clock == 1 && clk1_is_bad == 1'b1 && clk0_is_bad == 1'b0 )
                        begin
                            current_clock = 0;
                            active_clock = ~active_clock;
                        end
                end     
        end
        
        if(l_switch_over_type == "manual")
            inclk_n = inclk_man;
        else
            inclk_n = inclk_es;
            
        inclk0_last_value = inclk[0];
        inclk1_last_value = inclk[1];
        other_clock_last_value = other_clock_value;

    end

    and (clkbad[0], clk0_is_bad, 1'b1);
    and (clkbad[1], clk1_is_bad, 1'b1);
    and (activeclock, active_clock, 1'b1);


    assign inclk_m = (m_test_source == 0) ? fbclk : (m_test_source == 1) ? refclk : inclk_m_from_vco; 
                       

    ttn_m_cntr m1 (.clk(inclk_m),
                        .reset(areset || stop_vco),
                        .cout(fbclk),
                        .initial_value(m_initial_val),
                        .modulus(m_val[0]),
                        .time_delay(m_delay));

    ttn_n_cntr n1 (.clk(inclk_n),
                        .reset(areset),
                        .cout(refclk),
                        .modulus(n_val[0]));



    // Update clock on /o counters from corresponding VCO tap
    assign inclk_m_from_vco  = vco_tap[m_ph_val];
    assign inclk_c0_from_vco = vco_tap[c_ph_val[0]];
    assign inclk_c1_from_vco = vco_tap[c_ph_val[1]];
    assign inclk_c2_from_vco = vco_tap[c_ph_val[2]];
    assign inclk_c3_from_vco = vco_tap[c_ph_val[3]];
    assign inclk_c4_from_vco = vco_tap[c_ph_val[4]];
    assign inclk_c5_from_vco = vco_tap[c_ph_val[5]];
    assign inclk_c6_from_vco = vco_tap[c_ph_val[6]];
    assign inclk_c7_from_vco = vco_tap[c_ph_val[7]];
    assign inclk_c8_from_vco = vco_tap[c_ph_val[8]];
    assign inclk_c9_from_vco = vco_tap[c_ph_val[9]];
always @(vco_out)
    begin
        // check which VCO TAP has event
        for (x = 0; x <= 7; x = x + 1)
        begin
            if (vco_out[x] !== vco_out_last_value[x])
            begin
                // TAP 'X' has event
                if ((x == 0) && (!pll_is_in_reset) && (stop_vco !== 1'b1))
                begin
                    if (vco_out[0] == 1'b1)
                        tap0_is_active = 1;
                    if (tap0_is_active == 1'b1)
                        vco_tap[0] <= vco_out[0];
                end
                else if (tap0_is_active == 1'b1)
                    vco_tap[x] <= vco_out[x];
                if (stop_vco === 1'b1)
                    vco_out[x] <= 1'b0;
            end
        end
        vco_out_last_value = vco_out;
    end

    always @(vco_tap)
    begin
        // Update phase taps for C/M counters on negative edge of VCO clock output
        
        if (update_phase == 1'b1)
        begin
            for (x = 0; x <= 7; x = x + 1)
            begin
                if ((vco_tap[x] === 1'b0) && (vco_tap[x] !== vco_tap_last_value[x]))
                begin
                    for (y = 0; y < 10; y = y + 1)
                    begin
                        if (c_ph_val_tmp[y] == x)
                            c_ph_val[y] = c_ph_val_tmp[y];
                    end
                    if (m_ph_val_tmp == x)
                        m_ph_val = m_ph_val_tmp;
                end
            end
            update_phase <= #(0.5*scanclk_period) 1'b0;
        end

        // On reset, set all C/M counter phase taps to POF programmed values
        if (areset === 1'b1)
        begin
            m_ph_val = m_ph_val_orig;
            m_ph_val_tmp = m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
            begin
                c_ph_val[i] = c_ph_val_orig[i];
                c_ph_val_tmp[i] = c_ph_val_orig[i];
            end
        end

        vco_tap_last_value = vco_tap;
    end

    assign inclk_c0 = (c0_test_source == 0) ? fbclk : (c0_test_source == 1) ? refclk : inclk_c0_from_vco;

    ttn_scale_cntr c0 (.clk(inclk_c0),
                            .reset(areset  || stop_vco),
                            .cout(c0_clk),
                            .high(c_high_val[0]),
                            .low(c_low_val[0]),
                            .initial_value(c_initial_val[0]),
                            .mode(c_mode_val[0]),
                            .ph_tap(c_ph_val[0]));

    // Update /o counters mode and duty cycle immediately after configupdate is asserted
    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[0] <= c_high_val_tmp[0];
            c_mode_val[0] <= c_mode_val_tmp[0];
            c0_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c0_rising_edge_transfer_done)
        begin
            c_low_val[0] <= c_low_val_tmp[0];
        end
    end

    assign inclk_c1 = (c1_test_source == 0) ? fbclk : (c1_test_source == 1) ? refclk : (ic1_use_casc_in == 1) ? c0_clk : inclk_c1_from_vco;
    
    ttn_scale_cntr c1 (.clk(inclk_c1),
                            .reset(areset || stop_vco),
                            .cout(c1_clk),
                            .high(c_high_val[1]),
                            .low(c_low_val[1]),
                            .initial_value(c_initial_val[1]),
                            .mode(c_mode_val[1]),
                            .ph_tap(c_ph_val[1]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[1] <= c_high_val_tmp[1];
            c_mode_val[1] <= c_mode_val_tmp[1];
            c1_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c1_rising_edge_transfer_done)
        begin
            c_low_val[1] <= c_low_val_tmp[1];
        end
    end

    assign inclk_c2 = (c2_test_source == 0) ? fbclk : (c2_test_source == 1) ? refclk :(ic2_use_casc_in == 1) ? c1_clk : inclk_c2_from_vco;

    ttn_scale_cntr c2 (.clk(inclk_c2),
                            .reset(areset || stop_vco),
                            .cout(c2_clk),
                            .high(c_high_val[2]),
                            .low(c_low_val[2]),
                            .initial_value(c_initial_val[2]),
                            .mode(c_mode_val[2]),
                            .ph_tap(c_ph_val[2]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[2] <= c_high_val_tmp[2];
            c_mode_val[2] <= c_mode_val_tmp[2];
            c2_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c2_rising_edge_transfer_done)
        begin
            c_low_val[2] <= c_low_val_tmp[2];
        end
    end

    assign inclk_c3 = (c3_test_source == 0) ? fbclk : (c3_test_source == 1) ? refclk : (ic3_use_casc_in == 1) ? c2_clk : inclk_c3_from_vco;
    
    ttn_scale_cntr c3 (.clk(inclk_c3),
                            .reset(areset  || stop_vco),
                            .cout(c3_clk),
                            .high(c_high_val[3]),
                            .low(c_low_val[3]),
                            .initial_value(c_initial_val[3]),
                            .mode(c_mode_val[3]),
                            .ph_tap(c_ph_val[3]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[3] <= c_high_val_tmp[3];
            c_mode_val[3] <= c_mode_val_tmp[3];
            c3_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c3_rising_edge_transfer_done)
        begin
            c_low_val[3] <= c_low_val_tmp[3];
        end
    end

    assign inclk_c4 = ((c4_test_source == 0) ? fbclk : (c4_test_source == 1) ? refclk :  (ic4_use_casc_in == 1) ? c3_clk : inclk_c4_from_vco);
    ttn_scale_cntr c4 (.clk(inclk_c4),
                            .reset(areset || stop_vco),
                            .cout(c4_clk),
                            .high(c_high_val[4]),
                            .low(c_low_val[4]),
                            .initial_value(c_initial_val[4]),
                            .mode(c_mode_val[4]),
                            .ph_tap(c_ph_val[4]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[4] <= c_high_val_tmp[4];
            c_mode_val[4] <= c_mode_val_tmp[4];
            c4_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c4_rising_edge_transfer_done)
        begin
            c_low_val[4] <= c_low_val_tmp[4];
        end
    end

    assign inclk_c5 = (c5_test_source == 0) ? fbclk : (c5_test_source == 1) ? refclk : (ic5_use_casc_in == 1) ? c4_clk : inclk_c5_from_vco;
    ttn_scale_cntr c5 (.clk(inclk_c5),
                            .reset(areset  || stop_vco),
                            .cout(c5_clk),
                            .high(c_high_val[5]),
                            .low(c_low_val[5]),
                            .initial_value(c_initial_val[5]),
                            .mode(c_mode_val[5]),
                            .ph_tap(c_ph_val[5]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[5] <= c_high_val_tmp[5];
            c_mode_val[5] <= c_mode_val_tmp[5];
            c5_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c5_rising_edge_transfer_done)
        begin
            c_low_val[5] <= c_low_val_tmp[5];
        end
    end
    
    assign inclk_c6 = ((c6_test_source == 0) ? fbclk : (c6_test_source == 1) ? refclk :  (ic6_use_casc_in == 1) ? c5_clk : inclk_c6_from_vco);
    ttn_scale_cntr c6 (.clk(inclk_c6),
                            .reset(areset  || stop_vco),
                            .cout(c6_clk),
                            .high(c_high_val[6]),
                            .low(c_low_val[6]),
                            .initial_value(c_initial_val[6]),
                            .mode(c_mode_val[6]),
                            .ph_tap(c_ph_val[6]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[6] <= c_high_val_tmp[6];
            c_mode_val[6] <= c_mode_val_tmp[6];
            c6_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c6_rising_edge_transfer_done)
        begin
            c_low_val[6] <= c_low_val_tmp[6];
        end
    end
    
    assign inclk_c7 = ((c7_test_source == 0) ? fbclk : (c7_test_source == 1) ? refclk :  (ic7_use_casc_in == 1) ? c6_clk : inclk_c7_from_vco);
    ttn_scale_cntr c7 (.clk(inclk_c7),
                            .reset(areset  || stop_vco),
                            .cout(c7_clk),
                            .high(c_high_val[7]),
                            .low(c_low_val[7]),
                            .initial_value(c_initial_val[7]),
                            .mode(c_mode_val[7]),
                            .ph_tap(c_ph_val[7]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[7] <= c_high_val_tmp[7];
            c_mode_val[7] <= c_mode_val_tmp[7];
            c7_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c7_rising_edge_transfer_done)
        begin
            c_low_val[7] <= c_low_val_tmp[7];
        end
    end
    
    assign inclk_c8 = ((c8_test_source == 0) ? fbclk : (c8_test_source == 1) ? refclk :  (ic8_use_casc_in == 1) ? c7_clk : inclk_c8_from_vco);
    ttn_scale_cntr c8 (.clk(inclk_c8),
                            .reset(areset || stop_vco),
                            .cout(c8_clk),
                            .high(c_high_val[8]),
                            .low(c_low_val[8]),
                            .initial_value(c_initial_val[8]),
                            .mode(c_mode_val[8]),
                            .ph_tap(c_ph_val[8]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[8] <= c_high_val_tmp[8];
            c_mode_val[8] <= c_mode_val_tmp[8];
            c8_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c8_rising_edge_transfer_done)
        begin
            c_low_val[8] <= c_low_val_tmp[8];
        end
    end
    
    assign inclk_c9 = ((c9_test_source == 0) ? fbclk : (c9_test_source == 1) ? refclk :  (ic9_use_casc_in == 1) ? c8_clk : inclk_c9_from_vco);
    ttn_scale_cntr c9 (.clk(inclk_c9),
                            .reset(areset  || stop_vco),
                            .cout(c9_clk),
                            .high(c_high_val[9]),
                            .low(c_low_val[9]),
                            .initial_value(c_initial_val[9]),
                            .mode(c_mode_val[9]),
                            .ph_tap(c_ph_val[9]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[9] <= c_high_val_tmp[9];
            c_mode_val[9] <= c_mode_val_tmp[9];
            c9_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c9_rising_edge_transfer_done)
        begin
            c_low_val[9] <= c_low_val_tmp[9];
        end
    end
    
assign locked = (test_bypass_lock_detect == "on") ? pfd_locked : locked_tmp;

// Register scanclk enable
    always @(negedge scanclk)
        scanclkena_reg <= scanclkena;
        
// Negative edge flip-flop in front of scan-chain

    always @(negedge scanclk)
    begin
        if (scanclkena_reg)
        begin
            scandata_in <= scandata;
        end
    end
   
// Scan chain
    always @(posedge scanclk)
    begin
        if (got_first_scanclk === 1'b0)
                got_first_scanclk = 1'b1;
        else
                scanclk_period = $time - scanclk_last_rising_edge;
        if (scanclkena_reg) 
        begin        
            for (j = scan_chain_length-2; j >= 0; j = j - 1)
                scan_data[j] = scan_data[j - 1];
            scan_data[-1] <= scandata_in;
        end
        scanclk_last_rising_edge = $realtime;
    end
    
// Scan output
    assign scandataout_tmp = (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right") ? scan_data[FAST_SCAN_CHAIN-2] : scan_data[GPP_SCAN_CHAIN-2];

// Negative edge flip-flop in rear of scan-chain

    always @(negedge scanclk)
    begin
        if (scanclkena_reg)
        begin
            scandata_out <= scandataout_tmp;
        end
    end
    
// Scan complete
    always @(negedge scandone_tmp)
    begin
            if (got_first_scanclk === 1'b1)
            begin
            if (reconfig_err == 1'b0)
            begin
                $display("NOTE : PLL Reprogramming completed with the following values (Values in parantheses are original values) : ");
                $display ("Time: %0t  Instance: %m", $time);

                $display("               N modulus =   %0d (%0d) ", n_val[0], n_val_old[0]);
                $display("               M modulus =   %0d (%0d) ", m_val[0], m_val_old[0]);
                

                for (i = 0; i < num_output_cntrs; i=i+1)
                begin
                    $display("              %s :    C%0d  high = %0d (%0d),       C%0d  low = %0d (%0d),       C%0d  mode = %s (%s)", clk_num[i],i, c_high_val[i], c_high_val_old[i], i, c_low_val_tmp[i], c_low_val_old[i], i, c_mode_val[i], c_mode_val_old[i]);
                end

                // display Charge pump and loop filter values
                if (pll_reconfig_display_full_setting == 1'b1)
                begin
                    $display ("               Charge Pump Current (uA) =   %0d (%0d) ", cp_curr_val, cp_curr_old);
                    $display ("               Loop Filter Capacitor (pF) =   %0d (%0d) ", lfc_val, lfc_old);
                    $display ("               Loop Filter Resistor (Kohm) =   %s (%s) ", lfr_val, lfr_old);
                    $display ("               VCO_Post_Scale  =   %0d (%0d) ", vco_cur, vco_old);
                end
                else
                begin
                    $display ("               Charge Pump Current  =   %0d (%0d) ", cp_curr_bit_setting, cp_curr_old_bit_setting);
                    $display ("               Loop Filter Capacitor  =   %0d (%0d) ", lfc_val_bit_setting, lfc_val_old_bit_setting);
                    $display ("               Loop Filter Resistor   =   %0d (%0d) ", lfr_val_bit_setting, lfr_val_old_bit_setting);
                    $display ("               VCO_Post_Scale   =   %b (%b) ", vco_val_bit_setting, vco_val_old_bit_setting);
                end
                cp_curr_old_bit_setting = cp_curr_bit_setting;
                lfc_val_old_bit_setting = lfc_val_bit_setting;
                lfr_val_old_bit_setting = lfr_val_bit_setting;
                vco_val_old_bit_setting = vco_val_bit_setting;
            end
            else begin
                $display("Warning : Errors were encountered during PLL reprogramming. Please refer to error/warning messages above.");
                $display ("Time: %0t  Instance: %m", $time);
            end
            end
    end

// ************ PLL Phase Reconfiguration ************* //

// Latch updown,counter values at pos edge of scan clock
always @(posedge scanclk)
begin
    if (phasestep_reg == 1'b1)
    begin
        if (phasestep_high_count == 1)
        begin
            phasecounterselect_reg <= phasecounterselect;
            phaseupdown_reg <= phaseupdown;
            // start reconfiguration
            if (phasecounterselect < 4'b1100) // no counters selected
            begin
                if (phasecounterselect == 0) // all output counters selected
                begin
                    for (i = 0; i < num_output_cntrs; i = i + 1)
                        c_ph_val_tmp[i] = (phaseupdown == 1'b1) ? 
                                    (c_ph_val_tmp[i] + 1) % num_phase_taps :
                                    (c_ph_val_tmp[i] == 0) ? num_phase_taps - 1 : (c_ph_val_tmp[i] - 1) % num_phase_taps ;
                end
                else if (phasecounterselect == 1) // select M counter
                begin
                    m_ph_val_tmp = (phaseupdown == 1'b1) ? 
                                (m_ph_val + 1) % num_phase_taps :
                                (m_ph_val == 0) ? num_phase_taps - 1 : (m_ph_val - 1) % num_phase_taps ;
                end
                else // select C counters
                begin
                    select_counter = phasecounterselect - 2;
                    c_ph_val_tmp[select_counter] =  (phaseupdown == 1'b1) ? 
                                            (c_ph_val_tmp[select_counter] + 1) % num_phase_taps :
                                            (c_ph_val_tmp[select_counter] == 0) ? num_phase_taps - 1 : (c_ph_val_tmp[select_counter] - 1) % num_phase_taps ;
                end
                update_phase <= 1'b1;
            end 
           
        end
        phasestep_high_count = phasestep_high_count + 1;
       
    end
end

// Latch phase enable (same as phasestep) on neg edge of scan clock
always @(negedge scanclk)
begin
    phasestep_reg <= phasestep;
end

always @(posedge phasestep) 
begin
    if (update_phase == 1'b0) phasestep_high_count = 0; // phase adjustments must be 1 cycle apart
                                                        // if not, next phasestep cycle is skipped
end

// ************ PLL Full Reconfiguration ************* //
assign update_conf_latches = configupdate;


        // reset counter transfer flags
    always @(negedge scandone_tmp)
    begin
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        c5_rising_edge_transfer_done = 0;
        c6_rising_edge_transfer_done = 0;
        c7_rising_edge_transfer_done = 0;
        c8_rising_edge_transfer_done = 0;
        c9_rising_edge_transfer_done = 0;
        update_conf_latches_reg <= 1'b0;
    end


    always @(posedge update_conf_latches)
    begin
        initiate_reconfig <= 1'b1;
    end
   
    always @(posedge areset)
    begin
        if (scandone_tmp == 1'b1) scandone_tmp = 1'b0;
    end
   
    always @(posedge scanclk)
    begin
        if (initiate_reconfig == 1'b1) 
        begin
            initiate_reconfig <= 1'b0;
            $display ("NOTE : PLL Reprogramming initiated ....");
            $display ("Time: %0t  Instance: %m", $time);

            scandone_tmp <= #(scanclk_period) 1'b1;
            update_conf_latches_reg <= update_conf_latches;

            error = 0;
            reconfig_err = 0;
            scanread_setup_violation = 0;

            // save old values
            cp_curr_old = cp_curr_val;
            lfc_old = lfc_val;
            lfr_old = lfr_val;
            vco_old = vco_cur;
            // save old values of bit settings
            cp_curr_bit_setting = scan_data[14:16];
            lfc_val_bit_setting = scan_data[1:2];
            lfr_val_bit_setting = scan_data[3:7];
            vco_val_bit_setting = scan_data[8];

            // LF unused : bit 1
            // LF Capacitance : bits 1,2 : all values are legal
            if ((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right"))
                lfc_val = fpll_loop_filter_c_arr[scan_data[1:2]];
            else
                lfc_val = loop_filter_c_arr[scan_data[1:2]];

            // LF Resistance : bits 3-7
            // valid values - 00000,00100,10000,10100,11000,11011,11100,11110
            if (((scan_data[3:7] == 5'b00000) || (scan_data[3:7] == 5'b00100)) || 
                ((scan_data[3:7] == 5'b10000) || (scan_data[3:7] == 5'b10100)) ||
                ((scan_data[3:7] == 5'b11000) || (scan_data[3:7] == 5'b11011)) ||
                ((scan_data[3:7] == 5'b11100) || (scan_data[3:7] == 5'b11110))
            )
            begin
                lfr_val =   (scan_data[3:7] == 5'b00000) ? "20" :
                            (scan_data[3:7] == 5'b00100) ? "16" :
                            (scan_data[3:7] == 5'b10000) ? "12" :
                            (scan_data[3:7] == 5'b10100) ? "8" :
                            (scan_data[3:7] == 5'b11000) ? "6" :
                            (scan_data[3:7] == 5'b11011) ? "4" : 
                            (scan_data[3:7] == 5'b11100) ? "2" : "1";
            end

            //VCO post scale value
            if (scan_data[8] === 1'b1)  // vco_post_scale = 1
            begin
                i_vco_max = i_vco_max_no_division/2;
                i_vco_min = i_vco_min_no_division/2;
                vco_cur = 1;
            end
            else
            begin
                i_vco_max = vco_max;
                i_vco_min = vco_min; 
                vco_cur = 2;
            end          

            // CP
            // Bit 8 : CRBYPASS
            // Bit 9-13 : unused
            // Bits 14-16 : all values are legal
            cp_curr_val = scan_data[14:16];

            // save old values for display info.
            for (i=0; i<=1; i=i+1)
            begin
                m_val_old[i] = m_val[i];
                n_val_old[i] = n_val[i];
                m_mode_val_old[i] = m_mode_val[i];
                n_mode_val_old[i] = n_mode_val[i];
            end
            for (i=0; i< num_output_cntrs; i=i+1)
            begin
                c_high_val_old[i] = c_high_val[i];
                c_low_val_old[i] = c_low_val[i];
                c_mode_val_old[i] = c_mode_val[i];
            end

            // M counter
            // 1. Mode - bypass (bit 17)
            if (scan_data[17] == 1'b1)
                m_mode_val[0] = "bypass";
            // 3. Mode - odd/even (bit 26)
            else if (scan_data[26] == 1'b1)
                m_mode_val[0] = "   odd";
            else
                m_mode_val[0] = "  even";
            // 2. High (bit 18-25)
                m_hi = scan_data[18:25];
            // 4. Low (bit 27-34)
                m_lo = scan_data[27:34]; 


            // N counter
            // 1. Mode - bypass (bit 35)
            if (scan_data[35] == 1'b1)
                n_mode_val[0] = "bypass";
            // 3. Mode - odd/even (bit 44)
            else if (scan_data[44] == 1'b1)
                n_mode_val[0] = "   odd";
            else
                n_mode_val[0] = "  even";
            
            // 2. High (bit 36-43)
                n_hi = scan_data[36:43];
            
            // 4. Low (bit 45-52)
                n_lo = scan_data[45:52]; 


            
//Update the current M and N counter values if the counters are NOT bypassed

if (m_mode_val[0] != "bypass")
m_val[0] = m_hi + m_lo;
if (n_mode_val[0] != "bypass")  
n_val[0] = n_hi + n_lo;
            


            // C counters (start bit 53) bit 1:mode(bypass),bit 2-9:high,bit 10:mode(odd/even),bit 11-18:low

            for (i = 0; i < num_output_cntrs; i = i + 1)
            begin
                // 1. Mode - bypass
                if (scan_data[53 + i*18 + 0] == 1'b1)
                        c_mode_val_tmp[i] = "bypass";
                // 3. Mode - odd/even
                else if (scan_data[53 + i*18 + 9] == 1'b1)
                    c_mode_val_tmp[i] = "   odd";
                else
                    c_mode_val_tmp[i] = "  even";
                    
                // 2. Hi
                for (j = 1; j <= 8; j = j + 1)
                    c_val[8-j] = scan_data[53 + i*18 + j];
                c_hval[i] = c_val[7:0];
                if (c_hval[i] !== 32'h00000000)
                    c_high_val_tmp[i] = c_hval[i];
                else
                    c_high_val_tmp[i] = 9'b100000000;
                // 4. Low 
                for (j = 10; j <= 17; j = j + 1)
                    c_val[17 - j] = scan_data[53 + i*18 + j]; 
                c_lval[i] = c_val[7:0];
                if (c_lval[i] !== 32'h00000000)
                    c_low_val_tmp[i] = c_lval[i];  
                else
                    c_low_val_tmp[i] = 9'b100000000; 
            end

            // Legality Checks
            
            if (m_mode_val[0] != "bypass")
            begin
            if ((m_hi !== m_lo) && (m_mode_val[0] != "   odd"))
            begin
                    reconfig_err = 1;
                    $display ("Warning : The M counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
            end
            else if (m_hi !== 8'b00000000)
            begin
                    // counter value
                    m_val_tmp[0] = m_hi + m_lo;
            end
            else
                m_val_tmp[0] =  9'b100000000; 
            end
            else
                m_val_tmp[0] = 8'b00000001;
                
            if (n_mode_val[0] != "bypass")
            begin
            if ((n_hi !== n_lo) && (n_mode_val[0] != "   odd"))
            begin
                    reconfig_err = 1;
                    $display ("Warning : The N counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
            end
            else if (n_hi !== 8'b00000000)
            begin
                    // counter value
                    n_val[0] = n_hi + n_lo;
            end
            else
                n_val[0] =  9'b100000000; 
            end
            else
                n_val[0] = 8'b00000001;
                           
                 

// TODO : Give warnings/errors in the following cases?
// 1. Illegal counter values (error)
// 2. Change of mode (warning)
// 3. Only 50% duty cycle allowed for M counter (odd mode - hi-lo=1,even - hi-lo=0)

        end
    end
    
    // Self reset on loss of lock
    assign reset_self = (l_self_reset_on_loss_lock == "on") ? ~pll_is_locked : 1'b0;

    always @(posedge reset_self)
    begin
        $display (" Note : %s PLL self reset due to loss of lock", family_name);
        $display ("Time: %0t  Instance: %m", $time);
    end
    
    // Phase shift on /o counters
    
    always @(schedule_vco or areset)
    begin
        sched_time = 0;
    
        for (i = 0; i <= 7; i=i+1)
            last_phase_shift[i] = phase_shift[i];
     
        cycle_to_adjust = 0;
        l_index = 1;
        m_times_vco_period = new_m_times_vco_period;
            
        // give appropriate messages
        // if areset was asserted
        if (areset === 1'b1 && areset_last_value !== areset)
        begin
            $display (" Note : %s PLL was reset", family_name);
            $display ("Time: %0t  Instance: %m", $time);
            // reset lock parameters
            pll_is_locked = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
            tap0_is_active = 0;
            for (x = 0; x <= 7; x=x+1)
                vco_tap[x] <= 1'b0;
        end
    
        // illegal value on areset
        if (areset === 1'bx && (areset_last_value === 1'b0 || areset_last_value === 1'b1))
        begin
            $display("Warning : Illegal value 'X' detected on ARESET input");
            $display ("Time: %0t  Instance: %m", $time);
        end
    
        if ((areset == 1'b1))
        begin
            pll_is_in_reset = 1;
            got_first_refclk = 0;
            got_second_refclk = 0;
        end
                            
        if ((schedule_vco !== schedule_vco_last_value) && (areset == 1'b1 || stop_vco == 1'b1))
        begin
   
            // drop VCO taps to 0
            for (i = 0; i <= 7; i=i+1)
            begin
                for (j = 0; j <= last_phase_shift[i] + 1; j=j+1)
                    vco_out[i] <= #(j) 1'b0;
                phase_shift[i] = 0;
                last_phase_shift[i] = 0;
            end
    
            // reset lock parameters
            pll_is_locked = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
    
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = 0;
            got_first_fbclk = 0;
            fbclk_time = 0;
            first_fbclk_time = 0;
            fbclk_period = 0;
    
            first_schedule = 1;
            vco_val = 0;
            vco_period_was_phase_adjusted = 0;
            phase_adjust_was_scheduled = 0;

            // reset all counter phase tap values to POF programmed values
            m_ph_val = m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
                c_ph_val[i] = c_ph_val_orig[i];
    
        end else if (areset === 1'b0 && stop_vco === 1'b0)
        begin
            // else note areset deassert time
            // note it as refclk_time to prevent false triggering
            // of stop_vco after areset
            if (areset === 1'b0 && areset_last_value === 1'b1 && pll_is_in_reset === 1'b1)
            begin
                refclk_time = $time;
                locked_tmp = 1'b0;
            end
            pll_is_in_reset = 0;
    
            // calculate loop_xplier : this will be different from m_val in ext. fbk mode
            loop_xplier = m_val[0];
            loop_initial = i_m_initial - 1;
            loop_ph = m_ph_val;
    
            // convert initial value to delay
            initial_delay = (loop_initial * m_times_vco_period)/loop_xplier;
    
            // convert loop ph_tap to delay
            rem = m_times_vco_period % loop_xplier;
            vco_per = m_times_vco_period/loop_xplier;
            if (rem != 0)
                vco_per = vco_per + 1;
            fbk_phase = (loop_ph * vco_per)/8;
    
            pull_back_M = initial_delay + fbk_phase;
    
            total_pull_back = pull_back_M;
            if (l_simulation_type == "timing")
                total_pull_back = total_pull_back + pll_compensation_delay;
    
            while (total_pull_back > refclk_period)
                total_pull_back = total_pull_back - refclk_period;
    
            if (total_pull_back > 0)
                offset = refclk_period - total_pull_back;
            else
                offset = 0;
    
            fbk_delay = total_pull_back - fbk_phase;
            if (fbk_delay < 0)
            begin
                offset = offset - fbk_phase;
                fbk_delay = total_pull_back;
            end
    
            // assign m_delay
            m_delay = fbk_delay;
    
            for (i = 1; i <= loop_xplier; i=i+1)
            begin
                // adjust cycles
                tmp_vco_per = m_times_vco_period/loop_xplier;
                if (rem != 0 && l_index <= rem)
                begin
                    tmp_rem = (loop_xplier * l_index) % rem;
                    cycle_to_adjust = (loop_xplier * l_index) / rem;
                    if (tmp_rem != 0)
                        cycle_to_adjust = cycle_to_adjust + 1;
                end
                if (cycle_to_adjust == i)
                begin
                    tmp_vco_per = tmp_vco_per + 1;
                    l_index = l_index + 1;
                end
    
                // calculate high and low periods
                high_time = tmp_vco_per/2;
                if (tmp_vco_per % 2 != 0)
                    high_time = high_time + 1;
                low_time = tmp_vco_per - high_time;
    
                // schedule the rising and falling egdes
                for (j=0; j<=1; j=j+1)
                begin
                    vco_val = ~vco_val;
                    if (vco_val == 1'b0)
                        sched_time = sched_time + high_time;
                    else
                        sched_time = sched_time + low_time;
    
                    // schedule taps with appropriate phase shifts
                    for (k = 0; k <= 7; k=k+1)
                    begin
                        phase_shift[k] = (k*tmp_vco_per)/8;
                        if (first_schedule)
                            vco_out[k] <= #(sched_time + phase_shift[k]) vco_val;
                        else
                            vco_out[k] <= #(sched_time + last_phase_shift[k]) vco_val;
                    end
                end
            end
            if (first_schedule)
            begin
                vco_val = ~vco_val;
                if (vco_val == 1'b0)
                    sched_time = sched_time + high_time;
                else
                    sched_time = sched_time + low_time;
                for (k = 0; k <= 7; k=k+1)
                begin
                    phase_shift[k] = (k*tmp_vco_per)/8;
                    vco_out[k] <= #(sched_time+phase_shift[k]) vco_val;
                end
                first_schedule = 0;
            end

            schedule_vco <= #(sched_time) ~schedule_vco;
            if (vco_period_was_phase_adjusted)
            begin
                m_times_vco_period = refclk_period;
                new_m_times_vco_period = refclk_period;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 1;
    
                tmp_vco_per = m_times_vco_period/loop_xplier;
                for (k = 0; k <= 7; k=k+1)
                    phase_shift[k] = (k*tmp_vco_per)/8;
            end
        end
    
        areset_last_value = areset;
        schedule_vco_last_value = schedule_vco;
    
    end

    // PFD enable
    always @(pfdena)
    begin
        if (pfdena === 1'b0)
        begin
            if (pll_is_locked)
                locked_tmp = 1'bx;
            pll_is_locked = 0;
            cycles_to_lock = 0;
            $display (" Note : PFDENA was deasserted");
            $display ("Time: %0t  Instance: %m", $time);
        end
        else if (pfdena === 1'b1 && pfdena_last_value === 1'b0)
        begin
            // PFD was disabled, now enabled again
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = $time;
        end
        pfdena_last_value = pfdena;
    end

    always @(negedge refclk or negedge fbclk)
    begin
        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    // Bypass lock detect
        
    always @(posedge refclk)
    begin
    if (test_bypass_lock_detect == "on")
        begin
            if (pfdena === 1'b1)
            begin
                    cycles_pfd_low = 0;
                    if (pfd_locked == 1'b0)
                    begin
                    if (cycles_pfd_high == lock_high)
                    begin
                        $display ("Note : %s PLL locked in test mode on PFD enable assert", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        pfd_locked <= 1'b1;
                    end
                    cycles_pfd_high = cycles_pfd_high + 1;
                        end
                end
            if (pfdena === 1'b0)
            begin
                    cycles_pfd_high = 0;
                    if (pfd_locked == 1'b1)
                    begin
                    if (cycles_pfd_low == lock_low)
                    begin
                        $display ("Note : %s PLL lost lock in test mode on PFD enable deassert", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        pfd_locked <= 1'b0;
                    end
                    cycles_pfd_low = cycles_pfd_low + 1;
                        end
                end
        end
    end
    
    always @(posedge scandone_tmp or posedge locked_tmp)
    begin
        if(scandone_tmp == 1)
            pll_has_just_been_reconfigured <= 1;
        else
            pll_has_just_been_reconfigured <= 0;
    end
    
    // VCO Frequency Range check
    always @(posedge refclk or posedge fbclk)
    begin
        if (refclk == 1'b1 && refclk_last_value !== refclk && areset === 1'b0)
        begin
            if (! got_first_refclk)
            begin
                got_first_refclk = 1;
            end else
            begin
                got_second_refclk = 1;
                refclk_period = $time - refclk_time;

                // check if incoming freq. will cause VCO range to be
                // exceeded
                if ((i_vco_max != 0 && i_vco_min != 0) && (pfdena === 1'b1) &&        
                    ((refclk_period/loop_xplier > i_vco_max) || 
                    (refclk_period/loop_xplier < i_vco_min)) ) 
                begin
                    if (pll_is_locked == 1'b1)
                    begin
                        if (refclk_period/loop_xplier > i_vco_max)
                        begin
                            $display ("Warning : Input clock freq. is over VCO range. %s PLL may lose lock", family_name);
                            vco_over = 1'b1;
                        end
                        if (refclk_period/loop_xplier < i_vco_min)
                        begin
                            $display ("Warning : Input clock freq. is under VCO range. %s PLL may lose lock", family_name);
                            vco_under = 1'b1;
                        end

                        $display ("Time: %0t  Instance: %m", $time);
                        if (inclk_out_of_range === 1'b1)
                        begin
                            // unlock
                            pll_is_locked = 0;
                            locked_tmp = 0;
                            cycles_to_lock = 0;
                            $display ("Note : %s PLL lost lock", family_name);
                            $display ("Time: %0t  Instance: %m", $time);
                            vco_period_was_phase_adjusted = 0;
                            phase_adjust_was_scheduled = 0;
                        end
                    end
                    else begin
                        if (no_warn == 1'b0)
                        begin
                            if (refclk_period/loop_xplier > i_vco_max)
                            begin
                                $display ("Warning : Input clock freq. is over VCO range. %s PLL may lose lock", family_name);
                                vco_over = 1'b1;
                            end
                            if (refclk_period/loop_xplier < i_vco_min)
                            begin
                                $display ("Warning : Input clock freq. is under VCO range. %s PLL may lose lock", family_name);
                                vco_under = 1'b1;
                            end
                            $display ("Time: %0t  Instance: %m", $time);
                            no_warn = 1'b1;
                        end
                    end
                    inclk_out_of_range = 1;
                end
                else begin
                    vco_over  = 1'b0;
                    vco_under = 1'b0;
                    inclk_out_of_range = 0;
                    no_warn = 1'b0;
                end

            end
            if (stop_vco == 1'b1)
            begin
                stop_vco = 0;
                schedule_vco = ~schedule_vco;
            end
            refclk_time = $time;
        end

        // Update M counter value on feedback clock edge
        
        if (fbclk == 1'b1 && fbclk_last_value !== fbclk)
        begin
            if (update_conf_latches === 1'b1)
            begin
                m_val[0] <= m_val_tmp[0];
                m_val[1] <= m_val_tmp[1];
            end
            if (!got_first_fbclk)
            begin
                got_first_fbclk = 1;
                first_fbclk_time = $time;
            end
            else
                fbclk_period = $time - fbclk_time;

            // need refclk_period here, so initialized to proper value above
            if ( ( ($time - refclk_time > 1.5 * refclk_period) && pfdena === 1'b1 && pll_is_locked === 1'b1) ||
                ( ($time - refclk_time > 5 * refclk_period) && (pfdena === 1'b1) && (pll_has_just_been_reconfigured == 0) ) ||
                ( ($time - refclk_time > 50 * refclk_period) && (pfdena === 1'b1) && (pll_has_just_been_reconfigured == 1) ) )
            begin
                stop_vco = 1;
                // reset
                got_first_refclk = 0;
                got_first_fbclk = 0;
                got_second_refclk = 0;
                if (pll_is_locked == 1'b1)
                begin
                    pll_is_locked = 0;
                    locked_tmp = 0;
                    $display ("Note : %s PLL lost lock due to loss of input clock or the input clock is not detected within the allowed time frame.", family_name);
                    if ((i_vco_max == 0) && (i_vco_min == 0))
                        $display ("Note : Please run timing simulation to check whether the input clock is operating within the supported VCO range or not.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                cycles_to_lock = 0;
                cycles_to_unlock = 0;
                first_schedule = 1;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 0;
                tap0_is_active = 0;
                for (x = 0; x <= 7; x=x+1)
                    vco_tap[x] <= 1'b0;
            end
            fbclk_time = $time;
        end
        
                
        // Core lock functionality
        
        if (got_second_refclk && pfdena === 1'b1 && (!inclk_out_of_range))
        begin
            // now we know actual incoming period
            if (abs(fbclk_time - refclk_time) <= lock_window || (got_first_fbclk && abs(refclk_period - abs(fbclk_time - refclk_time)) <= lock_window))
            begin
                // considered in phase
                if (cycles_to_lock == real_lock_high)
                begin
                    if (pll_is_locked === 1'b0)
                    begin
                        $display (" Note : %s PLL locked to incoming clock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    pll_is_locked = 1;
                    locked_tmp = 1;
                    cycles_to_unlock = 0;
                end
                // increment lock counter only if the second part of the above
                // time check is not true
                if (!(abs(refclk_period - abs(fbclk_time - refclk_time)) <= lock_window))
                begin
                    cycles_to_lock = cycles_to_lock + 1;
                end

                // adjust m_times_vco_period
                new_m_times_vco_period = refclk_period;

            end else
            begin
                // if locked, begin unlock
                if (pll_is_locked)
                begin
                    cycles_to_unlock = cycles_to_unlock + 1;
                    if (cycles_to_unlock == lock_low)
                    begin
                        pll_is_locked = 0;
                        locked_tmp = 0;
                        cycles_to_lock = 0;
                        $display ("Note : %s PLL lost lock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        vco_period_was_phase_adjusted = 0;
                        phase_adjust_was_scheduled = 0;
                        got_first_refclk = 0;
                        got_first_fbclk = 0;
                        got_second_refclk = 0;
                    end
                end
                if (abs(refclk_period - fbclk_period) <= 2)
                begin
                    // frequency is still good
                    if ($time == fbclk_time && (!phase_adjust_was_scheduled))
                    begin
                        if (abs(fbclk_time - refclk_time) > refclk_period/2)
                        begin
                            new_m_times_vco_period = abs(m_times_vco_period + (refclk_period - abs(fbclk_time - refclk_time)));
                            vco_period_was_phase_adjusted = 1;
                        end else
                        begin
                            new_m_times_vco_period = abs(m_times_vco_period - abs(fbclk_time - refclk_time));
                            vco_period_was_phase_adjusted = 1;
                        end
                    end
                end else
                begin
                    new_m_times_vco_period = refclk_period;
                    phase_adjust_was_scheduled = 0;
                end
            end
        end

        if (reconfig_err == 1'b1)
        begin
            locked_tmp = 0;
        end

        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    assign clk_tmp[0] = i_clk0_counter == "c0" ? c0_clk : i_clk0_counter == "c1" ? c1_clk : i_clk0_counter == "c2" ? c2_clk : i_clk0_counter == "c3" ? c3_clk : i_clk0_counter == "c4" ? c4_clk : i_clk0_counter == "c5" ? c5_clk : i_clk0_counter == "c6" ? c6_clk : i_clk0_counter == "c7" ? c7_clk : i_clk0_counter == "c8" ? c8_clk : i_clk0_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[1] = i_clk1_counter == "c0" ? c0_clk : i_clk1_counter == "c1" ? c1_clk : i_clk1_counter == "c2" ? c2_clk : i_clk1_counter == "c3" ? c3_clk : i_clk1_counter == "c4" ? c4_clk : i_clk1_counter == "c5" ? c5_clk : i_clk1_counter == "c6" ? c6_clk : i_clk1_counter == "c7" ? c7_clk : i_clk1_counter == "c8" ? c8_clk : i_clk1_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[2] = i_clk2_counter == "c0" ? c0_clk : i_clk2_counter == "c1" ? c1_clk : i_clk2_counter == "c2" ? c2_clk : i_clk2_counter == "c3" ? c3_clk : i_clk2_counter == "c4" ? c4_clk : i_clk2_counter == "c5" ? c5_clk : i_clk2_counter == "c6" ? c6_clk : i_clk2_counter == "c7" ? c7_clk : i_clk2_counter == "c8" ? c8_clk : i_clk2_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[3] = i_clk3_counter == "c0" ? c0_clk : i_clk3_counter == "c1" ? c1_clk : i_clk3_counter == "c2" ? c2_clk : i_clk3_counter == "c3" ? c3_clk : i_clk3_counter == "c4" ? c4_clk : i_clk3_counter == "c5" ? c5_clk : i_clk3_counter == "c6" ? c6_clk : i_clk3_counter == "c7" ? c7_clk : i_clk3_counter == "c8" ? c8_clk : i_clk3_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[4] = i_clk4_counter == "c0" ? c0_clk : i_clk4_counter == "c1" ? c1_clk : i_clk4_counter == "c2" ? c2_clk : i_clk4_counter == "c3" ? c3_clk : i_clk4_counter == "c4" ? c4_clk : i_clk4_counter == "c5" ? c5_clk : i_clk4_counter == "c6" ? c6_clk : i_clk4_counter == "c7" ? c7_clk : i_clk4_counter == "c8" ? c8_clk : i_clk4_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[5] = i_clk5_counter == "c0" ? c0_clk : i_clk5_counter == "c1" ? c1_clk : i_clk5_counter == "c2" ? c2_clk : i_clk5_counter == "c3" ? c3_clk : i_clk5_counter == "c4" ? c4_clk : i_clk5_counter == "c5" ? c5_clk : i_clk5_counter == "c6" ? c6_clk : i_clk5_counter == "c7" ? c7_clk : i_clk5_counter == "c8" ? c8_clk : i_clk5_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[6] = i_clk6_counter == "c0" ? c0_clk : i_clk6_counter == "c1" ? c1_clk : i_clk6_counter == "c2" ? c2_clk : i_clk6_counter == "c3" ? c3_clk : i_clk6_counter == "c4" ? c4_clk : i_clk6_counter == "c5" ? c5_clk : i_clk6_counter == "c6" ? c6_clk : i_clk6_counter == "c7" ? c7_clk : i_clk6_counter == "c8" ? c8_clk : i_clk6_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[7] = i_clk7_counter == "c0" ? c0_clk : i_clk7_counter == "c1" ? c1_clk : i_clk7_counter == "c2" ? c2_clk : i_clk7_counter == "c3" ? c3_clk : i_clk7_counter == "c4" ? c4_clk : i_clk7_counter == "c5" ? c5_clk : i_clk7_counter == "c6" ? c6_clk : i_clk7_counter == "c7" ? c7_clk : i_clk7_counter == "c8" ? c8_clk : i_clk7_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[8] = i_clk8_counter == "c0" ? c0_clk : i_clk8_counter == "c1" ? c1_clk : i_clk8_counter == "c2" ? c2_clk : i_clk8_counter == "c3" ? c3_clk : i_clk8_counter == "c4" ? c4_clk : i_clk8_counter == "c5" ? c5_clk : i_clk8_counter == "c6" ? c6_clk : i_clk8_counter == "c7" ? c7_clk : i_clk8_counter == "c8" ? c8_clk : i_clk8_counter == "c9" ? c9_clk : 1'b0;
    assign clk_tmp[9] = i_clk9_counter == "c0" ? c0_clk : i_clk9_counter == "c1" ? c1_clk : i_clk9_counter == "c2" ? c2_clk : i_clk9_counter == "c3" ? c3_clk : i_clk9_counter == "c4" ? c4_clk : i_clk9_counter == "c5" ? c5_clk : i_clk9_counter == "c6" ? c6_clk : i_clk9_counter == "c7" ? c7_clk : i_clk9_counter == "c8" ? c8_clk : i_clk9_counter == "c9" ? c9_clk : 1'b0;

assign clk_out_pfd[0] = (pfd_locked == 1'b1) ? clk_tmp[0] : 1'bx;
assign clk_out_pfd[1] = (pfd_locked == 1'b1) ? clk_tmp[1] : 1'bx;
assign clk_out_pfd[2] = (pfd_locked == 1'b1) ? clk_tmp[2] : 1'bx;
assign clk_out_pfd[3] = (pfd_locked == 1'b1) ? clk_tmp[3] : 1'bx;
assign clk_out_pfd[4] = (pfd_locked == 1'b1) ? clk_tmp[4] : 1'bx;
    assign clk_out_pfd[5] = (pfd_locked == 1'b1) ? clk_tmp[5] : 1'bx;
    assign clk_out_pfd[6] = (pfd_locked == 1'b1) ? clk_tmp[6] : 1'bx;
    assign clk_out_pfd[7] = (pfd_locked == 1'b1) ? clk_tmp[7] : 1'bx;
    assign clk_out_pfd[8] = (pfd_locked == 1'b1) ? clk_tmp[8] : 1'bx;
    assign clk_out_pfd[9] = (pfd_locked == 1'b1) ? clk_tmp[9] : 1'bx;

    assign clk_out[0] = (test_bypass_lock_detect == "on") ? clk_out_pfd[0] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[0] : 1'bx);
    assign clk_out[1] = (test_bypass_lock_detect == "on") ? clk_out_pfd[1] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[1] : 1'bx);
    assign clk_out[2] = (test_bypass_lock_detect == "on") ? clk_out_pfd[2] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[2] : 1'bx);
    assign clk_out[3] = (test_bypass_lock_detect == "on") ? clk_out_pfd[3] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[3] : 1'bx);
    assign clk_out[4] = (test_bypass_lock_detect == "on") ? clk_out_pfd[4] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[4] : 1'bx);
    assign clk_out[5] = (test_bypass_lock_detect == "on") ? clk_out_pfd[5] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[5] : 1'bx);
    assign clk_out[6] = (test_bypass_lock_detect == "on") ? clk_out_pfd[6] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[6] : 1'bx);
    assign clk_out[7] = (test_bypass_lock_detect == "on") ? clk_out_pfd[7] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[7] : 1'bx);
    assign clk_out[8] = (test_bypass_lock_detect == "on") ? clk_out_pfd[8] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[8] : 1'bx);
    assign clk_out[9] = (test_bypass_lock_detect == "on") ? clk_out_pfd[9] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[9] : 1'bx);

    // ACCELERATE OUTPUTS
    and (clk[0], 1'b1, clk_out[0]);
    and (clk[1], 1'b1, clk_out[1]);
    and (clk[2], 1'b1, clk_out[2]);
    and (clk[3], 1'b1, clk_out[3]);
    and (clk[4], 1'b1, clk_out[4]);
    and (clk[5], 1'b1, clk_out[5]);
    and (clk[6], 1'b1, clk_out[6]);
    and (clk[7], 1'b1, clk_out[7]);
    and (clk[8], 1'b1, clk_out[8]);
    and (clk[9], 1'b1, clk_out[9]);

    and (scandataout, 1'b1, scandata_out);
    and (scandone, 1'b1, scandone_tmp);

assign fbout = fbclk;
assign vcooverrange  = (vco_range_detector_high_bits == -1) ? 1'bz : vco_over;
assign vcounderrange = (vco_range_detector_low_bits == -1) ? 1'bz :vco_under;
assign phasedone = ~update_phase;

endmodule // MF_stratixiii_pll

// cycloneiii_msg
///////////////////////////////////////////////////////////////////////////////
//
// Module Name : cda_m_cntr
//
// Description : Simulation model for the M counter. This is the
//               loop feedback counter for the Cyclone III PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module cda_m_cntr   ( clk,
                            reset,
                            cout,
                            initial_value,
                            modulus,
                            time_delay);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] initial_value;
    input [31:0] modulus;
    input [31:0] time_delay;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
            cout_tmp <= tmp_cout;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'b1 && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
                cout_tmp <= #(time_delay) tmp_cout;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                    cout_tmp <= #(time_delay) tmp_cout;
                end
            end
        end
        end
        clk_last_value = clk;

//        cout_tmp <= #(time_delay) tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // cda_m_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : cda_n_cntr
//
// Description : Simulation model for the N counter. This is the
//               input clock divide counter for the Cyclone III PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module cda_n_cntr   ( clk,
                            reset,
                            cout,
                            modulus);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] modulus;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk == 1 && clk_last_value !== clk && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                end
            end
        end
        clk_last_value = clk;

    end

    assign cout = tmp_cout;

endmodule // cda_n_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : cda_scale_cntr
//
// Description : Simulation model for the output scale-down counters.
//               This is a common model for the C0-C9
//               output counters of the Cyclone III PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module cda_scale_cntr   ( clk,
                                reset,
                                cout,
                                high,
                                low,
                                initial_value,
                                mode,
                                ph_tap);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] high;
    input [31:0] low;
    input [31:0] initial_value;
    input [8*6:1] mode;
    input [31:0] ph_tap;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg init;
    integer count;
    integer output_shift_count;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 0;
        tmp_cout = 0;
        output_shift_count = 1;
    end

    always @(clk or reset)
    begin
        if (init !== 1'b1)
        begin
            clk_last_value = 0;
            init = 1'b1;
        end
        if (reset)
        begin
            count = 1;
            output_shift_count = 1;
            tmp_cout = 0;
            first_rising_edge = 0;
        end
        else if (clk_last_value !== clk)
        begin
            if (mode == "   off")
                tmp_cout = 0;
            else if (mode == "bypass")
            begin
                tmp_cout = clk;
                first_rising_edge = 1;
            end
            else if (first_rising_edge == 0)
            begin
                if (clk == 1)
                begin
                    if (output_shift_count == initial_value)
                    begin
                        tmp_cout = clk;
                        first_rising_edge = 1;
                    end
                    else
                        output_shift_count = output_shift_count + 1;
                end
            end
            else if (output_shift_count < initial_value)
            begin
                if (clk == 1)
                    output_shift_count = output_shift_count + 1;
            end
            else
            begin
                count = count + 1;
                if (mode == "  even" && (count == (high*2) + 1))
                    tmp_cout = 0;
                else if (mode == "   odd" && (count == (high*2)))
                    tmp_cout = 0;
                else if (count == (high + low)*2 + 1)
                begin
                    tmp_cout = 1;
                    count = 1;        // reset count
                end
            end
        end
        clk_last_value = clk;
        cout_tmp <= tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // cda_scale_cntr


//////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_cycloneiii_pll
//
// Description : Behavioral model for CycloneIII pll.
// 
// Limitations : Does not support Spread Spectrum and Bandwidth.
//
// Outputs     : Up to 10 output clocks, each defined by its own set of
//               parameters. Locked output (active high) indicates when the
//               PLL locks. clkbad and activeclock are used for
//               clock switchover to indicate which input clock has gone
//               bad, when the clock switchover initiates and which input
//               clock is being used as the reference, respectively.
//               scandataout is the data output of the serial scan chain.
//
// New Features : The list below outlines key new features in Cyclone III:
//                1. Dynamic Phase Reconfiguration
//                2. Dynamic PLL Reconfiguration (different protocol)
//                3. More output counters
//////////////////////////////////////////////////////////////////////////////

`timescale 1 ps/1 ps
`define CYCIII_PLL_WORD_LENGTH 18

module MF_cycloneiii_pll (inclk,
                    fbin,
                    fbout,
                    clkswitch,
                    areset,
                    pfdena,
                    scanclk,
                    scandata,
                    scanclkena,
                    configupdate,
                    clk,
                    phasecounterselect,
                    phaseupdown,
                    phasestep,
                    clkbad,
                    activeclock,
                    locked,
                    scandataout,
                    scandone,
                    phasedone,
                    vcooverrange,
                    vcounderrange
                    );

    parameter operation_mode                       = "normal";
    parameter pll_type                             = "auto"; // auto,fast(left_right),enhanced(top_bottom)
    parameter compensate_clock                     = "clock0";


    parameter inclk0_input_frequency               = 0;
    parameter inclk1_input_frequency               = 0;

    parameter self_reset_on_loss_lock        = "off";
    parameter switch_over_type                     = "auto";

    parameter switch_over_counter                  = 1;
    parameter enable_switch_over_counter           = "off";

    parameter bandwidth                            = 0;
    parameter bandwidth_type                       = "auto";
    parameter use_dc_coupling                      = "false";

    parameter lock_high = 0; // 0 .. 4095
    parameter lock_low = 0;  // 0 .. 7
    parameter lock_window_ui = "0.05"; // "0.05", "0.1", "0.15", "0.2"
    parameter test_bypass_lock_detect              = "off";
    
    parameter clk0_output_frequency                = 0;
    parameter clk0_multiply_by                     = 0;
    parameter clk0_divide_by                       = 0;
    parameter clk0_phase_shift                     = "0";
    parameter clk0_duty_cycle                      = 50;

    parameter clk1_output_frequency                = 0;
    parameter clk1_multiply_by                     = 0;
    parameter clk1_divide_by                       = 0;
    parameter clk1_phase_shift                     = "0";
    parameter clk1_duty_cycle                      = 50;

    parameter clk2_output_frequency                = 0;
    parameter clk2_multiply_by                     = 0;
    parameter clk2_divide_by                       = 0;
    parameter clk2_phase_shift                     = "0";
    parameter clk2_duty_cycle                      = 50;

    parameter clk3_output_frequency                = 0;
    parameter clk3_multiply_by                     = 0;
    parameter clk3_divide_by                       = 0;
    parameter clk3_phase_shift                     = "0";
    parameter clk3_duty_cycle                      = 50;

    parameter clk4_output_frequency                = 0;
    parameter clk4_multiply_by                     = 0;
    parameter clk4_divide_by                       = 0;
    parameter clk4_phase_shift                     = "0";
    parameter clk4_duty_cycle                      = 50;

    
    
    
    
    

    parameter pfd_min                              = 0;
    parameter pfd_max                              = 0;
    parameter vco_min                              = 0;
    parameter vco_max                              = 0;
    parameter vco_center                           = 0;

    // ADVANCED USE PARAMETERS
    parameter m_initial = 1;
    parameter m = 0;
    parameter n = 1;

    parameter c0_high = 1;
    parameter c0_low = 1;
    parameter c0_initial = 1;
    parameter c0_mode = "bypass";
    parameter c0_ph = 0;

    parameter c1_high = 1;
    parameter c1_low = 1;
    parameter c1_initial = 1;
    parameter c1_mode = "bypass";
    parameter c1_ph = 0;

    parameter c2_high = 1;
    parameter c2_low = 1;
    parameter c2_initial = 1;
    parameter c2_mode = "bypass";
    parameter c2_ph = 0;

    parameter c3_high = 1;
    parameter c3_low = 1;
    parameter c3_initial = 1;
    parameter c3_mode = "bypass";
    parameter c3_ph = 0;

    parameter c4_high = 1;
    parameter c4_low = 1;
    parameter c4_initial = 1;
    parameter c4_mode = "bypass";
    parameter c4_ph = 0;

    
    
    
    
    

    parameter m_ph = 0;

    parameter clk0_counter = "unused";
    parameter clk1_counter = "unused";
    parameter clk2_counter = "unused";
    parameter clk3_counter = "unused";
    parameter clk4_counter = "unused";

    parameter c1_use_casc_in = "off";
    parameter c2_use_casc_in = "off";
    parameter c3_use_casc_in = "off";
    parameter c4_use_casc_in = "off";

    parameter m_test_source  = -1;
    parameter c0_test_source = -1;
    parameter c1_test_source = -1;
    parameter c2_test_source = -1;
    parameter c3_test_source = -1;
    parameter c4_test_source = -1;

    parameter vco_multiply_by = 0;
    parameter vco_divide_by = 0;
    parameter vco_post_scale = 1; // 1 .. 2
    parameter vco_frequency_control = "auto";
    parameter vco_phase_shift_step = 0;
    
    parameter charge_pump_current = 10;
    parameter loop_filter_r = "1.0";    // "1.0", "2.0", "4.0", "6.0", "8.0", "12.0", "16.0", "20.0"
    parameter loop_filter_c = 0;        // 0 , 2 , 4

    parameter pll_compensation_delay = 0;
    parameter simulation_type = "functional";

// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter down_spread                          = "0.0";
    parameter lock_c = 4;

    parameter sim_gate_lock_device_behavior        = "off";

    parameter clk0_phase_shift_num = 0;
    parameter clk1_phase_shift_num = 0;
    parameter clk2_phase_shift_num = 0;
    parameter clk3_phase_shift_num = 0;
    parameter clk4_phase_shift_num = 0;
    parameter family_name = "StratixIII";

    parameter clk0_use_even_counter_mode = "off";
    parameter clk1_use_even_counter_mode = "off";
    parameter clk2_use_even_counter_mode = "off";
    parameter clk3_use_even_counter_mode = "off";
    parameter clk4_use_even_counter_mode = "off";

    parameter clk0_use_even_counter_value = "off";
    parameter clk1_use_even_counter_value = "off";
    parameter clk2_use_even_counter_value = "off";
    parameter clk3_use_even_counter_value = "off";
    parameter clk4_use_even_counter_value = "off";

    // TEST ONLY
    
    parameter init_block_reset_a_count = 1;
    parameter init_block_reset_b_count = 1;

// SIMULATION_ONLY_PARAMETERS_END
    
// LOCAL_PARAMETERS_BEGIN

    parameter phase_counter_select_width = 3;
    parameter lock_window = 5;
    parameter inclk0_freq = inclk0_input_frequency;
    parameter inclk1_freq = inclk1_input_frequency;
   
parameter charge_pump_current_bits = 0;
parameter lock_window_ui_bits = 0;
parameter loop_filter_c_bits = 0;
parameter loop_filter_r_bits = 0;
parameter test_counter_c0_delay_chain_bits = 0;
parameter test_counter_c1_delay_chain_bits = 0;
parameter test_counter_c2_delay_chain_bits = 0;
parameter test_counter_c3_delay_chain_bits = 0;
parameter test_counter_c4_delay_chain_bits = 0;
parameter test_counter_c5_delay_chain_bits = 0;
parameter test_counter_m_delay_chain_bits = 0;
parameter test_counter_n_delay_chain_bits = 0;
parameter test_feedback_comp_delay_chain_bits = 0;
parameter test_input_comp_delay_chain_bits = 0;
parameter test_volt_reg_output_mode_bits = 0;
parameter test_volt_reg_output_voltage_bits = 0;
parameter test_volt_reg_test_mode = "false";
parameter vco_range_detector_high_bits = -1;
parameter vco_range_detector_low_bits = -1;
parameter scan_chain_mif_file = ""; 


parameter auto_settings = "true";

// LOCAL_PARAMETERS_END
 
    // INPUT PORTS
    input [1:0] inclk;
    input fbin;
    input clkswitch;
    input areset;
    input pfdena;
    input [phase_counter_select_width - 1:0] phasecounterselect;
    input phaseupdown;
    input phasestep;
    input scanclk;
    input scanclkena;
    input scandata;
    input configupdate;

    // OUTPUT PORTS
    output [4:0] clk;
    output [1:0] clkbad;
    output activeclock;
    output locked;
    output scandataout;
    output scandone;
    output fbout;
    output phasedone;
    output vcooverrange;
    output vcounderrange;
    
        

    // INTERNAL VARIABLES AND NETS
    reg [8*6:1] clk_num[0:4];
    integer scan_chain_length;
    integer i;
    integer j;
    integer k;
    integer x;
    integer y;
    integer l_index;
    integer gate_count;
    integer egpp_offset;
    integer sched_time;
    integer delay_chain;
    integer low;
    integer high;
    integer initial_delay;
    integer fbk_phase;
    integer fbk_delay;
    integer phase_shift[0:7];
    integer last_phase_shift[0:7];

    integer m_times_vco_period;
    integer new_m_times_vco_period;
    integer refclk_period;
    integer fbclk_period;
    integer high_time;
    integer low_time;
    integer my_rem;
    integer tmp_rem;
    integer rem;
    integer tmp_vco_per;
    integer vco_per;
    integer offset;
    integer temp_offset;
    integer cycles_to_lock;
    integer cycles_to_unlock;
    integer loop_xplier;
    integer loop_initial;
    integer loop_ph;
    integer cycle_to_adjust;
    integer total_pull_back;
    integer pull_back_M;

    time    fbclk_time;
    time    first_fbclk_time;
    time    refclk_time;

    reg switch_clock;

    reg [31:0] real_lock_high;

    reg got_first_refclk;
    reg got_second_refclk;
    reg got_first_fbclk;
    reg refclk_last_value;
    reg fbclk_last_value;
    reg inclk_last_value;
    reg pll_is_locked;
    reg locked_tmp;
    reg areset_last_value;
    reg pfdena_last_value;
    reg inclk_out_of_range;
    reg schedule_vco_last_value;
    
    // Test bypass lock detect
    reg pfd_locked;
    integer cycles_pfd_low, cycles_pfd_high;

    reg gate_out;
    reg vco_val;

    reg [31:0] m_initial_val;
    reg [31:0] m_val[0:1];
    reg [31:0] n_val[0:1];
    reg [31:0] m_delay;
    reg [8*6:1] m_mode_val[0:1];
    reg [8*6:1] n_mode_val[0:1];

    reg [31:0] c_high_val[0:9];
    reg [31:0] c_low_val[0:9];
    reg [8*6:1] c_mode_val[0:9];
    reg [31:0] c_initial_val[0:9];
    integer c_ph_val[0:9];

    reg [31:0] c_val; // placeholder for c_high,c_low values

    // VCO Frequency Range control
    reg vco_over, vco_under;
   
    // temporary registers for reprogramming
    integer c_ph_val_tmp[0:9];
    reg [31:0] c_high_val_tmp[0:9];
    reg [31:0] c_hval[0:9];
    reg [31:0] c_low_val_tmp[0:9];
    reg [31:0] c_lval[0:9];
    reg [8*6:1] c_mode_val_tmp[0:9];

    // hold registers for reprogramming
    integer c_ph_val_hold[0:9];
    reg [31:0] c_high_val_hold[0:9];
    reg [31:0] c_low_val_hold[0:9];
    reg [8*6:1] c_mode_val_hold[0:9];

    // old values
    reg [31:0] m_val_old[0:1];
    reg [31:0] m_val_tmp[0:1];
    reg [31:0] n_val_old[0:1];
    reg [8*6:1] m_mode_val_old[0:1];
    reg [8*6:1] n_mode_val_old[0:1];
    reg [31:0] c_high_val_old[0:9];
    reg [31:0] c_low_val_old[0:9];
    reg [8*6:1] c_mode_val_old[0:9];
    integer c_ph_val_old[0:9];
    integer   m_ph_val_old;
    integer   m_ph_val_tmp;

    integer cp_curr_old;
    integer cp_curr_val;
    integer lfc_old;
    integer lfc_val;
    integer vco_cur;
    integer vco_old;
    reg [9*8:1] lfr_val;
    reg [9*8:1] lfr_old;
    reg [1:2] lfc_val_bit_setting, lfc_val_old_bit_setting;
    reg vco_val_bit_setting, vco_val_old_bit_setting;
    reg [3:7] lfr_val_bit_setting, lfr_val_old_bit_setting;
    reg [14:16] cp_curr_bit_setting, cp_curr_old_bit_setting;
    
    // Setting on  - display real values
    // Setting off - display only bits
    reg pll_reconfig_display_full_setting;

    reg [7:0] m_hi;
    reg [7:0] m_lo;
    reg [7:0] n_hi;
    reg [7:0] n_lo;

    // ph tap orig values (POF)
    integer c_ph_val_orig[0:9];
    integer m_ph_val_orig;

    reg schedule_vco;
    reg stop_vco;
    reg inclk_n;
    reg inclk_man;
    reg inclk_es;

    reg [7:0] vco_out;
    reg [7:0] vco_tap;
    reg [7:0] vco_out_last_value;
    reg [7:0] vco_tap_last_value;
    wire inclk_c0;
    wire inclk_c1;
    wire inclk_c2;
    wire inclk_c3;
    wire inclk_c4;
    
    wire  inclk_c0_from_vco;
    wire  inclk_c1_from_vco;
    wire  inclk_c2_from_vco;
    wire  inclk_c3_from_vco;
    wire  inclk_c4_from_vco;
    
    wire  inclk_m_from_vco;

    wire inclk_m;
    wire [4:0] clk_tmp, clk_out_pfd;


    wire [4:0] clk_out;

    wire c0_clk;
    wire c1_clk;
    wire c2_clk;
    wire c3_clk;
    wire c4_clk;

    reg first_schedule;

    reg vco_period_was_phase_adjusted;
    reg phase_adjust_was_scheduled;

    wire refclk;
    wire fbclk;
    
    wire pllena_reg;
    wire test_mode_inclk;
 
    // Self Reset
    wire reset_self;

    // Clock Switchover
    reg clk0_is_bad;
    reg clk1_is_bad;
    reg inclk0_last_value;
    reg inclk1_last_value;
    reg other_clock_value;
    reg other_clock_last_value;
    reg primary_clk_is_bad;
    reg current_clk_is_bad;
    reg external_switch;
    reg active_clock;
    reg got_curr_clk_falling_edge_after_clkswitch;

    integer clk0_count;
    integer clk1_count;
    integer switch_over_count;

    wire scandataout_tmp;
    reg scandata_in, scandata_out; // hold scan data in negative-edge triggered ff (on either side on chain)
    reg scandone_tmp;
    reg initiate_reconfig;
    integer quiet_time;
    integer slowest_clk_old;
    integer slowest_clk_new;

    reg reconfig_err;
    reg error;
    time    scanclk_last_rising_edge;
    time    scanread_active_edge;
    reg got_first_scanclk;
    reg got_first_gated_scanclk;
    reg gated_scanclk;
    integer scanclk_period;
    reg scanclk_last_value;
    wire update_conf_latches;
    reg  update_conf_latches_reg;
    reg [-1:142]  scan_data;
    reg scanclkena_reg; // register scanclkena on negative edge of scanclk
    reg c0_rising_edge_transfer_done;
    reg c1_rising_edge_transfer_done;
    reg c2_rising_edge_transfer_done;
    reg c3_rising_edge_transfer_done;
    reg c4_rising_edge_transfer_done;
    reg scanread_setup_violation;
    integer index;
    integer scanclk_cycles;
    reg d_msg;

    integer num_output_cntrs;
    reg no_warn;
    
    // Phase reconfig
    
    reg [2:0] phasecounterselect_reg;
    reg phaseupdown_reg;
    reg phasestep_reg;
    integer select_counter;
    integer phasestep_high_count;
    reg update_phase;
    

// LOCAL_PARAMETERS_BEGIN

    parameter SCAN_CHAIN = 144;
    parameter GPP_SCAN_CHAIN  = 234;
    parameter FAST_SCAN_CHAIN = 180;
    // primary clk is always inclk0
    parameter num_phase_taps = 8;

// LOCAL_PARAMETERS_END


    // internal variables for scaling of multiply_by and divide_by values
    integer i_clk0_mult_by;
    integer i_clk0_div_by;
    integer i_clk1_mult_by;
    integer i_clk1_div_by;
    integer i_clk2_mult_by;
    integer i_clk2_div_by;
    integer i_clk3_mult_by;
    integer i_clk3_div_by;
    integer i_clk4_mult_by;
    integer i_clk4_div_by;
    integer i_clk5_mult_by;
    integer i_clk5_div_by;
    integer i_clk6_mult_by;
    integer i_clk6_div_by;
    integer i_clk7_mult_by;
    integer i_clk7_div_by;
    integer i_clk8_mult_by;
    integer i_clk8_div_by;
    integer i_clk9_mult_by;
    integer i_clk9_div_by;
    integer max_d_value;
    integer new_multiplier;

    // internal variables for storing the phase shift number.(used in lvds mode only)
    integer i_clk0_phase_shift;
    integer i_clk1_phase_shift;
    integer i_clk2_phase_shift;
    integer i_clk3_phase_shift;
    integer i_clk4_phase_shift;

    // user to advanced internal signals

    integer   i_m_initial;
    integer   i_m;
    integer   i_n;
    integer   i_c_high[0:9];
    integer   i_c_low[0:9];
    integer   i_c_initial[0:9];
    integer   i_c_ph[0:9];
    reg       [8*6:1] i_c_mode[0:9];

    integer   i_vco_min;
    integer   i_vco_max;
    integer   i_vco_min_no_division;
    integer   i_vco_max_no_division;
    integer   i_vco_center;
    integer   i_pfd_min;
    integer   i_pfd_max;
    integer   i_m_ph;
    integer   m_ph_val;
    reg [8*2:1] i_clk4_counter;
    reg [8*2:1] i_clk3_counter;
    reg [8*2:1] i_clk2_counter;
    reg [8*2:1] i_clk1_counter;
    reg [8*2:1] i_clk0_counter;
    integer   i_charge_pump_current;
    integer   i_loop_filter_r;
    integer   max_neg_abs;
    integer   output_count;
    integer   new_divisor;

    integer loop_filter_c_arr[0:3];
    integer fpll_loop_filter_c_arr[0:3];
    integer charge_pump_curr_arr[0:15];

    reg pll_in_test_mode;
    reg pll_is_in_reset;
    reg pll_has_just_been_reconfigured;

    // uppercase to lowercase parameter values
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_operation_mode;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_pll_type;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_compensate_clock;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_scan_chain;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_switch_over_type;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_bandwidth_type;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_simulation_type;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_sim_gate_lock_device_behavior;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_vco_frequency_control;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_enable_switch_over_counter;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] l_self_reset_on_loss_lock;
    


    integer current_clock;
    integer current_clock_man;
    reg is_fast_pll;
    reg ic1_use_casc_in;
    reg ic2_use_casc_in;
    reg ic3_use_casc_in;
    reg ic4_use_casc_in;

    reg init;
    reg tap0_is_active;

    real inclk0_period, last_inclk0_period,inclk1_period, last_inclk1_period;
    real last_inclk0_edge,last_inclk1_edge,diff_percent_period;
    reg first_inclk0_edge_detect,first_inclk1_edge_detect;



    // finds the closest integer fraction of a given pair of numerator and denominator. 
    task find_simple_integer_fraction;
        input numerator;
        input denominator;
        input max_denom;
        output fraction_num; 
        output fraction_div; 
        parameter max_iter = 20;
        
        integer numerator;
        integer denominator;
        integer max_denom;
        integer fraction_num; 
        integer fraction_div; 
        
        integer quotient_array[max_iter-1:0];
        integer int_loop_iter;
        integer int_quot;
        integer m_value;
        integer d_value;
        integer old_m_value;
        integer swap;

        integer loop_iter;
        integer num;
        integer den;
        integer i_max_iter;

    begin      
        loop_iter = 0;
        num = (numerator == 0) ? 1 : numerator;
        den = (denominator == 0) ? 1 : denominator;
        i_max_iter = max_iter;
       
        while (loop_iter < i_max_iter)
        begin
            int_quot = num / den;
            quotient_array[loop_iter] = int_quot;
            num = num - (den*int_quot);
            loop_iter=loop_iter+1;
            
            if ((num == 0) || (max_denom != -1) || (loop_iter == i_max_iter)) 
            begin
                // calculate the numerator and denominator if there is a restriction on the
                // max denom value or if the loop is ending
                m_value = 0;
                d_value = 1;
                // get the rounded value at this stage for the remaining fraction
                if (den != 0)
                begin
                    m_value = (2*num/den);
                end
                // calculate the fraction numerator and denominator at this stage
                for (int_loop_iter = loop_iter-1; int_loop_iter >= 0; int_loop_iter=int_loop_iter-1)
                begin
                    if (m_value == 0)
                    begin
                        m_value = quotient_array[int_loop_iter];
                        d_value = 1;
                    end
                    else
                    begin
                        old_m_value = m_value;
                        m_value = quotient_array[int_loop_iter]*m_value + d_value;
                        d_value = old_m_value;
                    end
                end
                // if the denominator is less than the maximum denom_value or if there is no restriction save it
                if ((d_value <= max_denom) || (max_denom == -1))
                begin
                    fraction_num = m_value;
                    fraction_div = d_value;
                end
                // end the loop if the denomitor has overflown or the numerator is zero (no remainder during this round)
                if (((d_value > max_denom) && (max_denom != -1)) || (num == 0))
                begin
                    i_max_iter = loop_iter;
                end
            end
            // swap the numerator and denominator for the next round
            swap = den;
            den = num;
            num = swap;
        end
    end
    endtask // find_simple_integer_fraction

    // get the absolute value
    function integer abs;
    input value;
    integer value;
    begin
        if (value < 0)
            abs = value * -1;
        else abs = value;
    end
    endfunction

    // find twice the period of the slowest clock
    function integer slowest_clk;
    input C0, C0_mode, C1, C1_mode, C2, C2_mode, C3, C3_mode, C4, C4_mode, C5, C5_mode, C6, C6_mode, C7, C7_mode, C8, C8_mode, C9, C9_mode, refclk, m_mod;
    integer C0, C1, C2, C3, C4, C5, C6, C7, C8, C9;
    reg [8*6:1] C0_mode, C1_mode, C2_mode, C3_mode, C4_mode, C5_mode, C6_mode, C7_mode, C8_mode, C9_mode;
    integer refclk;
    reg [31:0] m_mod;
    integer max_modulus;
    begin
        max_modulus = 1;
        if (C0_mode != "bypass" && C0_mode != "   off")
            max_modulus = C0;
        if (C1 > max_modulus && C1_mode != "bypass" && C1_mode != "   off")
            max_modulus = C1;
        if (C2 > max_modulus && C2_mode != "bypass" && C2_mode != "   off")
            max_modulus = C2;
        if (C3 > max_modulus && C3_mode != "bypass" && C3_mode != "   off")
            max_modulus = C3;
        if (C4 > max_modulus && C4_mode != "bypass" && C4_mode != "   off")
            max_modulus = C4;
        if (C5 > max_modulus && C5_mode != "bypass" && C5_mode != "   off")
            max_modulus = C5;
        if (C6 > max_modulus && C6_mode != "bypass" && C6_mode != "   off")
            max_modulus = C6;
        if (C7 > max_modulus && C7_mode != "bypass" && C7_mode != "   off")
            max_modulus = C7;
        if (C8 > max_modulus && C8_mode != "bypass" && C8_mode != "   off")
            max_modulus = C8;
        if (C9 > max_modulus && C9_mode != "bypass" && C9_mode != "   off")
            max_modulus = C9;

        slowest_clk = (refclk * max_modulus *2 / m_mod);
    end
    endfunction

    // count the number of digits in the given integer
    function integer count_digit;
    input X;
    integer X;
    integer count, result;
    begin
        count = 0;
        result = X;
        while (result != 0)
        begin
            result = (result / 10);
            count = count + 1;
        end
        
        count_digit = count;
    end
    endfunction

    // reduce the given huge number(X) to Y significant digits
    function integer scale_num;
    input X, Y;
    integer X, Y;
    integer count;
    integer fac_ten, lc;
    begin
        fac_ten = 1;
        count = count_digit(X);
        
        for (lc = 0; lc < (count-Y); lc = lc + 1)
            fac_ten = fac_ten * 10;

        scale_num = (X / fac_ten);
    end
    endfunction

    // find the greatest common denominator of X and Y
    function integer gcd;
    input X,Y;
    integer X,Y;
    integer L, S, R, G;
    begin
        if (X < Y) // find which is smaller.
        begin
            S = X;
            L = Y;
        end
        else
        begin
            S = Y;
            L = X;
        end

        R = S;
        while ( R > 1)
        begin
            S = L;
            L = R;
            R = S % L;  // divide bigger number by smaller.
                        // remainder becomes smaller number.
        end
        if (R == 0)     // if evenly divisible then L is gcd else it is 1.
            G = L;
        else
            G = R;
        gcd = G;
    end
    endfunction

    // find the least common multiple of A1 to A10
    function integer lcm;
    input A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer M1, M2, M3, M4, M5 , M6, M7, M8, M9, R;
    begin
        M1 = (A1 * A2)/gcd(A1, A2);
        M2 = (M1 * A3)/gcd(M1, A3);
        M3 = (M2 * A4)/gcd(M2, A4);
        M4 = (M3 * A5)/gcd(M3, A5);
        M5 = (M4 * A6)/gcd(M4, A6);
        M6 = (M5 * A7)/gcd(M5, A7);
        M7 = (M6 * A8)/gcd(M6, A8);
        M8 = (M7 * A9)/gcd(M7, A9);
        M9 = (M8 * A10)/gcd(M8, A10);
        if (M9 < 3)
            R = 10;
        else if ((M9 <= 10) && (M9 >= 3))
            R = 4 * M9;
        else if (M9 > 1000)
            R = scale_num(M9, 3);
        else
            R = M9;
        lcm = R; 
    end
    endfunction

    // find the M and N values for Manual phase based on the following 5 criterias:
    // 1. The PFD frequency (i.e. Fin / N) must be in the range 5 MHz to 720 MHz
    // 2. The VCO frequency (i.e. Fin * M / N) must be in the range 300 MHz to 1300 MHz
    // 3. M is less than 512
    // 4. N is less than 512
    // 5. It's the smallest M/N which satisfies all the above constraints, and is within 2ps
    //    of the desired vco-phase-shift-step
    task find_m_and_n_4_manual_phase;
        input inclock_period;
        input vco_phase_shift_step;
        input clk0_mult, clk1_mult, clk2_mult, clk3_mult, clk4_mult;
        input clk5_mult, clk6_mult, clk7_mult, clk8_mult, clk9_mult;
        input clk0_div,  clk1_div,  clk2_div,  clk3_div,  clk4_div;
        input clk5_div,  clk6_div,  clk7_div,  clk8_div,  clk9_div;
        input clk0_used,  clk1_used,  clk2_used,  clk3_used,  clk4_used;
        input clk5_used,  clk6_used,  clk7_used,  clk8_used,  clk9_used;
        output m; 
        output n; 

        parameter max_m = 511;
        parameter max_n = 511;
        parameter max_pfd = 720;
        parameter min_pfd = 5;
        parameter max_vco = 1600; // max vco frequency. (in mHz)
        parameter min_vco = 300;  // min vco frequency. (in mHz)
        parameter max_offset = 0.004;
        
        reg[160:1] clk0_used,  clk1_used,  clk2_used,  clk3_used,  clk4_used;
        reg[160:1] clk5_used,  clk6_used,  clk7_used,  clk8_used,  clk9_used;
        
        integer inclock_period;
        integer vco_phase_shift_step;
        integer clk0_mult, clk1_mult, clk2_mult, clk3_mult, clk4_mult;
        integer clk5_mult, clk6_mult, clk7_mult, clk8_mult, clk9_mult;
        integer clk0_div,  clk1_div,  clk2_div,  clk3_div,  clk4_div;
        integer clk5_div,  clk6_div,  clk7_div,  clk8_div,  clk9_div;
        integer m; 
        integer n;
        integer pre_m;
        integer pre_n;
        integer m_out;
        integer n_out;
        integer closest_vco_step_value;
        
        integer vco_period;
        integer pfd_freq;
        integer vco_freq;
        integer vco_ps_step_value;
        real    clk0_div_factor_real;
        real    clk1_div_factor_real;
        real    clk2_div_factor_real;
        real    clk3_div_factor_real;
        real    clk4_div_factor_real;
        real    clk5_div_factor_real;
        real    clk6_div_factor_real;
        real    clk7_div_factor_real;
        real    clk8_div_factor_real;
        real    clk9_div_factor_real;
        real    clk0_div_factor_diff;
        real    clk1_div_factor_diff;
        real    clk2_div_factor_diff;
        real    clk3_div_factor_diff;
        real    clk4_div_factor_diff;
        real    clk5_div_factor_diff;
        real    clk6_div_factor_diff;
        real    clk7_div_factor_diff;
        real    clk8_div_factor_diff;
        real    clk9_div_factor_diff;
        integer clk0_div_factor_int;
        integer clk1_div_factor_int;
        integer clk2_div_factor_int;
        integer clk3_div_factor_int;
        integer clk4_div_factor_int;
        integer clk5_div_factor_int;
        integer clk6_div_factor_int;
        integer clk7_div_factor_int;
        integer clk8_div_factor_int;
        integer clk9_div_factor_int;
    begin

        vco_period = vco_phase_shift_step * 8;

        pre_m = 0;
        pre_n = 0;
        closest_vco_step_value = 0;

        begin : LOOP_1
                for (n_out = 1; n_out < max_n; n_out = n_out +1)
                begin
                    for (m_out = 1; m_out < max_m; m_out = m_out +1)
                    begin
                        clk0_div_factor_real = (clk0_div * m_out * 1.0 ) / (clk0_mult * n_out);
                        clk1_div_factor_real = (clk1_div * m_out * 1.0) / (clk1_mult * n_out);
                        clk2_div_factor_real = (clk2_div * m_out * 1.0) / (clk2_mult * n_out);
                        clk3_div_factor_real = (clk3_div * m_out * 1.0) / (clk3_mult * n_out);
                        clk4_div_factor_real = (clk4_div * m_out * 1.0) / (clk4_mult * n_out);
                        clk5_div_factor_real = (clk5_div * m_out * 1.0) / (clk5_mult * n_out);
                        clk6_div_factor_real = (clk6_div * m_out * 1.0) / (clk6_mult * n_out);
                        clk7_div_factor_real = (clk7_div * m_out * 1.0) / (clk7_mult * n_out);
                        clk8_div_factor_real = (clk8_div * m_out * 1.0) / (clk8_mult * n_out);
                        clk9_div_factor_real = (clk9_div * m_out * 1.0) / (clk9_mult * n_out);
        
                        clk0_div_factor_int = clk0_div_factor_real;
                        clk1_div_factor_int = clk1_div_factor_real;
                        clk2_div_factor_int = clk2_div_factor_real;
                        clk3_div_factor_int = clk3_div_factor_real;
                        clk4_div_factor_int = clk4_div_factor_real;
                        clk5_div_factor_int = clk5_div_factor_real;
                        clk6_div_factor_int = clk6_div_factor_real;
                        clk7_div_factor_int = clk7_div_factor_real;
                        clk8_div_factor_int = clk8_div_factor_real;
                        clk9_div_factor_int = clk9_div_factor_real;
                        
                        clk0_div_factor_diff = (clk0_div_factor_real - clk0_div_factor_int < 0) ? (clk0_div_factor_real - clk0_div_factor_int) * -1.0 : clk0_div_factor_real - clk0_div_factor_int;
                        clk1_div_factor_diff = (clk1_div_factor_real - clk1_div_factor_int < 0) ? (clk1_div_factor_real - clk1_div_factor_int) * -1.0 : clk1_div_factor_real - clk1_div_factor_int;
                        clk2_div_factor_diff = (clk2_div_factor_real - clk2_div_factor_int < 0) ? (clk2_div_factor_real - clk2_div_factor_int) * -1.0 : clk2_div_factor_real - clk2_div_factor_int;
                        clk3_div_factor_diff = (clk3_div_factor_real - clk3_div_factor_int < 0) ? (clk3_div_factor_real - clk3_div_factor_int) * -1.0 : clk3_div_factor_real - clk3_div_factor_int;
                        clk4_div_factor_diff = (clk4_div_factor_real - clk4_div_factor_int < 0) ? (clk4_div_factor_real - clk4_div_factor_int) * -1.0 : clk4_div_factor_real - clk4_div_factor_int;
                        clk5_div_factor_diff = (clk5_div_factor_real - clk5_div_factor_int < 0) ? (clk5_div_factor_real - clk5_div_factor_int) * -1.0 : clk5_div_factor_real - clk5_div_factor_int;
                        clk6_div_factor_diff = (clk6_div_factor_real - clk6_div_factor_int < 0) ? (clk6_div_factor_real - clk6_div_factor_int) * -1.0 : clk6_div_factor_real - clk6_div_factor_int;
                        clk7_div_factor_diff = (clk7_div_factor_real - clk7_div_factor_int < 0) ? (clk7_div_factor_real - clk7_div_factor_int) * -1.0 : clk7_div_factor_real - clk7_div_factor_int;
                        clk8_div_factor_diff = (clk8_div_factor_real - clk8_div_factor_int < 0) ? (clk8_div_factor_real - clk8_div_factor_int) * -1.0 : clk8_div_factor_real - clk8_div_factor_int;
                        clk9_div_factor_diff = (clk9_div_factor_real - clk9_div_factor_int < 0) ? (clk9_div_factor_real - clk9_div_factor_int) * -1.0 : clk9_div_factor_real - clk9_div_factor_int;
                        
        
                        if (((clk0_div_factor_diff < max_offset) || (clk0_used == "unused")) &&
                            ((clk1_div_factor_diff < max_offset) || (clk1_used == "unused")) &&
                            ((clk2_div_factor_diff < max_offset) || (clk2_used == "unused")) &&
                            ((clk3_div_factor_diff < max_offset) || (clk3_used == "unused")) &&
                            ((clk4_div_factor_diff < max_offset) || (clk4_used == "unused")) &&
                            ((clk5_div_factor_diff < max_offset) || (clk5_used == "unused")) &&
                            ((clk6_div_factor_diff < max_offset) || (clk6_used == "unused")) &&
                            ((clk7_div_factor_diff < max_offset) || (clk7_used == "unused")) &&
                            ((clk8_div_factor_diff < max_offset) || (clk8_used == "unused")) &&
                            ((clk9_div_factor_diff < max_offset) || (clk9_used == "unused")) )
                        begin                
                            if ((m_out != 0) && (n_out != 0))
                            begin
                                pfd_freq = 1000000 / (inclock_period * n_out);
                                vco_freq = (1000000 * m_out) / (inclock_period * n_out);
                                vco_ps_step_value = (inclock_period * n_out) / (8 * m_out);
                
                                if ( (m_out < max_m) && (n_out < max_n) && (pfd_freq >= min_pfd) && (pfd_freq <= max_pfd) &&
                                    (vco_freq >= min_vco) && (vco_freq <= max_vco) )
                                begin
                                    if (abs(vco_ps_step_value - vco_phase_shift_step) <= 2)
                                    begin
                                        pre_m = m_out;
                                        pre_n = n_out;
                                        disable LOOP_1;
                                    end
                                    else
                                    begin
                                        if ((closest_vco_step_value == 0) || (abs(vco_ps_step_value - vco_phase_shift_step) < abs(closest_vco_step_value - vco_phase_shift_step)))
                                        begin
                                            pre_m = m_out;
                                            pre_n = n_out;
                                            closest_vco_step_value = vco_ps_step_value;
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
        end
        
        if ((pre_m != 0) && (pre_n != 0))
        begin
            find_simple_integer_fraction(pre_m, pre_n,
                        max_n, m, n);
        end
        else
        begin
            n = 1;
            m = lcm  (clk0_mult, clk1_mult, clk2_mult, clk3_mult,
                    clk4_mult, clk5_mult, clk6_mult,
                    clk7_mult, clk8_mult, clk9_mult, inclock_period);           
        end
    end
    endtask // find_m_and_n_4_manual_phase

    // find the factor of division of the output clock frequency
    // compared to the VCO
    function integer output_counter_value;
    input clk_divide, clk_mult, M, N;
    integer clk_divide, clk_mult, M, N;
    real r;
    integer r_int;
    begin
        r = (clk_divide * M * 1.0)/(clk_mult * N);
        r_int = r;
        output_counter_value = r_int;
    end
    endfunction

    // find the mode of each of the PLL counters - bypass, even or odd
    function [8*6:1] counter_mode;
    input duty_cycle;
    input output_counter_value;
    integer duty_cycle;
    integer output_counter_value;
    integer half_cycle_high;
    reg [8*6:1] R;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        if (output_counter_value == 1)
            R = "bypass";
        else if ((half_cycle_high % 2) == 0)
            R = "  even";
        else
            R = "   odd";
        counter_mode = R;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock high
    function integer counter_high;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle;
    integer half_cycle_high;
    integer tmp_counter_high;
    integer mode;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_high = tmp_counter_high + !mode;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock low
    function integer counter_low;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle, counter_h;
    integer half_cycle_high;
    integer mode;
    integer tmp_counter_high;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_h = tmp_counter_high + !mode;
        counter_low =  output_counter_value - counter_h;
    end
    endfunction

    // find the smallest time delay amongst t1 to t10
    function integer mintimedelay;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2)
            m1 = t1;
        else
            m1 = t2;
        if (m1 < t3)
            m2 = m1;
        else
            m2 = t3;
        if (m2 < t4)
            m3 = m2;
        else
            m3 = t4;
        if (m3 < t5)
            m4 = m3;
        else
            m4 = t5;
        if (m4 < t6)
            m5 = m4;
        else
            m5 = t6;
        if (m5 < t7)
            m6 = m5;
        else
            m6 = t7;
        if (m6 < t8)
            m7 = m6;
        else
            m7 = t8;
        if (m7 < t9)
            m8 = m7;
        else
            m8 = t9;
        if (m8 < t10)
            m9 = m8;
        else
            m9 = t10;
        if (m9 > 0)
            mintimedelay = m9;
        else
            mintimedelay = 0;
    end
    endfunction

    // find the numerically largest negative number, and return its absolute value
    function integer maxnegabs;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2) m1 = t1; else m1 = t2;
        if (m1 < t3) m2 = m1; else m2 = t3;
        if (m2 < t4) m3 = m2; else m3 = t4;
        if (m3 < t5) m4 = m3; else m4 = t5;
        if (m4 < t6) m5 = m4; else m5 = t6;
        if (m5 < t7) m6 = m5; else m6 = t7;
        if (m6 < t8) m7 = m6; else m7 = t8;
        if (m7 < t9) m8 = m7; else m8 = t9;
        if (m8 < t10) m9 = m8; else m9 = t10;
        maxnegabs = (m9 < 0) ? 0 - m9 : 0;
    end
    endfunction

    // adjust the given tap_phase by adding the largest negative number (ph_base) 
    function integer ph_adjust;
    input tap_phase, ph_base;
    integer tap_phase, ph_base;
    begin
        ph_adjust = tap_phase + ph_base;
    end
    endfunction

    // find the number of VCO clock cycles to wait initially before the first 
    // rising edge of the output clock
    function integer counter_initial;
    input tap_phase, m, n;
    integer tap_phase, m, n, phase;
    begin
        if (tap_phase < 0) tap_phase = 0 - tap_phase;
        // adding 0.5 for rounding correction (required in order to round
        // to the nearest integer instead of truncating)
        phase = ((tap_phase * m) / (360.0 * n)) + 0.6;
        counter_initial = phase;
    end
    endfunction

    // find which VCO phase tap to align the rising edge of the output clock to
    function integer counter_ph;
    input tap_phase;
    input m,n;
    integer m,n, phase;
    integer tap_phase;
    begin
    // adding 0.5 for rounding correction
        phase = (tap_phase * m / n) + 0.5;
        counter_ph = (phase % 360) / 45.0;

        if (counter_ph == 8)
            counter_ph = 0;
    end
    endfunction

    // convert the given string to length 6 by padding with spaces
    function [8*6:1] translate_string;
    input [8*6:1] mode;
    reg [8*6:1] new_mode;
    begin
        if (mode == "bypass")
            new_mode = "bypass";
        else if (mode == "even")
            new_mode = "  even";
        else if (mode == "odd")
            new_mode = "   odd";

        translate_string = new_mode;
    end
    endfunction

    // convert string to integer with sign
    function integer str2int; 
    input [8*16:1] s;

    reg [8*16:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    integer m, magnitude;
    integer sign;

    begin
        sign = 1;
        magnitude = 0;
        reg_s = s;
        for (m=1; m<=16; m=m+1)
        begin
            tmp = reg_s[128:121];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            // Accumulate ascii digits 0-9 only.
            if ((tmp>=48) && (tmp<=57)) 
                magnitude = (magnitude * 10) + digit;
            if (tmp == 45)
                sign = -1;  // Found a '-' character, i.e. number is negative.
        end
        str2int = sign*magnitude;
    end
    endfunction

    // this is for cycloneiii lvds only
    // convert phase delay to integer
    function integer get_int_phase_shift; 
    input [8*16:1] s;
    input i_phase_shift;
    integer i_phase_shift;

    begin
        if (i_phase_shift != 0)
        begin                   
            get_int_phase_shift = i_phase_shift;
        end       
        else
        begin
            get_int_phase_shift = str2int(s);
        end        
    end
    endfunction

    // calculate the given phase shift (in ps) in terms of degrees
    function integer get_phase_degree; 
    input phase_shift;
    integer phase_shift, result;
    begin
        result = (phase_shift * 360) / inclk0_freq;
        // this is to round up the calculation result
        if ( result > 0 )
            result = result + 1;
        else if ( result < 0 )
            result = result - 1;
        else
            result = 0;

        // assign the rounded up result
        get_phase_degree = result;
    end
    endfunction

    // convert uppercase parameter values to lowercase
    // assumes that the maximum character length of a parameter is 18
    function [8*`CYCIII_PLL_WORD_LENGTH:1] alpha_tolower;
    input [8*`CYCIII_PLL_WORD_LENGTH:1] given_string;

    reg [8*`CYCIII_PLL_WORD_LENGTH:1] return_string;
    reg [8*`CYCIII_PLL_WORD_LENGTH:1] reg_string;
    reg [8:1] tmp;
    reg [8:1] conv_char;
    integer byte_count;
    begin
        return_string = "                    "; // initialise strings to spaces
        conv_char = "        ";
        reg_string = given_string;
        for (byte_count = `CYCIII_PLL_WORD_LENGTH; byte_count >= 1; byte_count = byte_count - 1)
        begin
            tmp = reg_string[8*`CYCIII_PLL_WORD_LENGTH:(8*(`CYCIII_PLL_WORD_LENGTH-1)+1)];
            reg_string = reg_string << 8;
            if ((tmp >= 65) && (tmp <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
            begin
                conv_char = tmp + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
                return_string = {return_string, conv_char};
            end
            else
                return_string = {return_string, tmp};
        end
    
        alpha_tolower = return_string;
    end
    endfunction

    function integer display_msg;
    input [8*2:1] cntr_name;
    input msg_code;
    integer msg_code;
    begin
        if (msg_code == 1)
            $display ("Warning : %s counter switched from BYPASS mode to enabled. PLL may lose lock.", cntr_name);
        else if (msg_code == 2)
            $display ("Warning : Illegal 1 value for %s counter. Instead, the %s counter should be BYPASSED. Reconfiguration may not work.", cntr_name, cntr_name);
        else if (msg_code == 3)
            $display ("Warning : Illegal value for counter %s in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.", cntr_name);
        else if (msg_code == 4)
            $display ("Warning : %s counter switched from enabled to BYPASS mode. PLL may lose lock.", cntr_name);
        $display ("Time: %0t  Instance: %m", $time);
        display_msg = 1;
    end
    endfunction

    initial
    begin
        scandata_out = 1'b0;
        first_inclk0_edge_detect = 1'b0;
        first_inclk1_edge_detect = 1'b0;
        pll_reconfig_display_full_setting = 1'b0;
        initiate_reconfig = 1'b0;
    switch_over_count = 0;
        // convert string parameter values from uppercase to lowercase,
        // as expected in this model
        l_operation_mode             = alpha_tolower(operation_mode);
        l_pll_type                   = alpha_tolower(pll_type);
        l_compensate_clock           = alpha_tolower(compensate_clock);
        l_switch_over_type           = alpha_tolower(switch_over_type);
        l_bandwidth_type             = alpha_tolower(bandwidth_type);
        l_simulation_type            = alpha_tolower(simulation_type);
        l_sim_gate_lock_device_behavior = alpha_tolower(sim_gate_lock_device_behavior);
        l_vco_frequency_control      = alpha_tolower(vco_frequency_control);
        l_enable_switch_over_counter = alpha_tolower(enable_switch_over_counter);
        l_self_reset_on_loss_lock    = alpha_tolower(self_reset_on_loss_lock);
    
        real_lock_high = (l_sim_gate_lock_device_behavior == "on") ? lock_high : 0;    
        // initialize charge_pump_current, and loop_filter tables
        loop_filter_c_arr[0] = 0;
        loop_filter_c_arr[1] = 0;
        loop_filter_c_arr[2] = 0;
        loop_filter_c_arr[3] = 0;
        
        fpll_loop_filter_c_arr[0] = 0;
        fpll_loop_filter_c_arr[1] = 0;
        fpll_loop_filter_c_arr[2] = 0;
        fpll_loop_filter_c_arr[3] = 0;
        
        charge_pump_curr_arr[0] = 0;
        charge_pump_curr_arr[1] = 0;
        charge_pump_curr_arr[2] = 0;
        charge_pump_curr_arr[3] = 0;
        charge_pump_curr_arr[4] = 0;
        charge_pump_curr_arr[5] = 0;
        charge_pump_curr_arr[6] = 0;
        charge_pump_curr_arr[7] = 0;
        charge_pump_curr_arr[8] = 0;
        charge_pump_curr_arr[9] = 0;
        charge_pump_curr_arr[10] = 0;
        charge_pump_curr_arr[11] = 0;
        charge_pump_curr_arr[12] = 0;
        charge_pump_curr_arr[13] = 0;
        charge_pump_curr_arr[14] = 0;
        charge_pump_curr_arr[15] = 0;

        i_vco_max = vco_max;
        i_vco_min = vco_min; 

        if(vco_post_scale == 1)
        begin
            i_vco_max_no_division = vco_max * 2;
            i_vco_min_no_division = vco_min * 2;    
        end
        else
        begin
            i_vco_max_no_division = vco_max;
            i_vco_min_no_division = vco_min;    
        end


        if (m == 0)
        begin
            i_clk4_counter    = "c4" ;
            i_clk3_counter    = "c3" ;
            i_clk2_counter    = "c2" ;
            i_clk1_counter    = "c1" ;
            i_clk0_counter    = "c0" ;
        end
        else begin
            i_clk4_counter    = alpha_tolower(clk4_counter);
            i_clk3_counter    = alpha_tolower(clk3_counter);
            i_clk2_counter    = alpha_tolower(clk2_counter);
            i_clk1_counter    = alpha_tolower(clk1_counter);
            i_clk0_counter    = alpha_tolower(clk0_counter);
        end

        if (m == 0)
        begin 

            // set the limit of the divide_by value that can be returned by
            // the following function.
            max_d_value = 500;
            
            // scale down the multiply_by and divide_by values provided by the design
            // before attempting to use them in the calculations below
            find_simple_integer_fraction(clk0_multiply_by, clk0_divide_by,
                            max_d_value, i_clk0_mult_by, i_clk0_div_by);
            find_simple_integer_fraction(clk1_multiply_by, clk1_divide_by,
                            max_d_value, i_clk1_mult_by, i_clk1_div_by);
            find_simple_integer_fraction(clk2_multiply_by, clk2_divide_by,
                            max_d_value, i_clk2_mult_by, i_clk2_div_by);
            find_simple_integer_fraction(clk3_multiply_by, clk3_divide_by,
                            max_d_value, i_clk3_mult_by, i_clk3_div_by);
            find_simple_integer_fraction(clk4_multiply_by, clk4_divide_by,
                            max_d_value, i_clk4_mult_by, i_clk4_div_by);

            // convert user parameters to advanced
            if (l_vco_frequency_control == "manual_phase")
            begin
                find_m_and_n_4_manual_phase(inclk0_freq, vco_phase_shift_step,
                            i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,i_clk4_mult_by,
                1, 1, 1, 1, 1, 
                            i_clk0_div_by, i_clk1_div_by,
                            i_clk2_div_by, i_clk3_div_by,i_clk4_div_by,
                1, 1, 1, 1, 1, 
                            clk0_counter, clk1_counter,
                            clk2_counter, clk3_counter,clk4_counter,
                "unused", "unused", "unused", "unused", "unused", 
                            i_m, i_n);
            end
            else if (((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right")) && (vco_multiply_by != 0) && (vco_divide_by != 0))
            begin
                i_n = vco_divide_by;
                i_m = vco_multiply_by;
            end
            else begin
                i_n = 1;
                if (((l_pll_type == "fast") || (l_pll_type == "left_right")) && (l_compensate_clock == "lvdsclk"))
                    i_m = i_clk0_mult_by;
                else
                    i_m = lcm  (i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,i_clk4_mult_by,
                1, 1, 1, 1, 1, 
                            inclk0_freq);
            end

            i_c_high[0] = counter_high (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by, i_m, i_n), clk0_duty_cycle);
            i_c_high[1] = counter_high (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by, i_m, i_n), clk1_duty_cycle);
            i_c_high[2] = counter_high (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by, i_m, i_n), clk2_duty_cycle);
            i_c_high[3] = counter_high (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by, i_m, i_n), clk3_duty_cycle);
            i_c_high[4] = counter_high (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);

            i_c_low[0]  = counter_low  (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by,  i_m, i_n), clk0_duty_cycle);
            i_c_low[1]  = counter_low  (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by,  i_m, i_n), clk1_duty_cycle);
            i_c_low[2]  = counter_low  (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by,  i_m, i_n), clk2_duty_cycle);
            i_c_low[3]  = counter_low  (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by,  i_m, i_n), clk3_duty_cycle);
            i_c_low[4]  = counter_low  (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);

            if (l_pll_type == "flvds")
            begin
                // Need to readjust phase shift values when the clock multiply value has been readjusted.
                new_multiplier = clk0_multiply_by / i_clk0_mult_by;
                i_clk0_phase_shift = (clk0_phase_shift_num * new_multiplier);
                i_clk1_phase_shift = (clk1_phase_shift_num * new_multiplier);
                i_clk2_phase_shift = (clk2_phase_shift_num * new_multiplier);
                i_clk3_phase_shift = 0;
                i_clk4_phase_shift = 0;
            end
            else
            begin
                i_clk0_phase_shift = get_int_phase_shift(clk0_phase_shift, clk0_phase_shift_num);
                i_clk1_phase_shift = get_int_phase_shift(clk1_phase_shift, clk1_phase_shift_num);
                i_clk2_phase_shift = get_int_phase_shift(clk2_phase_shift, clk2_phase_shift_num);
                i_clk3_phase_shift = get_int_phase_shift(clk3_phase_shift, clk3_phase_shift_num);
                i_clk4_phase_shift = get_int_phase_shift(clk4_phase_shift, clk4_phase_shift_num);
            end

            max_neg_abs = maxnegabs   ( i_clk0_phase_shift,
                                        i_clk1_phase_shift,
                                        i_clk2_phase_shift,
                                        i_clk3_phase_shift,
                                        i_clk4_phase_shift,
                                            0,
                                            0,
                                            0,
                                            0,
                                            0
                                        );

            i_c_initial[0] = counter_initial(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[1] = counter_initial(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[2] = counter_initial(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[3] = counter_initial(get_phase_degree(ph_adjust(i_clk3_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[4] = counter_initial(get_phase_degree(ph_adjust(i_clk4_phase_shift, max_neg_abs)), i_m, i_n);

            i_c_mode[0] = counter_mode(clk0_duty_cycle,output_counter_value(i_clk0_div_by, i_clk0_mult_by,  i_m, i_n));
            i_c_mode[1] = counter_mode(clk1_duty_cycle,output_counter_value(i_clk1_div_by, i_clk1_mult_by,  i_m, i_n));
            i_c_mode[2] = counter_mode(clk2_duty_cycle,output_counter_value(i_clk2_div_by, i_clk2_mult_by,  i_m, i_n));
            i_c_mode[3] = counter_mode(clk3_duty_cycle,output_counter_value(i_clk3_div_by, i_clk3_mult_by,  i_m, i_n));
            i_c_mode[4] = counter_mode(clk4_duty_cycle,output_counter_value(i_clk4_div_by, i_clk4_mult_by,  i_m, i_n));

            i_m_ph    = counter_ph(get_phase_degree(max_neg_abs), i_m, i_n);
            i_m_initial = counter_initial(get_phase_degree(max_neg_abs), i_m, i_n);
            
            i_c_ph[0] = counter_ph(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[1] = counter_ph(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[2] = counter_ph(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[3] = counter_ph(get_phase_degree(ph_adjust(i_clk3_phase_shift,max_neg_abs)), i_m, i_n);
            i_c_ph[4] = counter_ph(get_phase_degree(ph_adjust(i_clk4_phase_shift,max_neg_abs)), i_m, i_n);


        end
        else 
        begin //  m != 0

            i_n = n;
            i_m = m;
            i_c_high[0] = c0_high;
            i_c_high[1] = c1_high;
            i_c_high[2] = c2_high;
            i_c_high[3] = c3_high;
            i_c_high[4] = c4_high;
            i_c_low[0]  = c0_low;
            i_c_low[1]  = c1_low;
            i_c_low[2]  = c2_low;
            i_c_low[3]  = c3_low;
            i_c_low[4]  = c4_low;
            i_c_initial[0] = c0_initial;
            i_c_initial[1] = c1_initial;
            i_c_initial[2] = c2_initial;
            i_c_initial[3] = c3_initial;
            i_c_initial[4] = c4_initial;
            i_c_mode[0] = translate_string(alpha_tolower(c0_mode));
            i_c_mode[1] = translate_string(alpha_tolower(c1_mode));
            i_c_mode[2] = translate_string(alpha_tolower(c2_mode));
            i_c_mode[3] = translate_string(alpha_tolower(c3_mode));
            i_c_mode[4] = translate_string(alpha_tolower(c4_mode));
            i_c_ph[0]  = c0_ph;
            i_c_ph[1]  = c1_ph;
            i_c_ph[2]  = c2_ph;
            i_c_ph[3]  = c3_ph;
            i_c_ph[4]  = c4_ph;
            i_m_ph   = m_ph;        // default
            i_m_initial = m_initial;

        end // user to advanced conversion
        
        switch_clock = 1'b0;

        refclk_period = inclk0_freq * i_n;

        m_times_vco_period = refclk_period;
        new_m_times_vco_period = refclk_period;

        fbclk_period = 0;
        high_time = 0;
        low_time = 0;
        schedule_vco = 0;
        vco_out[7:0] = 8'b0;
        vco_tap[7:0] = 8'b0;
        fbclk_last_value = 0;
        offset = 0;
        temp_offset = 0;
        got_first_refclk = 0;
        got_first_fbclk = 0;
        fbclk_time = 0;
        first_fbclk_time = 0;
        refclk_time = 0;
        first_schedule = 1;
        sched_time = 0;
        vco_val = 0;
        gate_count = 0;
        gate_out = 0;
        initial_delay = 0;
        fbk_phase = 0;
        for (i = 0; i <= 7; i = i + 1)
        begin
            phase_shift[i] = 0;
            last_phase_shift[i] = 0;
        end
        fbk_delay = 0;
        inclk_n = 0;
        inclk_es = 0;
        inclk_man = 0;
        cycle_to_adjust = 0;
        m_delay = 0;
        total_pull_back = 0;
        pull_back_M = 0;
        vco_period_was_phase_adjusted = 0;
        phase_adjust_was_scheduled = 0;
        inclk_out_of_range = 0;
        scandone_tmp = 1'b0;
        schedule_vco_last_value = 0;

        scan_chain_length = SCAN_CHAIN;
        num_output_cntrs  = 5;

        
        phasestep_high_count = 0;
        update_phase = 0;
        // set initial values for counter parameters
        m_initial_val = i_m_initial;
        m_val[0] = i_m;
        n_val[0] = i_n;
        m_ph_val = i_m_ph;
        m_ph_val_orig = i_m_ph;
        m_ph_val_tmp = i_m_ph;
        m_val_tmp[0] = i_m;


        if (m_val[0] == 1)
            m_mode_val[0] = "bypass";
        else m_mode_val[0] = "";
        if (m_val[1] == 1)
            m_mode_val[1] = "bypass";
        if (n_val[0] == 1)
            n_mode_val[0] = "bypass";
        if (n_val[1] == 1)
            n_mode_val[1] = "bypass";

        for (i = 0; i < 10; i=i+1)
        begin
            c_high_val[i] = i_c_high[i];
            c_low_val[i] = i_c_low[i];
            c_initial_val[i] = i_c_initial[i];
            c_mode_val[i] = i_c_mode[i];
            c_ph_val[i] = i_c_ph[i];
            c_high_val_tmp[i] = i_c_high[i];
            c_hval[i] = i_c_high[i];
            c_low_val_tmp[i] = i_c_low[i];
            c_lval[i] = i_c_low[i];
            if (c_mode_val[i] == "bypass")
            begin
                if (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right")
                begin
                    c_high_val[i] = 5'b10000;
                    c_low_val[i] = 5'b10000;
                    c_high_val_tmp[i] = 5'b10000;
                    c_low_val_tmp[i] = 5'b10000;
                end
                else begin
                    c_high_val[i] = 9'b100000000;
                    c_low_val[i] = 9'b100000000;
                    c_high_val_tmp[i] = 9'b100000000;
                    c_low_val_tmp[i] = 9'b100000000;
                end
            end

            c_mode_val_tmp[i] = i_c_mode[i];
            c_ph_val_tmp[i] = i_c_ph[i];

            c_ph_val_orig[i] = i_c_ph[i];
            c_high_val_hold[i] = i_c_high[i];
            c_low_val_hold[i] = i_c_low[i];
            c_mode_val_hold[i] = i_c_mode[i];
        end

        lfc_val = loop_filter_c;
        lfr_val = loop_filter_r;
        cp_curr_val = charge_pump_current;
        vco_cur = vco_post_scale;

        i = 0;
        j = 0;
        inclk_last_value = 0;

    
        // initialize clkswitch variables

        clk0_is_bad = 0;
        clk1_is_bad = 0;
        inclk0_last_value = 0;
        inclk1_last_value = 0;
        other_clock_value = 0;
        other_clock_last_value = 0;
        primary_clk_is_bad = 0;
        current_clk_is_bad = 0;
        external_switch = 0;
        current_clock = 0;
        current_clock_man = 0;

        active_clock = 0;   // primary_clk is always inclk0
        if (l_pll_type == "fast" || (l_pll_type == "left_right"))
            l_switch_over_type = "manual";

        if (l_switch_over_type == "manual" && clkswitch === 1'b1)
        begin
            current_clock_man = 1;
            active_clock = 1;
        end
        got_curr_clk_falling_edge_after_clkswitch = 0;
        clk0_count = 0;
        clk1_count = 0;

        // initialize reconfiguration variables
        // quiet_time
        quiet_time = slowest_clk  ( c_high_val[0]+c_low_val[0], c_mode_val[0],
                                    c_high_val[1]+c_low_val[1], c_mode_val[1],
                                    c_high_val[2]+c_low_val[2], c_mode_val[2],
                                    c_high_val[3]+c_low_val[3], c_mode_val[3],
                                    c_high_val[4]+c_low_val[4], c_mode_val[4],
                                    c_high_val[5]+c_low_val[5], c_mode_val[5],
                                    c_high_val[6]+c_low_val[6], c_mode_val[6],
                                    c_high_val[7]+c_low_val[7], c_mode_val[7],
                                    c_high_val[8]+c_low_val[8], c_mode_val[8],
                                    c_high_val[9]+c_low_val[9], c_mode_val[9],
                                    refclk_period, m_val[0]);
        reconfig_err = 0;
        error = 0;
        
        
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        got_first_scanclk = 0;
        got_first_gated_scanclk = 0;
        gated_scanclk = 1;
        scanread_setup_violation = 0;
        index = 0;

        vco_over  = 1'b0;
        vco_under = 1'b0;
        
        // Initialize the scan chain 
        
        // LF unused : bit 1
        scan_data[-1:0] = 2'b00;
        // LF Capacitance : bits 1,2 : all values are legal
        scan_data[1:2] = loop_filter_c_bits;
        // LF Resistance : bits 3-7
        scan_data[3:7] = loop_filter_r_bits;
        
        // VCO post scale
        if(vco_post_scale == 1)
        begin
            scan_data[8] = 1'b1;
            vco_val_old_bit_setting = 1'b1;
        end
        else
        begin
            scan_data[8] = 1'b0;
            vco_val_old_bit_setting = 1'b0;
        end
            
        scan_data[9:13] = 5'b00000;
        // CP
        // Bit 8 : CRBYPASS
        // Bit 9-13 : unused
        // Bits 14-16 : all values are legal                 
                scan_data[14:16] = charge_pump_current_bits;
        // store as old values
        
        cp_curr_old_bit_setting = charge_pump_current_bits;
        lfc_val_old_bit_setting = loop_filter_c_bits;
        lfr_val_old_bit_setting = loop_filter_r_bits;
            
        // C counters (start bit 53) bit 1:mode(bypass),bit 2-9:high,bit 10:mode(odd/even),bit 11-18:low
        for (i = 0; i < num_output_cntrs; i = i + 1)
        begin
            // 1. Mode - bypass
            if (c_mode_val[i] == "bypass")
            begin
                scan_data[53 + i*18 + 0] = 1'b1;
                if (c_mode_val[i] == "   odd")
                    scan_data[53 + i*18 + 9] = 1'b1;
                else
                    scan_data[53 + i*18 + 9] = 1'b0;
            end
            else
            begin
                scan_data[53 + i*18 + 0] = 1'b0;
                // 3. Mode - odd/even
                if (c_mode_val[i] == "   odd")
                    scan_data[53 + i*18 + 9] = 1'b1;
                else
                    scan_data[53 + i*18 + 9] = 1'b0;
            end
            // 2. Hi
            c_val = c_high_val[i];
            for (j = 1; j <= 8; j = j + 1)
                scan_data[53 + i*18 + j]  = c_val[8 - j];
   
            // 4. Low
            c_val = c_low_val[i];
            for (j = 10; j <= 17; j = j + 1)
                scan_data[53 + i*18 + j] = c_val[17 - j];
        end
            
        // M counter
        // 1. Mode - bypass (bit 17)
        if (m_mode_val[0] == "bypass")
                scan_data[35] = 1'b1;
        else
                scan_data[35] = 1'b0;
       
        // 2. High (bit 18-25)
        // 3. Mode - odd/even (bit 26)
        if (m_val[0] % 2 == 0)
        begin
            // M is an even no. : set M high = low,
            // set odd/even bit to 0
                scan_data[36:43]= m_val[0]/2;
                scan_data[44] = 1'b0;
        end
        else 
        begin 
            // M is odd : M high = low + 1
                scan_data[36:43] = m_val[0]/2 + 1;
                scan_data[44] = 1'b1;             
        end
        // 4. Low (bit 27-34)
            scan_data[45:52] = m_val[0]/2;

        
        // N counter
        // 1. Mode - bypass (bit 35)
        if (n_mode_val[0] == "bypass")
                scan_data[17] = 1'b1;
        else 
                scan_data[17] = 1'b0;
        // 2. High (bit 36-43)
        // 3. Mode - odd/even (bit 44)
        if (n_val[0] % 2 == 0)
        begin
            // N is an even no. : set N high = low,
            // set odd/even bit to 0
                scan_data[18:25] = n_val[0]/2;
                scan_data[26] = 1'b0;         
        end
        else 
        begin // N is odd : N high = N low + 1
                scan_data[18:25] = n_val[0]/2+ 1;
                scan_data[26] = 1'b1;         
        end
        // 4. Low (bit 45-52)
                scan_data[27:34] = n_val[0]/2;


        l_index = 1;
        stop_vco = 0;
        cycles_to_lock = 0;
        cycles_to_unlock = 0;
        locked_tmp = 0;
        pll_is_locked = 0;
        no_warn = 1'b0;
        
        pfd_locked = 1'b0;
        cycles_pfd_high = 0;
        cycles_pfd_low  = 0;

        // check if pll is in test mode
        if (m_test_source != -1 || c0_test_source != -1 || c1_test_source != -1 || c2_test_source != -1 || c3_test_source != -1 || c4_test_source != -1)
            pll_in_test_mode = 1'b1;
        else
            pll_in_test_mode = 1'b0;

        pll_is_in_reset = 0;
        pll_has_just_been_reconfigured = 0;
        if (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right")
            is_fast_pll = 1;
        else is_fast_pll = 0;

        if (c1_use_casc_in == "on")
            ic1_use_casc_in = 1;
        else
            ic1_use_casc_in = 0;
        if (c2_use_casc_in == "on")
            ic2_use_casc_in = 1;
        else
            ic2_use_casc_in = 0;
        if (c3_use_casc_in == "on")
            ic3_use_casc_in = 1;
        else
            ic3_use_casc_in = 0;
        if (c4_use_casc_in == "on")
            ic4_use_casc_in = 1;
        else
            ic4_use_casc_in = 0;

        tap0_is_active = 1;
        
// To display clock mapping       
    case( i_clk0_counter)
            "c0" : clk_num[0] = "  clk0";
            "c1" : clk_num[0] = "  clk1";
            "c2" : clk_num[0] = "  clk2";
            "c3" : clk_num[0] = "  clk3";
            "c4" : clk_num[0] = "  clk4";
            default:clk_num[0] = "unused";
    endcase
    
        case( i_clk1_counter)
            "c0" : clk_num[1] = "  clk0";
            "c1" : clk_num[1] = "  clk1";
            "c2" : clk_num[1] = "  clk2";
            "c3" : clk_num[1] = "  clk3";
            "c4" : clk_num[1] = "  clk4";
            default:clk_num[1] = "unused";
    endcase
        
    case( i_clk2_counter)
            "c0" : clk_num[2] = "  clk0";
            "c1" : clk_num[2] = "  clk1";
            "c2" : clk_num[2] = "  clk2";
            "c3" : clk_num[2] = "  clk3";
            "c4" : clk_num[2] = "  clk4";
            default:clk_num[2] = "unused";
    endcase
        
    case( i_clk3_counter)
            "c0" : clk_num[3] = "  clk0";
            "c1" : clk_num[3] = "  clk1";
            "c2" : clk_num[3] = "  clk2";
            "c3" : clk_num[3] = "  clk3";
            "c4" : clk_num[3] = "  clk4";
            default:clk_num[3] = "unused";
    endcase
        
    case( i_clk4_counter)
            "c0" : clk_num[4] = "  clk0";
            "c1" : clk_num[4] = "  clk1";
            "c2" : clk_num[4] = "  clk2";
            "c3" : clk_num[4] = "  clk3";
            "c4" : clk_num[4] = "  clk4";
            default:clk_num[4] = "unused";
    endcase
        

        end


// Clock Switchover

always @(clkswitch)
begin
    if (clkswitch === 1'b1 && l_switch_over_type == "auto")
        external_switch = 1;
    else if (l_switch_over_type == "manual") 
    begin
        if(clkswitch === 1'b1)
            switch_clock = 1'b1;
        else
            switch_clock = 1'b0;
    end
end


always @(posedge inclk[0])
begin
// Determine the inclk0 frequency
    if (first_inclk0_edge_detect == 1'b0)
        begin
            first_inclk0_edge_detect = 1'b1;
        end
    else
        begin
            last_inclk0_period = inclk0_period;
            inclk0_period = $realtime - last_inclk0_edge;
        end
    last_inclk0_edge = $realtime;

end

always @(posedge inclk[1])
begin
// Determine the inclk1 frequency
    if (first_inclk1_edge_detect == 1'b0)
        begin
            first_inclk1_edge_detect = 1'b1;
        end
    else
        begin
            last_inclk1_period = inclk1_period;
            inclk1_period = $realtime - last_inclk1_edge;
        end
    last_inclk1_edge = $realtime;

end

    always @(inclk[0] or inclk[1])
    begin
        if(switch_clock == 1'b1)
        begin
                if(current_clock_man == 0)
                begin
                    current_clock_man = 1;
                    active_clock = 1;
                end
                else
                begin
                    current_clock_man = 0;
                    active_clock = 0;
                end
                switch_clock = 1'b0;
            end

        if (current_clock_man == 0)
            inclk_man = inclk[0];
        else
            inclk_man = inclk[1];


        // save the inclk event value
        if (inclk[0] !== inclk0_last_value)
        begin
            if (current_clock != 0)
                other_clock_value = inclk[0];
        end
        if (inclk[1] !== inclk1_last_value)
        begin
            if (current_clock != 1)
                other_clock_value = inclk[1];
        end

        // check if either input clk is bad
        if (inclk[0] === 1'b1 && inclk[0] !== inclk0_last_value)
        begin
            clk0_count = clk0_count + 1;
            clk0_is_bad = 0;
            clk1_count = 0;
            if (clk0_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk1_is_bad = 1;
                if (current_clock == 1)
                    current_clk_is_bad = 1;
            end
        end
        if (inclk[1] === 1'b1 && inclk[1] !== inclk1_last_value)
        begin
            clk1_count = clk1_count + 1;
            clk1_is_bad = 0;
            clk0_count = 0;
            if (clk1_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk0_is_bad = 1;
                if (current_clock == 0)
                    current_clk_is_bad = 1;
            end
        end

        // check if the bad clk is the primary clock, which is always clk0
        if (clk0_is_bad == 1'b1)
            primary_clk_is_bad = 1;
        else
            primary_clk_is_bad = 0;

        // actual switching -- manual switch
        if ((inclk[0] !== inclk0_last_value) && current_clock == 0)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk[0] === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_es = inclk[0];
                end
            end
            else inclk_es = inclk[0];
        end
        if ((inclk[1] !== inclk1_last_value) && current_clock == 1)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk[1] === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_es = inclk[1];
                end
            end
            else inclk_es = inclk[1];
        end

        // actual switching -- automatic switch
        if ((other_clock_value == 1'b1) && (other_clock_value != other_clock_last_value) && l_enable_switch_over_counter == "on" && primary_clk_is_bad)
            switch_over_count = switch_over_count + 1;
        
        if ((other_clock_value == 1'b0) && (other_clock_value != other_clock_last_value))
        begin
            if ((external_switch && (got_curr_clk_falling_edge_after_clkswitch || current_clk_is_bad)) || (primary_clk_is_bad && (clkswitch !== 1'b1) && ((l_enable_switch_over_counter == "off" || switch_over_count == switch_over_counter))))
            begin
                if (areset === 1'b0)
                begin
                    if ((inclk0_period > inclk1_period) && (inclk1_period != 0))
                        diff_percent_period = (( inclk0_period - inclk1_period ) * 100) / inclk1_period;
                    else if (inclk0_period != 0)
                        diff_percent_period = (( inclk1_period - inclk0_period ) * 100) / inclk0_period;

                    if((diff_percent_period > 20)&& (l_switch_over_type == "auto"))
                    begin
                        $display ("Warning : The input clock frequencies specified for the specified PLL are too far apart for auto-switch-over feature to work properly. Please make sure that the clock frequencies are 20 percent apart for correct functionality.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end

                got_curr_clk_falling_edge_after_clkswitch = 0;
                if (current_clock == 0)
                    current_clock = 1;
                else
                    current_clock = 0;
                    
                active_clock = ~active_clock;
                switch_over_count = 0;
                external_switch = 0;
                current_clk_is_bad = 0;
            end
            else if(l_switch_over_type == "auto")
                begin
                    if(current_clock == 0 && clk0_is_bad == 1'b1 && clk1_is_bad == 1'b0 )
                        begin
                            current_clock = 1;
                            active_clock = ~active_clock;
                        end 
                
                    if(current_clock == 1 && clk1_is_bad == 1'b1 && clk0_is_bad == 1'b0 )
                        begin
                            current_clock = 0;
                            active_clock = ~active_clock;
                        end
                end     
        end
        
        if(l_switch_over_type == "manual")
            inclk_n = inclk_man;
        else
            inclk_n = inclk_es;
            
        inclk0_last_value = inclk[0];
        inclk1_last_value = inclk[1];
        other_clock_last_value = other_clock_value;

    end

    and (clkbad[0], clk0_is_bad, 1'b1);
    and (clkbad[1], clk1_is_bad, 1'b1);
    and (activeclock, active_clock, 1'b1);


    assign inclk_m = (m_test_source == 0) ? fbclk : (m_test_source == 1) ? refclk : inclk_m_from_vco; 
                       

    cda_m_cntr m1 (.clk(inclk_m),
                        .reset(areset || stop_vco),
                        .cout(fbclk),
                        .initial_value(m_initial_val),
                        .modulus(m_val[0]),
                        .time_delay(m_delay));

    cda_n_cntr n1 (.clk(inclk_n),
                        .reset(areset),
                        .cout(refclk),
                        .modulus(n_val[0]));



    // Update clock on /o counters from corresponding VCO tap
    assign inclk_m_from_vco  = vco_tap[m_ph_val];
    assign inclk_c0_from_vco = vco_tap[c_ph_val[0]];
    assign inclk_c1_from_vco = vco_tap[c_ph_val[1]];
    assign inclk_c2_from_vco = vco_tap[c_ph_val[2]];
    assign inclk_c3_from_vco = vco_tap[c_ph_val[3]];
    assign inclk_c4_from_vco = vco_tap[c_ph_val[4]];
always @(vco_out)
    begin
        // check which VCO TAP has event
        for (x = 0; x <= 7; x = x + 1)
        begin
            if (vco_out[x] !== vco_out_last_value[x])
            begin
                // TAP 'X' has event
                if ((x == 0) && (!pll_is_in_reset) && (stop_vco !== 1'b1))
                begin
                    if (vco_out[0] == 1'b1)
                        tap0_is_active = 1;
                    if (tap0_is_active == 1'b1)
                        vco_tap[0] <= vco_out[0];
                end
                else if (tap0_is_active == 1'b1)
                    vco_tap[x] <= vco_out[x];
                if (stop_vco === 1'b1)
                    vco_out[x] <= 1'b0;
            end
        end
        vco_out_last_value = vco_out;
    end

    always @(vco_tap)
    begin
        // Update phase taps for C/M counters on negative edge of VCO clock output
        
        if (update_phase == 1'b1)
        begin
            for (x = 0; x <= 7; x = x + 1)
            begin
                if ((vco_tap[x] === 1'b0) && (vco_tap[x] !== vco_tap_last_value[x]))
                begin
                    for (y = 0; y < 10; y = y + 1)
                    begin
                        if (c_ph_val_tmp[y] == x)
                            c_ph_val[y] = c_ph_val_tmp[y];
                    end
                    if (m_ph_val_tmp == x)
                        m_ph_val = m_ph_val_tmp;
                end
            end
            update_phase <= #(0.5*scanclk_period) 1'b0;
        end

        // On reset, set all C/M counter phase taps to POF programmed values
        if (areset === 1'b1)
        begin
            m_ph_val = m_ph_val_orig;
            m_ph_val_tmp = m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
            begin
                c_ph_val[i] = c_ph_val_orig[i];
                c_ph_val_tmp[i] = c_ph_val_orig[i];
            end
        end

        vco_tap_last_value = vco_tap;
    end

    assign inclk_c0 = (c0_test_source == 0) ? fbclk : (c0_test_source == 1) ? refclk : inclk_c0_from_vco;

    cda_scale_cntr c0 (.clk(inclk_c0),
                            .reset(areset  || stop_vco),
                            .cout(c0_clk),
                            .high(c_high_val[0]),
                            .low(c_low_val[0]),
                            .initial_value(c_initial_val[0]),
                            .mode(c_mode_val[0]),
                            .ph_tap(c_ph_val[0]));

    // Update /o counters mode and duty cycle immediately after configupdate is asserted
    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[0] <= c_high_val_tmp[0];
            c_mode_val[0] <= c_mode_val_tmp[0];
            c0_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c0_rising_edge_transfer_done)
        begin
            c_low_val[0] <= c_low_val_tmp[0];
        end
    end

    assign inclk_c1 = (c1_test_source == 0) ? fbclk : (c1_test_source == 1) ? refclk : (ic1_use_casc_in == 1) ? c0_clk : inclk_c1_from_vco;
    
    cda_scale_cntr c1 (.clk(inclk_c1),
                            .reset(areset || stop_vco),
                            .cout(c1_clk),
                            .high(c_high_val[1]),
                            .low(c_low_val[1]),
                            .initial_value(c_initial_val[1]),
                            .mode(c_mode_val[1]),
                            .ph_tap(c_ph_val[1]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[1] <= c_high_val_tmp[1];
            c_mode_val[1] <= c_mode_val_tmp[1];
            c1_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c1_rising_edge_transfer_done)
        begin
            c_low_val[1] <= c_low_val_tmp[1];
        end
    end

    assign inclk_c2 = (c2_test_source == 0) ? fbclk : (c2_test_source == 1) ? refclk :(ic2_use_casc_in == 1) ? c1_clk : inclk_c2_from_vco;

    cda_scale_cntr c2 (.clk(inclk_c2),
                            .reset(areset || stop_vco),
                            .cout(c2_clk),
                            .high(c_high_val[2]),
                            .low(c_low_val[2]),
                            .initial_value(c_initial_val[2]),
                            .mode(c_mode_val[2]),
                            .ph_tap(c_ph_val[2]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[2] <= c_high_val_tmp[2];
            c_mode_val[2] <= c_mode_val_tmp[2];
            c2_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c2_rising_edge_transfer_done)
        begin
            c_low_val[2] <= c_low_val_tmp[2];
        end
    end

    assign inclk_c3 = (c3_test_source == 0) ? fbclk : (c3_test_source == 1) ? refclk : (ic3_use_casc_in == 1) ? c2_clk : inclk_c3_from_vco;
    
    cda_scale_cntr c3 (.clk(inclk_c3),
                            .reset(areset  || stop_vco),
                            .cout(c3_clk),
                            .high(c_high_val[3]),
                            .low(c_low_val[3]),
                            .initial_value(c_initial_val[3]),
                            .mode(c_mode_val[3]),
                            .ph_tap(c_ph_val[3]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[3] <= c_high_val_tmp[3];
            c_mode_val[3] <= c_mode_val_tmp[3];
            c3_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c3_rising_edge_transfer_done)
        begin
            c_low_val[3] <= c_low_val_tmp[3];
        end
    end

    assign inclk_c4 = ((c4_test_source == 0) ? fbclk : (c4_test_source == 1) ? refclk :  (ic4_use_casc_in == 1) ? c3_clk : inclk_c4_from_vco);
    cda_scale_cntr c4 (.clk(inclk_c4),
                            .reset(areset || stop_vco),
                            .cout(c4_clk),
                            .high(c_high_val[4]),
                            .low(c_low_val[4]),
                            .initial_value(c_initial_val[4]),
                            .mode(c_mode_val[4]),
                            .ph_tap(c_ph_val[4]));

    always @(posedge scanclk)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[4] <= c_high_val_tmp[4];
            c_mode_val[4] <= c_mode_val_tmp[4];
            c4_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk)
    begin
        if (c4_rising_edge_transfer_done)
        begin
            c_low_val[4] <= c_low_val_tmp[4];
        end
    end

    
assign locked = (test_bypass_lock_detect == "on") ? pfd_locked : locked_tmp;

// Register scanclk enable
    always @(negedge scanclk)
        scanclkena_reg <= scanclkena;
        
// Negative edge flip-flop in front of scan-chain

    always @(negedge scanclk)
    begin
        if (scanclkena_reg)
        begin
            scandata_in <= scandata;
        end
    end
   
// Scan chain
    always @(posedge scanclk)
    begin
        if (got_first_scanclk === 1'b0)
                got_first_scanclk = 1'b1;
        else
                scanclk_period = $time - scanclk_last_rising_edge;
        if (scanclkena_reg) 
        begin        
            for (j = scan_chain_length-2; j >= 0; j = j - 1)
                scan_data[j] = scan_data[j - 1];
            scan_data[-1] <= scandata_in;
        end
        scanclk_last_rising_edge = $realtime;
    end
    
// Scan output
    assign scandataout_tmp = scan_data[SCAN_CHAIN - 2];

// Negative edge flip-flop in rear of scan-chain

    always @(negedge scanclk)
    begin
        if (scanclkena_reg)
        begin
            scandata_out <= scandataout_tmp;
        end
    end
    
// Scan complete
    always @(negedge scandone_tmp)
    begin
            if (got_first_scanclk === 1'b1)
            begin
            if (reconfig_err == 1'b0)
            begin
                $display("NOTE : PLL Reprogramming completed with the following values (Values in parantheses are original values) : ");
                $display ("Time: %0t  Instance: %m", $time);

                $display("               N modulus =   %0d (%0d) ", n_val[0], n_val_old[0]);
                $display("               M modulus =   %0d (%0d) ", m_val[0], m_val_old[0]);
                

                for (i = 0; i < num_output_cntrs; i=i+1)
                begin
                    $display("              %s :    C%0d  high = %0d (%0d),       C%0d  low = %0d (%0d),       C%0d  mode = %s (%s)", clk_num[i],i, c_high_val[i], c_high_val_old[i], i, c_low_val_tmp[i], c_low_val_old[i], i, c_mode_val[i], c_mode_val_old[i]);
                end

                // display Charge pump and loop filter values
                if (pll_reconfig_display_full_setting == 1'b1)
                begin
                    $display ("               Charge Pump Current (uA) =   %0d (%0d) ", cp_curr_val, cp_curr_old);
                    $display ("               Loop Filter Capacitor (pF) =   %0d (%0d) ", lfc_val, lfc_old);
                    $display ("               Loop Filter Resistor (Kohm) =   %s (%s) ", lfr_val, lfr_old);
                    $display ("               VCO_Post_Scale  =   %0d (%0d) ", vco_cur, vco_old);
                end
                else
                begin
                    $display ("               Charge Pump Current  =   %0d (%0d) ", cp_curr_bit_setting, cp_curr_old_bit_setting);
                    $display ("               Loop Filter Capacitor  =   %0d (%0d) ", lfc_val_bit_setting, lfc_val_old_bit_setting);
                    $display ("               Loop Filter Resistor   =   %0d (%0d) ", lfr_val_bit_setting, lfr_val_old_bit_setting);
                    $display ("               VCO_Post_Scale   =   %b (%b) ", vco_val_bit_setting, vco_val_old_bit_setting);
                end
                cp_curr_old_bit_setting = cp_curr_bit_setting;
                lfc_val_old_bit_setting = lfc_val_bit_setting;
                lfr_val_old_bit_setting = lfr_val_bit_setting;
                vco_val_old_bit_setting = vco_val_bit_setting;
            end
            else begin
                $display("Warning : Errors were encountered during PLL reprogramming. Please refer to error/warning messages above.");
                $display ("Time: %0t  Instance: %m", $time);
            end
            end
    end

// ************ PLL Phase Reconfiguration ************* //

// Latch updown,counter values at pos edge of scan clock
always @(posedge scanclk)
begin
    if (phasestep_reg == 1'b1)
    begin
        if (phasestep_high_count == 1)
        begin
            phasecounterselect_reg <= phasecounterselect;
            phaseupdown_reg <= phaseupdown;
            // start reconfiguration
            if (phasecounterselect < 3'b111) // no counters selected
            begin
                if (phasecounterselect == 0) // all output counters selected
                begin
                    for (i = 0; i < num_output_cntrs; i = i + 1)
                        c_ph_val_tmp[i] = (phaseupdown == 1'b1) ? 
                                    (c_ph_val_tmp[i] + 1) % num_phase_taps :
                                    (c_ph_val_tmp[i] == 0) ? num_phase_taps - 1 : (c_ph_val_tmp[i] - 1) % num_phase_taps ;
                end
                else if (phasecounterselect == 1) // select M counter
                begin
                    m_ph_val_tmp = (phaseupdown == 1'b1) ? 
                                (m_ph_val + 1) % num_phase_taps :
                                (m_ph_val == 0) ? num_phase_taps - 1 : (m_ph_val - 1) % num_phase_taps ;
                end
                else // select C counters
                begin
                    select_counter = phasecounterselect - 2;
                    c_ph_val_tmp[select_counter] =  (phaseupdown == 1'b1) ? 
                                            (c_ph_val_tmp[select_counter] + 1) % num_phase_taps :
                                            (c_ph_val_tmp[select_counter] == 0) ? num_phase_taps - 1 : (c_ph_val_tmp[select_counter] - 1) % num_phase_taps ;
                end
                update_phase <= 1'b1;
            end 
           
        end
        phasestep_high_count = phasestep_high_count + 1;
       
    end
end

// Latch phase enable (same as phasestep) on neg edge of scan clock
always @(negedge scanclk)
begin
    phasestep_reg <= phasestep;
end

always @(posedge phasestep) 
begin
    if (update_phase == 1'b0) phasestep_high_count = 0; // phase adjustments must be 1 cycle apart
                                                        // if not, next phasestep cycle is skipped
end

// ************ PLL Full Reconfiguration ************* //
assign update_conf_latches = configupdate;


        // reset counter transfer flags
    always @(negedge scandone_tmp)
    begin
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        update_conf_latches_reg <= 1'b0;
    end


    always @(posedge update_conf_latches)
    begin
        initiate_reconfig <= 1'b1;
    end
   
    always @(posedge areset)
    begin
        if (scandone_tmp == 1'b1) scandone_tmp = 1'b0;
    end
   
    always @(posedge scanclk)
    begin
        if (initiate_reconfig == 1'b1) 
        begin
            initiate_reconfig <= 1'b0;
            $display ("NOTE : PLL Reprogramming initiated ....");
            $display ("Time: %0t  Instance: %m", $time);

            scandone_tmp <= #(scanclk_period) 1'b1;
            update_conf_latches_reg <= update_conf_latches;

            error = 0;
            reconfig_err = 0;
            scanread_setup_violation = 0;

            // save old values
            cp_curr_old = cp_curr_val;
            lfc_old = lfc_val;
            lfr_old = lfr_val;
            vco_old = vco_cur;
            // save old values of bit settings
            cp_curr_bit_setting = scan_data[14:16];
            lfc_val_bit_setting = scan_data[1:2];
            lfr_val_bit_setting = scan_data[3:7];
            vco_val_bit_setting = scan_data[8];

            // LF unused : bit 1
            // LF Capacitance : bits 1,2 : all values are legal
            if ((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right"))
                lfc_val = fpll_loop_filter_c_arr[scan_data[1:2]];
            else
                lfc_val = loop_filter_c_arr[scan_data[1:2]];

            // LF Resistance : bits 3-7
            // valid values - 00000,00100,10000,10100,11000,11011,11100,11110
            if (((scan_data[3:7] == 5'b00000) || (scan_data[3:7] == 5'b00100)) || 
                ((scan_data[3:7] == 5'b10000) || (scan_data[3:7] == 5'b10100)) ||
                ((scan_data[3:7] == 5'b11000) || (scan_data[3:7] == 5'b11011)) ||
                ((scan_data[3:7] == 5'b11100) || (scan_data[3:7] == 5'b11110))
            )
            begin
                lfr_val =   (scan_data[3:7] == 5'b00000) ? "20" :
                            (scan_data[3:7] == 5'b00100) ? "16" :
                            (scan_data[3:7] == 5'b10000) ? "12" :
                            (scan_data[3:7] == 5'b10100) ? "8" :
                            (scan_data[3:7] == 5'b11000) ? "6" :
                            (scan_data[3:7] == 5'b11011) ? "4" : 
                            (scan_data[3:7] == 5'b11100) ? "2" : "1";
            end

            //VCO post scale value
            if (scan_data[8] === 1'b1)  // vco_post_scale = 1
            begin
                i_vco_max = i_vco_max_no_division/2;
                i_vco_min = i_vco_min_no_division/2;
                vco_cur = 1;
            end
            else
            begin
                i_vco_max = vco_max;
                i_vco_min = vco_min; 
                vco_cur = 2;
            end          

            // CP
            // Bit 8 : CRBYPASS
            // Bit 9-13 : unused
            // Bits 14-16 : all values are legal
            cp_curr_val = scan_data[14:16];

            // save old values for display info.
            for (i=0; i<=1; i=i+1)
            begin
                m_val_old[i] = m_val[i];
                n_val_old[i] = n_val[i];
                m_mode_val_old[i] = m_mode_val[i];
                n_mode_val_old[i] = n_mode_val[i];
            end
            for (i=0; i< num_output_cntrs; i=i+1)
            begin
                c_high_val_old[i] = c_high_val[i];
                c_low_val_old[i] = c_low_val[i];
                c_mode_val_old[i] = c_mode_val[i];
            end

            // M counter
            // 1. Mode - bypass (bit 17)
            if (scan_data[17] == 1'b1)
                n_mode_val[0] = "bypass";
            // 3. Mode - odd/even (bit 26)
            else if (scan_data[26] == 1'b1)
                n_mode_val[0] = "   odd";         
            else
                n_mode_val[0] = "  even";         
            // 2. High (bit 18-25)
                n_hi = scan_data[18:25];
            // 4. Low (bit 27-34)
                n_lo = scan_data[27:34]; 


            // N counter
            // 1. Mode - bypass (bit 35)
            if (scan_data[35] == 1'b1)
                m_mode_val[0] = "bypass";
            // 3. Mode - odd/even (bit 44)
            else if (scan_data[44] == 1'b1)
                m_mode_val[0] = "   odd";
            else
                m_mode_val[0] = "  even";
            
            // 2. High (bit 36-43)
                m_hi = scan_data[36:43];
            
            // 4. Low (bit 45-52)
                m_lo = scan_data[45:52]; 


            
//Update the current M and N counter values if the counters are NOT bypassed

if (m_mode_val[0] != "bypass")
m_val[0] = m_hi + m_lo;
if (n_mode_val[0] != "bypass")  
n_val[0] = n_hi + n_lo;
            


            // C counters (start bit 53) bit 1:mode(bypass),bit 2-9:high,bit 10:mode(odd/even),bit 11-18:low

            for (i = 0; i < num_output_cntrs; i = i + 1)
            begin
                // 1. Mode - bypass
                if (scan_data[53 + i*18 + 0] == 1'b1)
                        c_mode_val_tmp[i] = "bypass";
                // 3. Mode - odd/even
                else if (scan_data[53 + i*18 + 9] == 1'b1)
                    c_mode_val_tmp[i] = "   odd";
                else
                    c_mode_val_tmp[i] = "  even";
                    
                // 2. Hi
                for (j = 1; j <= 8; j = j + 1)
                    c_val[8-j] = scan_data[53 + i*18 + j];
                c_hval[i] = c_val[7:0];
                if (c_hval[i] !== 32'h00000000)
                    c_high_val_tmp[i] = c_hval[i];
                else
                    c_high_val_tmp[i] = 9'b100000000;
                // 4. Low 
                for (j = 10; j <= 17; j = j + 1)
                    c_val[17 - j] = scan_data[53 + i*18 + j]; 
                c_lval[i] = c_val[7:0];
                if (c_lval[i] !== 32'h00000000)
                    c_low_val_tmp[i] = c_lval[i];  
                else
                    c_low_val_tmp[i] = 9'b100000000; 
            end

            // Legality Checks
            
            if (m_mode_val[0] != "bypass")
            begin
            if ((m_hi !== m_lo) && (m_mode_val[0] != "   odd"))
            begin
                    reconfig_err = 1;
                    $display ("Warning : The M counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
            end
            else if (m_hi !== 8'b00000000)
            begin
                    // counter value
                    m_val_tmp[0] = m_hi + m_lo;
            end
            else
                m_val_tmp[0] =  9'b100000000; 
            end
            else
                m_val_tmp[0] = 8'b00000001;
                
            if (n_mode_val[0] != "bypass")
            begin
            if ((n_hi !== n_lo) && (n_mode_val[0] != "   odd"))
            begin
                    reconfig_err = 1;
                    $display ("Warning : The N counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
            end
            else if (n_hi !== 8'b00000000)
            begin
                    // counter value
                    n_val[0] = n_hi + n_lo;
            end
            else
                n_val[0] =  9'b100000000; 
            end
            else
                n_val[0] = 8'b00000001;
                           
                 

// TODO : Give warnings/errors in the following cases?
// 1. Illegal counter values (error)
// 2. Change of mode (warning)
// 3. Only 50% duty cycle allowed for M counter (odd mode - hi-lo=1,even - hi-lo=0)

        end
    end
    
    // Self reset on loss of lock
    assign reset_self = (l_self_reset_on_loss_lock == "on") ? ~pll_is_locked : 1'b0;

    always @(posedge reset_self)
    begin
        $display (" Note : %s PLL self reset due to loss of lock", family_name);
        $display ("Time: %0t  Instance: %m", $time);
    end
    
    // Phase shift on /o counters
    
    always @(schedule_vco or areset)
    begin
        sched_time = 0;
    
        for (i = 0; i <= 7; i=i+1)
            last_phase_shift[i] = phase_shift[i];
     
        cycle_to_adjust = 0;
        l_index = 1;
        m_times_vco_period = new_m_times_vco_period;
            
        // give appropriate messages
        // if areset was asserted
        if (areset === 1'b1 && areset_last_value !== areset)
        begin
            $display (" Note : %s PLL was reset", family_name);
            $display ("Time: %0t  Instance: %m", $time);
            // reset lock parameters
            pll_is_locked = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
            tap0_is_active = 0;
            for (x = 0; x <= 7; x=x+1)
                vco_tap[x] <= 1'b0;
        end
    
        // illegal value on areset
        if (areset === 1'bx && (areset_last_value === 1'b0 || areset_last_value === 1'b1))
        begin
            $display("Warning : Illegal value 'X' detected on ARESET input");
            $display ("Time: %0t  Instance: %m", $time);
        end
    
        if ((areset == 1'b1))
        begin
            pll_is_in_reset = 1;
            got_first_refclk = 0;
            got_second_refclk = 0;
        end
                            
        if ((schedule_vco !== schedule_vco_last_value) && (areset == 1'b1 || stop_vco == 1'b1))
        begin
   
            // drop VCO taps to 0
            for (i = 0; i <= 7; i=i+1)
            begin
                for (j = 0; j <= last_phase_shift[i] + 1; j=j+1)
                    vco_out[i] <= #(j) 1'b0;
                phase_shift[i] = 0;
                last_phase_shift[i] = 0;
            end
    
            // reset lock parameters
            pll_is_locked = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
    
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = 0;
            got_first_fbclk = 0;
            fbclk_time = 0;
            first_fbclk_time = 0;
            fbclk_period = 0;
    
            first_schedule = 1;
            vco_val = 0;
            vco_period_was_phase_adjusted = 0;
            phase_adjust_was_scheduled = 0;

            // reset all counter phase tap values to POF programmed values
            m_ph_val = m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
                c_ph_val[i] = c_ph_val_orig[i];
    
        end else if (areset === 1'b0 && stop_vco === 1'b0)
        begin
            // else note areset deassert time
            // note it as refclk_time to prevent false triggering
            // of stop_vco after areset
            if (areset === 1'b0 && areset_last_value === 1'b1 && pll_is_in_reset === 1'b1)
            begin
                refclk_time = $time;
                locked_tmp = 1'b0;
            end
            pll_is_in_reset = 0;
    
            // calculate loop_xplier : this will be different from m_val in ext. fbk mode
            loop_xplier = m_val[0];
            loop_initial = i_m_initial - 1;
            loop_ph = m_ph_val;
    
            // convert initial value to delay
            initial_delay = (loop_initial * m_times_vco_period)/loop_xplier;
    
            // convert loop ph_tap to delay
            rem = m_times_vco_period % loop_xplier;
            vco_per = m_times_vco_period/loop_xplier;
            if (rem != 0)
                vco_per = vco_per + 1;
            fbk_phase = (loop_ph * vco_per)/8;
    
            pull_back_M = initial_delay + fbk_phase;
    
            total_pull_back = pull_back_M;
            if (l_simulation_type == "timing")
                total_pull_back = total_pull_back + pll_compensation_delay;
    
            while (total_pull_back > refclk_period)
                total_pull_back = total_pull_back - refclk_period;
    
            if (total_pull_back > 0)
                offset = refclk_period - total_pull_back;
            else
                offset = 0;
    
            fbk_delay = total_pull_back - fbk_phase;
            if (fbk_delay < 0)
            begin
                offset = offset - fbk_phase;
                fbk_delay = total_pull_back;
            end
    
            // assign m_delay
            m_delay = fbk_delay;
    
            for (i = 1; i <= loop_xplier; i=i+1)
            begin
                // adjust cycles
                tmp_vco_per = m_times_vco_period/loop_xplier;
                if (rem != 0 && l_index <= rem)
                begin
                    tmp_rem = (loop_xplier * l_index) % rem;
                    cycle_to_adjust = (loop_xplier * l_index) / rem;
                    if (tmp_rem != 0)
                        cycle_to_adjust = cycle_to_adjust + 1;
                end
                if (cycle_to_adjust == i)
                begin
                    tmp_vco_per = tmp_vco_per + 1;
                    l_index = l_index + 1;
                end
    
                // calculate high and low periods
                high_time = tmp_vco_per/2;
                if (tmp_vco_per % 2 != 0)
                    high_time = high_time + 1;
                low_time = tmp_vco_per - high_time;
    
                // schedule the rising and falling egdes
                for (j=0; j<=1; j=j+1)
                begin
                    vco_val = ~vco_val;
                    if (vco_val == 1'b0)
                        sched_time = sched_time + high_time;
                    else
                        sched_time = sched_time + low_time;
    
                    // schedule taps with appropriate phase shifts
                    for (k = 0; k <= 7; k=k+1)
                    begin
                        phase_shift[k] = (k*tmp_vco_per)/8;
                        if (first_schedule)
                            vco_out[k] <= #(sched_time + phase_shift[k]) vco_val;
                        else
                            vco_out[k] <= #(sched_time + last_phase_shift[k]) vco_val;
                    end
                end
            end
            if (first_schedule)
            begin
                vco_val = ~vco_val;
                if (vco_val == 1'b0)
                    sched_time = sched_time + high_time;
                else
                    sched_time = sched_time + low_time;
                for (k = 0; k <= 7; k=k+1)
                begin
                    phase_shift[k] = (k*tmp_vco_per)/8;
                    vco_out[k] <= #(sched_time+phase_shift[k]) vco_val;
                end
                first_schedule = 0;
            end

            schedule_vco <= #(sched_time) ~schedule_vco;
            if (vco_period_was_phase_adjusted)
            begin
                m_times_vco_period = refclk_period;
                new_m_times_vco_period = refclk_period;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 1;
    
                tmp_vco_per = m_times_vco_period/loop_xplier;
                for (k = 0; k <= 7; k=k+1)
                    phase_shift[k] = (k*tmp_vco_per)/8;
            end
        end
    
        areset_last_value = areset;
        schedule_vco_last_value = schedule_vco;
    
    end

    // PFD enable
    always @(pfdena)
    begin
        if (pfdena === 1'b0)
        begin
            if (pll_is_locked)
                locked_tmp = 1'bx;
            pll_is_locked = 0;
            cycles_to_lock = 0;
            $display (" Note : PFDENA was deasserted");
            $display ("Time: %0t  Instance: %m", $time);
        end
        else if (pfdena === 1'b1 && pfdena_last_value === 1'b0)
        begin
            // PFD was disabled, now enabled again
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = $time;
        end
        pfdena_last_value = pfdena;
    end

    always @(negedge refclk or negedge fbclk)
    begin
        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    // Bypass lock detect
        
    always @(posedge refclk)
    begin
    if (test_bypass_lock_detect == "on")
        begin
            if (pfdena === 1'b1)
            begin
                    cycles_pfd_low = 0;
                    if (pfd_locked == 1'b0)
                    begin
                    if (cycles_pfd_high == lock_high)
                    begin
                        $display ("Note : %s PLL locked in test mode on PFD enable assert", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        pfd_locked <= 1'b1;
                    end
                    cycles_pfd_high = cycles_pfd_high + 1;
                        end
                end
            if (pfdena === 1'b0)
            begin
                    cycles_pfd_high = 0;
                    if (pfd_locked == 1'b1)
                    begin
                    if (cycles_pfd_low == lock_low)
                    begin
                        $display ("Note : %s PLL lost lock in test mode on PFD enable deassert", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        pfd_locked <= 1'b0;
                    end
                    cycles_pfd_low = cycles_pfd_low + 1;
                        end
                end
        end
    end
    
    always @(posedge scandone_tmp or posedge locked_tmp)
    begin
        if(scandone_tmp == 1)
            pll_has_just_been_reconfigured <= 1;
        else
            pll_has_just_been_reconfigured <= 0;
    end
    
    // VCO Frequency Range check
    always @(posedge refclk or posedge fbclk)
    begin
        if (refclk == 1'b1 && refclk_last_value !== refclk && areset === 1'b0)
        begin
            if (! got_first_refclk)
            begin
                got_first_refclk = 1;
            end else
            begin
                got_second_refclk = 1;
                refclk_period = $time - refclk_time;

                // check if incoming freq. will cause VCO range to be
                // exceeded
                if ((i_vco_max != 0 && i_vco_min != 0) && (pfdena === 1'b1) &&        
                    ((refclk_period/loop_xplier > i_vco_max) || 
                    (refclk_period/loop_xplier < i_vco_min)) ) 
                begin
                    if (pll_is_locked == 1'b1)
                    begin
                        if (refclk_period/loop_xplier > i_vco_max)
                        begin
                            $display ("Warning : Input clock freq. is over VCO range. %s PLL may lose lock", family_name);
                            vco_over = 1'b1;
                        end
                        if (refclk_period/loop_xplier < i_vco_min)
                        begin
                            $display ("Warning : Input clock freq. is under VCO range. %s PLL may lose lock", family_name);
                            vco_under = 1'b1;
                        end

                        $display ("Time: %0t  Instance: %m", $time);
                        if (inclk_out_of_range === 1'b1)
                        begin
                            // unlock
                            pll_is_locked = 0;
                            locked_tmp = 0;
                            cycles_to_lock = 0;
                            $display ("Note : %s PLL lost lock", family_name);
                            $display ("Time: %0t  Instance: %m", $time);
                            vco_period_was_phase_adjusted = 0;
                            phase_adjust_was_scheduled = 0;
                        end
                    end
                    else begin
                        if (no_warn == 1'b0)
                        begin
                            if (refclk_period/loop_xplier > i_vco_max)
                            begin
                                $display ("Warning : Input clock freq. is over VCO range. %s PLL may lose lock", family_name);
                                vco_over = 1'b1;
                            end
                            if (refclk_period/loop_xplier < i_vco_min)
                            begin
                                $display ("Warning : Input clock freq. is under VCO range. %s PLL may lose lock", family_name);
                                vco_under = 1'b1;
                            end
                            $display ("Time: %0t  Instance: %m", $time);
                            no_warn = 1'b1;
                        end
                    end
                    inclk_out_of_range = 1;
                end
                else begin
                    vco_over  = 1'b0;
                    vco_under = 1'b0;
                    inclk_out_of_range = 0;
                    no_warn = 1'b0;
                end

            end
            if (stop_vco == 1'b1)
            begin
                stop_vco = 0;
                schedule_vco = ~schedule_vco;
            end
            refclk_time = $time;
        end

        // Update M counter value on feedback clock edge
        
        if (fbclk == 1'b1 && fbclk_last_value !== fbclk)
        begin
            if (update_conf_latches === 1'b1)
            begin
                m_val[0] <= m_val_tmp[0];
                m_val[1] <= m_val_tmp[1];
            end
            if (!got_first_fbclk)
            begin
                got_first_fbclk = 1;
                first_fbclk_time = $time;
            end
            else
                fbclk_period = $time - fbclk_time;

            // need refclk_period here, so initialized to proper value above
            if ( ( ($time - refclk_time > 1.5 * refclk_period) && pfdena === 1'b1 && pll_is_locked === 1'b1) ||
                ( ($time - refclk_time > 5 * refclk_period) && (pfdena === 1'b1) && (pll_has_just_been_reconfigured == 0) ) ||
                ( ($time - refclk_time > 50 * refclk_period) && (pfdena === 1'b1) && (pll_has_just_been_reconfigured == 1) ) )
            begin
                stop_vco = 1;
                // reset
                got_first_refclk = 0;
                got_first_fbclk = 0;
                got_second_refclk = 0;
                if (pll_is_locked == 1'b1)
                begin
                    pll_is_locked = 0;
                    locked_tmp = 0;
                    $display ("Note : %s PLL lost lock due to loss of input clock or the input clock is not detected within the allowed time frame.", family_name);
                    if ((i_vco_max == 0) && (i_vco_min == 0))
                        $display ("Note : Please run timing simulation to check whether the input clock is operating within the supported VCO range or not.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                cycles_to_lock = 0;
                cycles_to_unlock = 0;
                first_schedule = 1;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 0;
                tap0_is_active = 0;
                for (x = 0; x <= 7; x=x+1)
                    vco_tap[x] <= 1'b0;
            end
            fbclk_time = $time;
        end
        
                
        // Core lock functionality
        
        if (got_second_refclk && pfdena === 1'b1 && (!inclk_out_of_range))
        begin
            // now we know actual incoming period
            if (abs(fbclk_time - refclk_time) <= lock_window || (got_first_fbclk && abs(refclk_period - abs(fbclk_time - refclk_time)) <= lock_window))
            begin
                // considered in phase
                if (cycles_to_lock == real_lock_high)
                begin
                    if (pll_is_locked === 1'b0)
                    begin
                        $display (" Note : %s PLL locked to incoming clock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    pll_is_locked = 1;
                    locked_tmp = 1;
                    cycles_to_unlock = 0;
                end
                // increment lock counter only if the second part of the above
                // time check is not true
                if (!(abs(refclk_period - abs(fbclk_time - refclk_time)) <= lock_window))
                begin
                    cycles_to_lock = cycles_to_lock + 1;
                end

                // adjust m_times_vco_period
                new_m_times_vco_period = refclk_period;

            end else
            begin
                // if locked, begin unlock
                if (pll_is_locked)
                begin
                    cycles_to_unlock = cycles_to_unlock + 1;
                    if (cycles_to_unlock == lock_low)
                    begin
                        pll_is_locked = 0;
                        locked_tmp = 0;
                        cycles_to_lock = 0;
                        $display ("Note : %s PLL lost lock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        vco_period_was_phase_adjusted = 0;
                        phase_adjust_was_scheduled = 0;
                        got_first_refclk = 0;
                        got_first_fbclk = 0;
                        got_second_refclk = 0;
                    end
                end
                if (abs(refclk_period - fbclk_period) <= 2)
                begin
                    // frequency is still good
                    if ($time == fbclk_time && (!phase_adjust_was_scheduled))
                    begin
                        if (abs(fbclk_time - refclk_time) > refclk_period/2)
                        begin
                            new_m_times_vco_period = abs(m_times_vco_period + (refclk_period - abs(fbclk_time - refclk_time)));
                            vco_period_was_phase_adjusted = 1;
                        end else
                        begin
                            new_m_times_vco_period = abs(m_times_vco_period - abs(fbclk_time - refclk_time));
                            vco_period_was_phase_adjusted = 1;
                        end
                    end
                end else
                begin
                    new_m_times_vco_period = refclk_period;
                    phase_adjust_was_scheduled = 0;
                end
            end
        end

        if (reconfig_err == 1'b1)
        begin
            locked_tmp = 0;
        end

        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    assign clk_tmp[0] = i_clk0_counter == "c0" ? c0_clk : i_clk0_counter == "c1" ? c1_clk : i_clk0_counter == "c2" ? c2_clk : i_clk0_counter == "c3" ? c3_clk : i_clk0_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[1] = i_clk1_counter == "c0" ? c0_clk : i_clk1_counter == "c1" ? c1_clk : i_clk1_counter == "c2" ? c2_clk : i_clk1_counter == "c3" ? c3_clk : i_clk1_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[2] = i_clk2_counter == "c0" ? c0_clk : i_clk2_counter == "c1" ? c1_clk : i_clk2_counter == "c2" ? c2_clk : i_clk2_counter == "c3" ? c3_clk : i_clk2_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[3] = i_clk3_counter == "c0" ? c0_clk : i_clk3_counter == "c1" ? c1_clk : i_clk3_counter == "c2" ? c2_clk : i_clk3_counter == "c3" ? c3_clk : i_clk3_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[4] = i_clk4_counter == "c0" ? c0_clk : i_clk4_counter == "c1" ? c1_clk : i_clk4_counter == "c2" ? c2_clk : i_clk4_counter == "c3" ? c3_clk : i_clk4_counter == "c4" ? c4_clk : 1'b0;

assign clk_out_pfd[0] = (pfd_locked == 1'b1) ? clk_tmp[0] : 1'bx;
assign clk_out_pfd[1] = (pfd_locked == 1'b1) ? clk_tmp[1] : 1'bx;
assign clk_out_pfd[2] = (pfd_locked == 1'b1) ? clk_tmp[2] : 1'bx;
assign clk_out_pfd[3] = (pfd_locked == 1'b1) ? clk_tmp[3] : 1'bx;
assign clk_out_pfd[4] = (pfd_locked == 1'b1) ? clk_tmp[4] : 1'bx;

    assign clk_out[0] = (test_bypass_lock_detect == "on") ? clk_out_pfd[0] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[0] : 1'bx);
    assign clk_out[1] = (test_bypass_lock_detect == "on") ? clk_out_pfd[1] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[1] : 1'bx);
    assign clk_out[2] = (test_bypass_lock_detect == "on") ? clk_out_pfd[2] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[2] : 1'bx);
    assign clk_out[3] = (test_bypass_lock_detect == "on") ? clk_out_pfd[3] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[3] : 1'bx);
    assign clk_out[4] = (test_bypass_lock_detect == "on") ? clk_out_pfd[4] : ((areset === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[4] : 1'bx);

    // ACCELERATE OUTPUTS
    and (clk[0], 1'b1, clk_out[0]);
    and (clk[1], 1'b1, clk_out[1]);
    and (clk[2], 1'b1, clk_out[2]);
    and (clk[3], 1'b1, clk_out[3]);
    and (clk[4], 1'b1, clk_out[4]);

    and (scandataout, 1'b1, scandata_out);
    and (scandone, 1'b1, scandone_tmp);

assign fbout = fbclk;
assign vcooverrange  = (vco_range_detector_high_bits == -1) ? 1'bz : vco_over;
assign vcounderrange = (vco_range_detector_low_bits == -1) ? 1'bz :vco_under;
assign phasedone = ~update_phase;

endmodule // MF_cycloneiii_pll
// cycloneiii_msg


///////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_cycloneiiigl_m_cntr
//
// Description : Simulation model for the M counter. This is the
//               loop feedback counter for the cycloneiiigl PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 fs / 1 fs
module MF_cycloneiiigl_m_cntr   ( clk,
                            reset,
                            cout,
                            initial_value,
                            modulus,
                            time_delay);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] initial_value;
    input [31:0] modulus;
    input [31:0] time_delay;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
            cout_tmp <= tmp_cout;
        end
        else begin
            if (clk_last_value !== clk)
            begin
                if (clk === 1'b1 && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
                cout_tmp <= #(time_delay) tmp_cout;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                    cout_tmp <= #(time_delay) tmp_cout;
                end
            end
        end
        end
        clk_last_value = clk;

//        cout_tmp <= #(time_delay) tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // MF_cycloneiiigl_m_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_cycloneiiigl_n_cntr
//
// Description : Simulation model for the N counter. This is the
//               input clock divide counter for the cycloneiiigl PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 fs / 1 fs
module MF_cycloneiiigl_n_cntr   ( clk,
                            reset,
                            cout,
                            modulus);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] modulus;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk == 1 && clk_last_value !== clk && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                end
            end
        end
        clk_last_value = clk;

    end

    assign cout = tmp_cout;

endmodule // MF_cycloneiiigl_n_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_cycloneiiigl_scale_cntr
//
// Description : Simulation model for the output scale-down counters.
//               This is a common model for the C0-C4
//               output counters of the cycloneiiigl PLL.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 fs / 1 fs
module MF_cycloneiiigl_scale_cntr   ( clk,
                                reset,
                                cout,
                                high,
                                low,
                                initial_value,
                                mode,
                                ph_tap);

    // INPUT PORTS
    input clk;
    input reset;
    input [31:0] high;
    input [31:0] low;
    input [31:0] initial_value;
    input [8*6:1] mode;
    input [31:0] ph_tap;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg init;
    integer count;
    integer output_shift_count;
    reg cout_tmp;

    initial
    begin
        count = 1;
        first_rising_edge = 0;
        tmp_cout = 0;
        output_shift_count = 1;
    end

    always @(clk or reset)
    begin
        if (init !== 1'b1)
        begin
            clk_last_value = 0;
            init = 1'b1;
        end
        if (reset)
        begin
            count = 1;
            output_shift_count = 1;
            tmp_cout = 0;
            first_rising_edge = 0;
        end
        else if (clk_last_value !== clk)
        begin
            if (mode == "   off")
                tmp_cout = 0;
            else if (mode == "bypass")
            begin
                tmp_cout = clk;
                first_rising_edge = 1;
            end
            else if (first_rising_edge == 0)
            begin
                if (clk == 1)
                begin
                    if (output_shift_count == initial_value)
                    begin
                        tmp_cout = clk;
                        first_rising_edge = 1;
                    end
                    else
                        output_shift_count = output_shift_count + 1;
                end
            end
            else if (output_shift_count < initial_value)
            begin
                if (clk == 1)
                    output_shift_count = output_shift_count + 1;
            end
            else
            begin
                count = count + 1;
                if (mode == "  even" && (count == (high*2) + 1))
                    tmp_cout = 0;
                else if (mode == "   odd" && (count == (high*2)))
                    tmp_cout = 0;
                else if (count == (high + low)*2 + 1)
                begin
                    tmp_cout = 1;
                    count = 1;        // reset count
                end
            end
        end
        clk_last_value = clk;
        cout_tmp <= tmp_cout;
    end

    and (cout, cout_tmp, 1'b1);

endmodule // MF_cycloneiiigl_scale_cntr

///////////////////////////////////////////////////////////////////////////////
//
// Module Name : cycloneiiigl_post_divider
//
// Description : Simulation model that models the icdrclk output.
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps
module cycloneiiigl_post_divider   ( clk,
                            reset,
                            cout);

    // PARAMETER
    parameter dpa_divider = 1;

    // INPUT PORTS
    input clk;
    input reset;

    // OUTPUT PORTS
    output cout;

    // INTERNAL VARIABLES AND NETS
    integer count;
    reg tmp_cout;
    reg first_rising_edge;
    reg clk_last_value;
    reg cout_tmp;
    integer modulus;

    initial
    begin
        count = 1;
        first_rising_edge = 1;
        clk_last_value = 0;
        modulus = (dpa_divider == 0) ? 1 : dpa_divider;
    end

    always @(reset or clk)
    begin
        if (reset)
        begin
            count = 1;
            tmp_cout = 0;
            first_rising_edge = 1;
        end
        else begin
            if (clk == 1 && clk_last_value !== clk && first_rising_edge)
            begin
                first_rising_edge = 0;
                tmp_cout = clk;
            end
            else if (first_rising_edge == 0)
            begin
                if (count < modulus)
                    count = count + 1;
                else
                begin
                    count = 1;
                    tmp_cout = ~tmp_cout;
                end
            end
        end
        clk_last_value = clk;

    end

    assign cout = tmp_cout;

endmodule // cycloneiiigl_post_divider


//////////////////////////////////////////////////////////////////////////////
//
// Module Name : MF_cycloneiiigl_pll
//
// Description : Simulation model for the cycloneiiigl PLL.
// 
// Limitations : Does not support Spread Spectrum and Bandwidth.
//
// Outputs     : Up to 10 output clocks, each defined by its own set of
//               parameters. Locked output (active high) indicates when the
//               PLL locks. clkbad and activeclock are used for
//               clock switchover to indicate which input clock has gone
//               bad, when the clock switchover initiates and which input
//               clock is being used as the reference, respectively.
//               scandataout is the data output of the serial scan chain.
//
// New Features : The list below outlines key new features in cycloneiiigl:
//                1. Dynamic Phase Reconfiguration
//                2. Dynamic PLL Reconfiguration (different protocol)
//                3. More output counters
//////////////////////////////////////////////////////////////////////////////

`timescale 1 fs/1 fs
`define CYCIIIGL_PLL_WORD_LENGTH 18

module MF_cycloneiiigl_pll (inclk,
                    fbin,
                    fbout,
                    clkswitch,
                    areset,
                    pfdena,
                    scanclk,
                    scandata,
                    scanclkena,
                    configupdate,
                    clk,
                    phasecounterselect,
                    phaseupdown,
                    phasestep,
                    clkbad,
                    activeclock,
                    locked,
                    scandataout,
                    scandone,
                    phasedone,
                    vcooverrange,
                    vcounderrange,
                    fref,
                    icdrclk
                    );

    parameter operation_mode                       = "normal";
    parameter pll_type                             = "auto"; // auto,fast(left_right),enhanced(top_bottom)
    parameter compensate_clock                     = "clock0";


    parameter inclk0_input_frequency               = 0;
    parameter inclk1_input_frequency               = 0;

    parameter self_reset_on_loss_lock        = "off";
    parameter switch_over_type                     = "auto";

    parameter switch_over_counter                  = 1;
    parameter enable_switch_over_counter           = "off";

    parameter bandwidth                            = 0;
    parameter bandwidth_type                       = "auto";
    parameter use_dc_coupling                      = "false";

    parameter lock_high = 0; // 0 .. 4095
    parameter lock_low = 0;  // 0 .. 7
    parameter lock_window_ui = "0.05"; // "0.05", "0.1", "0.15", "0.2"
    parameter test_bypass_lock_detect              = "off";
    
    parameter clk0_output_frequency                = 0;
    parameter clk0_multiply_by                     = 0;
    parameter clk0_divide_by                       = 0;
    parameter clk0_phase_shift                     = "0";
    parameter clk0_duty_cycle                      = 50;

    parameter clk1_output_frequency                = 0;
    parameter clk1_multiply_by                     = 0;
    parameter clk1_divide_by                       = 0;
    parameter clk1_phase_shift                     = "0";
    parameter clk1_duty_cycle                      = 50;

    parameter clk2_output_frequency                = 0;
    parameter clk2_multiply_by                     = 0;
    parameter clk2_divide_by                       = 0;
    parameter clk2_phase_shift                     = "0";
    parameter clk2_duty_cycle                      = 50;

    parameter clk3_output_frequency                = 0;
    parameter clk3_multiply_by                     = 0;
    parameter clk3_divide_by                       = 0;
    parameter clk3_phase_shift                     = "0";
    parameter clk3_duty_cycle                      = 50;

    parameter clk4_output_frequency                = 0;
    parameter clk4_multiply_by                     = 0;
    parameter clk4_divide_by                       = 0;
    parameter clk4_phase_shift                     = "0";
    parameter clk4_duty_cycle                      = 50;

    parameter pfd_min                              = 0;
    parameter pfd_max                              = 0;
    parameter vco_min                              = 0;
    parameter vco_max                              = 0;
    parameter vco_center                           = 0;

    // ADVANCED USE PARAMETERS
    parameter m_initial = 1;
    parameter m = 0;
    parameter n = 1;

    parameter c0_high = 1;
    parameter c0_low = 1;
    parameter c0_initial = 1;
    parameter c0_mode = "bypass";
    parameter c0_ph = 0;

    parameter c1_high = 1;
    parameter c1_low = 1;
    parameter c1_initial = 1;
    parameter c1_mode = "bypass";
    parameter c1_ph = 0;

    parameter c2_high = 1;
    parameter c2_low = 1;
    parameter c2_initial = 1;
    parameter c2_mode = "bypass";
    parameter c2_ph = 0;

    parameter c3_high = 1;
    parameter c3_low = 1;
    parameter c3_initial = 1;
    parameter c3_mode = "bypass";
    parameter c3_ph = 0;

    parameter c4_high = 1;
    parameter c4_low = 1;
    parameter c4_initial = 1;
    parameter c4_mode = "bypass";
    parameter c4_ph = 0;

    parameter m_ph = 0;

    parameter clk0_counter = "unused";
    parameter clk1_counter = "unused";
    parameter clk2_counter = "unused";
    parameter clk3_counter = "unused";
    parameter clk4_counter = "unused";

    parameter c1_use_casc_in = "off";
    parameter c2_use_casc_in = "off";
    parameter c3_use_casc_in = "off";
    parameter c4_use_casc_in = "off";

    parameter m_test_source  = -1;
    parameter c0_test_source = -1;
    parameter c1_test_source = -1;
    parameter c2_test_source = -1;
    parameter c3_test_source = -1;
    parameter c4_test_source = -1;

    parameter vco_multiply_by = 0;
    parameter vco_divide_by = 0;
    parameter vco_post_scale = 1; // 1 .. 2
    parameter vco_frequency_control = "auto";
    parameter vco_phase_shift_step = 0;

    parameter dpa_multiply_by = 0;
    parameter dpa_divide_by = 0;
    parameter dpa_divider = 1;

    parameter charge_pump_current = 10;
    parameter loop_filter_r = "1.0";    // "1.0", "2.0", "4.0", "6.0", "8.0", "12.0", "16.0", "20.0"
    parameter loop_filter_c = 0;        // 0 , 2 , 4

    parameter pll_compensation_delay = 0;
    parameter simulation_type = "functional";

// SIMULATION_ONLY_PARAMETERS_BEGIN

    parameter down_spread                          = "0.0";
    parameter lock_c = 4;

    parameter sim_gate_lock_device_behavior        = "off";

    parameter clk0_phase_shift_num = 0;
    parameter clk1_phase_shift_num = 0;
    parameter clk2_phase_shift_num = 0;
    parameter clk3_phase_shift_num = 0;
    parameter clk4_phase_shift_num = 0;
    parameter family_name = "cycloneiiigl";

    parameter clk0_use_even_counter_mode = "off";
    parameter clk1_use_even_counter_mode = "off";
    parameter clk2_use_even_counter_mode = "off";
    parameter clk3_use_even_counter_mode = "off";
    parameter clk4_use_even_counter_mode = "off";

    parameter clk0_use_even_counter_value = "off";
    parameter clk1_use_even_counter_value = "off";
    parameter clk2_use_even_counter_value = "off";
    parameter clk3_use_even_counter_value = "off";
    parameter clk4_use_even_counter_value = "off";

    // TEST ONLY
    
    parameter init_block_reset_a_count = 1;
    parameter init_block_reset_b_count = 1;

// SIMULATION_ONLY_PARAMETERS_END
    
// LOCAL_PARAMETERS_BEGIN

    parameter phase_counter_select_width = 3;
    parameter lock_window = 5000;
    parameter inclk0_freq = inclk0_input_frequency * 1000;
    parameter inclk1_freq = inclk1_input_frequency * 1000;
   
parameter charge_pump_current_bits = 0;
parameter lock_window_ui_bits = 0;
parameter loop_filter_c_bits = 0;
parameter loop_filter_r_bits = 0;
parameter test_counter_c0_delay_chain_bits = 0;
parameter test_counter_c1_delay_chain_bits = 0;
parameter test_counter_c2_delay_chain_bits = 0;
parameter test_counter_c3_delay_chain_bits = 0;
parameter test_counter_c4_delay_chain_bits = 0;
parameter test_counter_m_delay_chain_bits = 0;
parameter test_counter_n_delay_chain_bits = 0;
parameter test_feedback_comp_delay_chain_bits = 0;
parameter test_input_comp_delay_chain_bits = 0;
parameter test_volt_reg_output_mode_bits = 0;
parameter test_volt_reg_output_voltage_bits = 0;
parameter test_volt_reg_test_mode = "false";
parameter vco_range_detector_high_bits = -1;
parameter vco_range_detector_low_bits = -1;
parameter scan_chain_mif_file = ""; 


parameter auto_settings = "true";

// LOCAL_PARAMETERS_END
 
    // INPUT PORTS
    input [1:0] inclk;
    input fbin;
    input clkswitch;
    input areset;
    input pfdena;
    input [phase_counter_select_width - 1:0] phasecounterselect;
    input phaseupdown;
    input phasestep;
    input scanclk;
    input scanclkena;
    input scandata;
    input configupdate;

    // OUTPUT PORTS
    output [4:0] clk;
    output [1:0] clkbad;
    output activeclock;
    output locked;
    output scandataout;
    output scandone;
    output fbout;
    output phasedone;
    output vcooverrange;
    output vcounderrange;
    output fref;
    output icdrclk;


    // BUFFER INPUTS
    wire inclk0_ipd;
    wire inclk1_ipd;
    wire fbin_ipd;
    wire clkswitch_ipd;
    wire areset_ipd;
    wire pfdena_ipd;
    wire [phase_counter_select_width - 1:0] phasecounterselect_ipd;
    wire phaseupdown_ipd;
    wire phasestep_ipd;
    wire scanclk_ipd;
    wire scanclkena_ipd;
    wire scandata_ipd;
    wire configupdate_ipd;

    buf (inclk0_ipd, inclk[0]);
    buf (inclk1_ipd, inclk[1]);
    buf (fbin_ipd, fbin);
    buf (clkswitch_ipd, clkswitch);
    buf (areset_ipd, areset);
    buf (pfdena_ipd, pfdena);
    buf buf_pcs [phase_counter_select_width - 1:0] (phasecounterselect_ipd, phasecounterselect);
    buf (phaseupdown_ipd, phaseupdown);
    buf (phasestep_ipd, phasestep);
    buf (scanclk_ipd, scanclk);
    buf (scandata_ipd, scandata);
    buf (scanclkena_ipd, scanclkena);
    buf (configupdate_ipd, configupdate);
    
        

    // INTERNAL VARIABLES AND NETS
    reg [8*6:1] clk_num[0:4];
    integer scan_chain_length;
    integer i;
    integer j;
    integer k;
    integer x;
    integer y;
    integer l_index;
    integer gate_count;
    integer egpp_offset;
    time sched_time;
    integer delay_chain;
    integer low;
    integer high;
    integer initial_delay;
    integer fbk_phase;
    integer fbk_delay;
    time phase_shift[0:7];
    time last_phase_shift[0:7];

    time m_times_vco_period;
    time new_m_times_vco_period;
    time refclk_period;
    time fbclk_period;
    time high_time;
    time low_time;
    integer my_rem;
    integer tmp_rem;
    integer rem;
    time tmp_vco_per;
    integer vco_per;
    integer offset;
    integer temp_offset;
    integer cycles_to_lock;
    integer cycles_to_unlock;
    integer loop_xplier;
    integer loop_initial;
    integer loop_ph;
    integer cycle_to_adjust;
    integer total_pull_back;
    integer pull_back_M;

    time    fbclk_time;
    time    first_fbclk_time;
    time    refclk_time;

    reg switch_clock;

    reg [31:0] real_lock_high;

    reg got_first_refclk;
    reg got_second_refclk;
    reg got_first_fbclk;
    reg refclk_last_value;
    reg fbclk_last_value;
    reg inclk_last_value;
    reg pll_is_locked;
    reg locked_tmp;
    reg areset_ipd_last_value;
    reg pfdena_ipd_last_value;
    reg inclk_out_of_range;
    reg schedule_vco_last_value;
    
    // Test bypass lock detect
    reg pfd_locked;
    integer cycles_pfd_low, cycles_pfd_high;

    reg gate_out;
    reg vco_val;

    reg [31:0] m_initial_val;
    reg [31:0] m_val[0:1];
    reg [31:0] n_val[0:1];
    reg [31:0] m_delay;
    reg [8*6:1] m_mode_val[0:1];
    reg [8*6:1] n_mode_val[0:1];

    reg [31:0] c_high_val[0:9];
    reg [31:0] c_low_val[0:9];
    reg [8*6:1] c_mode_val[0:9];
    reg [31:0] c_initial_val[0:9];
    integer c_ph_val[0:9];

    reg [31:0] c_val; // placeholder for c_high,c_low values

    // VCO Frequency Range control
    reg vco_over, vco_under;
   
    // temporary registers for reprogramming
    integer c_ph_val_tmp[0:9];
    reg [31:0] c_high_val_tmp[0:9];
    reg [31:0] c_hval[0:9];
    reg [31:0] c_low_val_tmp[0:9];
    reg [31:0] c_lval[0:9];
    reg [8*6:1] c_mode_val_tmp[0:9];

    // hold registers for reprogramming
    integer c_ph_val_hold[0:9];
    reg [31:0] c_high_val_hold[0:9];
    reg [31:0] c_low_val_hold[0:9];
    reg [8*6:1] c_mode_val_hold[0:9];

    // old values
    reg [31:0] m_val_old[0:1];
    reg [31:0] m_val_tmp[0:1];
    reg [31:0] n_val_old[0:1];
    reg [8*6:1] m_mode_val_old[0:1];
    reg [8*6:1] n_mode_val_old[0:1];
    reg [31:0] c_high_val_old[0:9];
    reg [31:0] c_low_val_old[0:9];
    reg [8*6:1] c_mode_val_old[0:9];
    integer c_ph_val_old[0:9];
    integer   m_ph_val_old;
    integer   m_ph_val_tmp;

    integer cp_curr_old;
    integer cp_curr_val;
    integer lfc_old;
    integer lfc_val;
    integer vco_cur;
    integer vco_old;
    reg [9*8:1] lfr_val;
    reg [9*8:1] lfr_old;
    reg [1:2] lfc_val_bit_setting, lfc_val_old_bit_setting;
    reg vco_val_bit_setting, vco_val_old_bit_setting;
    reg [3:7] lfr_val_bit_setting, lfr_val_old_bit_setting;
    reg [14:16] cp_curr_bit_setting, cp_curr_old_bit_setting;
    
    // Setting on  - display real values
    // Setting off - display only bits
    reg pll_reconfig_display_full_setting;

    reg [7:0] m_hi;
    reg [7:0] m_lo;
    reg [7:0] n_hi;
    reg [7:0] n_lo;

    // ph tap orig values (POF)
    integer c_ph_val_orig[0:9];
    integer m_ph_val_orig;

    reg schedule_vco;
    reg stop_vco;
    reg inclk_n;
    reg inclk_man;
    reg inclk_es;

    reg [7:0] vco_out;
    reg [7:0] vco_tap;
    reg [7:0] vco_out_last_value;
    reg [7:0] vco_tap_last_value;
    wire inclk_c0;
    wire inclk_c1;
    wire inclk_c2;
    wire inclk_c3;
    wire inclk_c4;
    
    wire  inclk_c0_from_vco;
    wire  inclk_c1_from_vco;
    wire  inclk_c2_from_vco;
    wire  inclk_c3_from_vco;
    wire  inclk_c4_from_vco;
    
    wire  inclk_m_from_vco;

    wire inclk_m;
    wire [4:0] clk_tmp, clk_out_pfd;


    wire [4:0] clk_out;

    wire c0_clk;
    wire c1_clk;
    wire c2_clk;
    wire c3_clk;
    wire c4_clk;

    reg first_schedule;

    reg vco_period_was_phase_adjusted;
    reg phase_adjust_was_scheduled;

    wire refclk;
    wire fbclk;

    wire icdr_clk;

    wire pllena_reg;
    wire test_mode_inclk;
 
    // Self Reset
    wire reset_self;

    // Clock Switchover
    reg clk0_is_bad;
    reg clk1_is_bad;
    reg inclk0_last_value;
    reg inclk1_last_value;
    reg other_clock_value;
    reg other_clock_last_value;
    reg primary_clk_is_bad;
    reg current_clk_is_bad;
    reg external_switch;
    reg active_clock;
    reg got_curr_clk_falling_edge_after_clkswitch;

    integer clk0_count;
    integer clk1_count;
    integer switch_over_count;

    wire scandataout_tmp;
    reg scandata_in, scandata_out; // hold scan data in negative-edge triggered ff (on either side on chain)
    reg scandone_tmp;
    reg initiate_reconfig;
    integer quiet_time;
    integer slowest_clk_old;
    integer slowest_clk_new;

    reg reconfig_err;
    reg error;
    time    scanclk_last_rising_edge;
    time    scanread_active_edge;
    reg got_first_scanclk;
    reg got_first_gated_scanclk;
    reg gated_scanclk;
    integer scanclk_period;
    reg scanclk_last_value;
    wire update_conf_latches;
    reg  update_conf_latches_reg;
    reg [-1:142]  scan_data;
    reg scanclkena_reg; // register scanclkena on negative edge of scanclk
    reg c0_rising_edge_transfer_done;
    reg c1_rising_edge_transfer_done;
    reg c2_rising_edge_transfer_done;
    reg c3_rising_edge_transfer_done;
    reg c4_rising_edge_transfer_done;
    reg scanread_setup_violation;
    integer index;
    integer scanclk_cycles;
    reg d_msg;

    integer num_output_cntrs;
    reg no_warn;
    
    // Phase reconfig
    
    reg [2:0] phasecounterselect_reg;
    reg phaseupdown_reg;
    reg phasestep_reg;
    integer select_counter;
    integer phasestep_high_count;
    reg update_phase;
    

// LOCAL_PARAMETERS_BEGIN

    parameter SCAN_CHAIN = 144;
    parameter GPP_SCAN_CHAIN  = 234;
    parameter FAST_SCAN_CHAIN = 180;
    // primary clk is always inclk0
    parameter num_phase_taps = 8;

// LOCAL_PARAMETERS_END


    // internal variables for scaling of multiply_by and divide_by values
    integer i_clk0_mult_by;
    integer i_clk0_div_by;
    integer i_clk1_mult_by;
    integer i_clk1_div_by;
    integer i_clk2_mult_by;
    integer i_clk2_div_by;
    integer i_clk3_mult_by;
    integer i_clk3_div_by;
    integer i_clk4_mult_by;
    integer i_clk4_div_by;
    integer i_clk5_mult_by;
    integer i_clk5_div_by;
    integer i_clk6_mult_by;
    integer i_clk6_div_by;
    integer i_clk7_mult_by;
    integer i_clk7_div_by;
    integer i_clk8_mult_by;
    integer i_clk8_div_by;
    integer i_clk9_mult_by;
    integer i_clk9_div_by;
    integer max_d_value;
    integer new_multiplier;

    // internal variables for storing the phase shift number.(used in lvds mode only)
    integer i_clk0_phase_shift;
    integer i_clk1_phase_shift;
    integer i_clk2_phase_shift;
    integer i_clk3_phase_shift;
    integer i_clk4_phase_shift;

    // user to advanced internal signals

    integer   i_m_initial;
    integer   i_m;
    integer   i_n;
    integer   i_c_high[0:9];
    integer   i_c_low[0:9];
    integer   i_c_initial[0:9];
    integer   i_c_ph[0:9];
    reg       [8*6:1] i_c_mode[0:9];

    integer   i_vco_min;
    integer   i_vco_max;
    integer   i_vco_center;
    integer   i_pfd_min;
    integer   i_pfd_max;
    integer   i_m_ph;
    integer   m_ph_val;
    reg [8*2:1] i_clk4_counter;
    reg [8*2:1] i_clk3_counter;
    reg [8*2:1] i_clk2_counter;
    reg [8*2:1] i_clk1_counter;
    reg [8*2:1] i_clk0_counter;
    integer   i_charge_pump_current;
    integer   i_loop_filter_r;
    integer   max_neg_abs;
    integer   output_count;
    integer   new_divisor;

    integer loop_filter_c_arr[0:3];
    integer fpll_loop_filter_c_arr[0:3];
    integer charge_pump_curr_arr[0:15];

    reg pll_in_test_mode;
    reg pll_is_in_reset;
    reg pll_has_just_been_reconfigured;

    // uppercase to lowercase parameter values
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_operation_mode;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_pll_type;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_compensate_clock;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_scan_chain;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_switch_over_type;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_bandwidth_type;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_simulation_type;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_sim_gate_lock_device_behavior;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_vco_frequency_control;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_enable_switch_over_counter;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] l_self_reset_on_loss_lock;
    


    integer current_clock;
    integer current_clock_man;
    reg is_fast_pll;
    reg ic1_use_casc_in;
    reg ic2_use_casc_in;
    reg ic3_use_casc_in;
    reg ic4_use_casc_in;

    reg init;
    reg tap0_is_active;

    real inclk0_period, last_inclk0_period,inclk1_period, last_inclk1_period;
    real last_inclk0_edge,last_inclk1_edge,diff_percent_period;
    reg first_inclk0_edge_detect,first_inclk1_edge_detect;



    // finds the closest integer fraction of a given pair of numerator and denominator. 
    task find_simple_integer_fraction;
        input numerator;
        input denominator;
        input max_denom;
        output fraction_num; 
        output fraction_div; 
        parameter max_iter = 20;
        
        integer numerator;
        integer denominator;
        integer max_denom;
        integer fraction_num; 
        integer fraction_div; 
        
        integer quotient_array[max_iter-1:0];
        integer int_loop_iter;
        integer int_quot;
        integer m_value;
        integer d_value;
        integer old_m_value;
        integer swap;

        integer loop_iter;
        integer num;
        integer den;
        integer i_max_iter;

    begin      
        loop_iter = 0;
        num = (numerator == 0) ? 1 : numerator;
        den = (denominator == 0) ? 1 : denominator;
        i_max_iter = max_iter;
       
        while (loop_iter < i_max_iter)
        begin
            int_quot = num / den;
            quotient_array[loop_iter] = int_quot;
            num = num - (den*int_quot);
            loop_iter=loop_iter+1;
            
            if ((num == 0) || (max_denom != -1) || (loop_iter == i_max_iter)) 
            begin
                // calculate the numerator and denominator if there is a restriction on the
                // max denom value or if the loop is ending
                m_value = 0;
                d_value = 1;
                // get the rounded value at this stage for the remaining fraction
                if (den != 0)
                begin
                    m_value = (2*num/den);
                end
                // calculate the fraction numerator and denominator at this stage
                for (int_loop_iter = loop_iter-1; int_loop_iter >= 0; int_loop_iter=int_loop_iter-1)
                begin
                    if (m_value == 0)
                    begin
                        m_value = quotient_array[int_loop_iter];
                        d_value = 1;
                    end
                    else
                    begin
                        old_m_value = m_value;
                        m_value = quotient_array[int_loop_iter]*m_value + d_value;
                        d_value = old_m_value;
                    end
                end
                // if the denominator is less than the maximum denom_value or if there is no restriction save it
                if ((d_value <= max_denom) || (max_denom == -1))
                begin
                    fraction_num = m_value;
                    fraction_div = d_value;
                end
                // end the loop if the denomitor has overflown or the numerator is zero (no remainder during this round)
                if (((d_value > max_denom) && (max_denom != -1)) || (num == 0))
                begin
                    i_max_iter = loop_iter;
                end
            end
            // swap the numerator and denominator for the next round
            swap = den;
            den = num;
            num = swap;
        end
    end
    endtask // find_simple_integer_fraction

    // get the absolute value
    function integer abs;
    input value;
    integer value;
    begin
        if (value < 0)
            abs = value * -1;
        else abs = value;
    end
    endfunction

    // find twice the period of the slowest clock
    function integer slowest_clk;
    input C0, C0_mode, C1, C1_mode, C2, C2_mode, C3, C3_mode, C4, C4_mode, C5, C5_mode, C6, C6_mode, C7, C7_mode, C8, C8_mode, C9, C9_mode, refclk, m_mod;
    integer C0, C1, C2, C3, C4, C5, C6, C7, C8, C9;
    reg [8*6:1] C0_mode, C1_mode, C2_mode, C3_mode, C4_mode, C5_mode, C6_mode, C7_mode, C8_mode, C9_mode;
    integer refclk;
    reg [31:0] m_mod;
    integer max_modulus;
    begin
        max_modulus = 1;
        if (C0_mode != "bypass" && C0_mode != "   off")
            max_modulus = C0;
        if (C1 > max_modulus && C1_mode != "bypass" && C1_mode != "   off")
            max_modulus = C1;
        if (C2 > max_modulus && C2_mode != "bypass" && C2_mode != "   off")
            max_modulus = C2;
        if (C3 > max_modulus && C3_mode != "bypass" && C3_mode != "   off")
            max_modulus = C3;
        if (C4 > max_modulus && C4_mode != "bypass" && C4_mode != "   off")
            max_modulus = C4;
        if (C5 > max_modulus && C5_mode != "bypass" && C5_mode != "   off")
            max_modulus = C5;
        if (C6 > max_modulus && C6_mode != "bypass" && C6_mode != "   off")
            max_modulus = C6;
        if (C7 > max_modulus && C7_mode != "bypass" && C7_mode != "   off")
            max_modulus = C7;
        if (C8 > max_modulus && C8_mode != "bypass" && C8_mode != "   off")
            max_modulus = C8;
        if (C9 > max_modulus && C9_mode != "bypass" && C9_mode != "   off")
            max_modulus = C9;

        slowest_clk = (refclk * max_modulus *2 / m_mod);
    end
    endfunction

    // count the number of digits in the given integer
    function integer count_digit;
    input X;
    integer X;
    integer count, result;
    begin
        count = 0;
        result = X;
        while (result != 0)
        begin
            result = (result / 10);
            count = count + 1;
        end
        
        count_digit = count;
    end
    endfunction

    // reduce the given huge number(X) to Y significant digits
    function integer scale_num;
    input X, Y;
    integer X, Y;
    integer count;
    integer fac_ten, lc;
    begin
        fac_ten = 1;
        count = count_digit(X);
        
        for (lc = 0; lc < (count-Y); lc = lc + 1)
            fac_ten = fac_ten * 10;

        scale_num = (X / fac_ten);
    end
    endfunction

    // find the greatest common denominator of X and Y
    function integer gcd;
    input X,Y;
    integer X,Y;
    integer L, S, R, G;
    begin
        if (X < Y) // find which is smaller.
        begin
            S = X;
            L = Y;
        end
        else
        begin
            S = Y;
            L = X;
        end

        R = S;
        while ( R > 1)
        begin
            S = L;
            L = R;
            R = S % L;  // divide bigger number by smaller.
                        // remainder becomes smaller number.
        end
        if (R == 0)     // if evenly divisible then L is gcd else it is 1.
            G = L;
        else
            G = R;
        gcd = G;
    end
    endfunction

    // find the least common multiple of A1 to A10
    function integer lcm;
    input A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, P;
    integer M1, M2, M3, M4, M5 , M6, M7, M8, M9, R;
    begin
        M1 = (A1 * A2)/gcd(A1, A2);
        M2 = (M1 * A3)/gcd(M1, A3);
        M3 = (M2 * A4)/gcd(M2, A4);
        M4 = (M3 * A5)/gcd(M3, A5);
        M5 = (M4 * A6)/gcd(M4, A6);
        M6 = (M5 * A7)/gcd(M5, A7);
        M7 = (M6 * A8)/gcd(M6, A8);
        M8 = (M7 * A9)/gcd(M7, A9);
        M9 = (M8 * A10)/gcd(M8, A10);
        if (M9 < 3)
            R = 10;
        else if ((M9 <= 10) && (M9 >= 3))
            R = 4 * M9;
        else if (M9 > 1000)
            R = scale_num(M9, 3);
        else
            R = M9;
        lcm = R; 
    end
    endfunction

    // find the M and N values for Manual phase based on the following 5 criterias:
    // 1. The PFD frequency (i.e. Fin / N) must be in the range 5 MHz to 720 MHz
    // 2. The VCO frequency (i.e. Fin * M / N) must be in the range 300 MHz to 1300 MHz
    // 3. M is less than 512
    // 4. N is less than 512
    // 5. It's the smallest M/N which satisfies all the above constraints, and is within 2ps
    //    of the desired vco-phase-shift-step
    task find_m_and_n_4_manual_phase;
        input inclock_period;
        input vco_phase_shift_step;
        input clk0_mult, clk1_mult, clk2_mult, clk3_mult, clk4_mult;
        input clk5_mult, clk6_mult, clk7_mult, clk8_mult, clk9_mult;
        input clk0_div,  clk1_div,  clk2_div,  clk3_div,  clk4_div;
        input clk5_div,  clk6_div,  clk7_div,  clk8_div,  clk9_div;
        input clk0_used,  clk1_used,  clk2_used,  clk3_used,  clk4_used;
        input clk5_used,  clk6_used,  clk7_used,  clk8_used,  clk9_used;
        output m; 
        output n; 

        parameter max_m = 511;
        parameter max_n = 511;
        parameter max_pfd = 720;
        parameter min_pfd = 5;
        parameter max_vco = 1300;
        parameter min_vco = 300;
        parameter max_offset = 0.004;
        
        reg[160:1] clk0_used,  clk1_used,  clk2_used,  clk3_used,  clk4_used;
        reg[160:1] clk5_used,  clk6_used,  clk7_used,  clk8_used,  clk9_used;
        
        integer inclock_period;
        integer vco_phase_shift_step;
        integer clk0_mult, clk1_mult, clk2_mult, clk3_mult, clk4_mult;
        integer clk5_mult, clk6_mult, clk7_mult, clk8_mult, clk9_mult;
        integer clk0_div,  clk1_div,  clk2_div,  clk3_div,  clk4_div;
        integer clk5_div,  clk6_div,  clk7_div,  clk8_div,  clk9_div;
        integer m; 
        integer n;
        integer pre_m;
        integer pre_n;
        integer m_out;
        integer n_out;
        integer closest_vco_step_value;
        
        integer vco_period;
        integer pfd_freq;
        integer vco_freq;
        integer vco_ps_step_value;
        real    clk0_div_factor_real;
        real    clk1_div_factor_real;
        real    clk2_div_factor_real;
        real    clk3_div_factor_real;
        real    clk4_div_factor_real;
        real    clk5_div_factor_real;
        real    clk6_div_factor_real;
        real    clk7_div_factor_real;
        real    clk8_div_factor_real;
        real    clk9_div_factor_real;
        real    clk0_div_factor_diff;
        real    clk1_div_factor_diff;
        real    clk2_div_factor_diff;
        real    clk3_div_factor_diff;
        real    clk4_div_factor_diff;
        real    clk5_div_factor_diff;
        real    clk6_div_factor_diff;
        real    clk7_div_factor_diff;
        real    clk8_div_factor_diff;
        real    clk9_div_factor_diff;
        integer clk0_div_factor_int;
        integer clk1_div_factor_int;
        integer clk2_div_factor_int;
        integer clk3_div_factor_int;
        integer clk4_div_factor_int;
        integer clk5_div_factor_int;
        integer clk6_div_factor_int;
        integer clk7_div_factor_int;
        integer clk8_div_factor_int;
        integer clk9_div_factor_int;
    begin

        vco_period = vco_phase_shift_step * 8;

        pre_m = 0;
        pre_n = 0;
        closest_vco_step_value = 0;

        begin : LOOP_1
                for (n_out = 1; n_out < max_n; n_out = n_out +1)
                begin
                    for (m_out = 1; m_out < max_m; m_out = m_out +1)
                    begin
                        clk0_div_factor_real = (clk0_div * m_out * 1.0 ) / (clk0_mult * n_out);
                        clk1_div_factor_real = (clk1_div * m_out * 1.0) / (clk1_mult * n_out);
                        clk2_div_factor_real = (clk2_div * m_out * 1.0) / (clk2_mult * n_out);
                        clk3_div_factor_real = (clk3_div * m_out * 1.0) / (clk3_mult * n_out);
                        clk4_div_factor_real = (clk4_div * m_out * 1.0) / (clk4_mult * n_out);
                        clk5_div_factor_real = (clk5_div * m_out * 1.0) / (clk5_mult * n_out);
                        clk6_div_factor_real = (clk6_div * m_out * 1.0) / (clk6_mult * n_out);
                        clk7_div_factor_real = (clk7_div * m_out * 1.0) / (clk7_mult * n_out);
                        clk8_div_factor_real = (clk8_div * m_out * 1.0) / (clk8_mult * n_out);
                        clk9_div_factor_real = (clk9_div * m_out * 1.0) / (clk9_mult * n_out);
        
                        clk0_div_factor_int = clk0_div_factor_real;
                        clk1_div_factor_int = clk1_div_factor_real;
                        clk2_div_factor_int = clk2_div_factor_real;
                        clk3_div_factor_int = clk3_div_factor_real;
                        clk4_div_factor_int = clk4_div_factor_real;
                        clk5_div_factor_int = clk5_div_factor_real;
                        clk6_div_factor_int = clk6_div_factor_real;
                        clk7_div_factor_int = clk7_div_factor_real;
                        clk8_div_factor_int = clk8_div_factor_real;
                        clk9_div_factor_int = clk9_div_factor_real;
                        
                        clk0_div_factor_diff = (clk0_div_factor_real - clk0_div_factor_int < 0) ? (clk0_div_factor_real - clk0_div_factor_int) * -1.0 : clk0_div_factor_real - clk0_div_factor_int;
                        clk1_div_factor_diff = (clk1_div_factor_real - clk1_div_factor_int < 0) ? (clk1_div_factor_real - clk1_div_factor_int) * -1.0 : clk1_div_factor_real - clk1_div_factor_int;
                        clk2_div_factor_diff = (clk2_div_factor_real - clk2_div_factor_int < 0) ? (clk2_div_factor_real - clk2_div_factor_int) * -1.0 : clk2_div_factor_real - clk2_div_factor_int;
                        clk3_div_factor_diff = (clk3_div_factor_real - clk3_div_factor_int < 0) ? (clk3_div_factor_real - clk3_div_factor_int) * -1.0 : clk3_div_factor_real - clk3_div_factor_int;
                        clk4_div_factor_diff = (clk4_div_factor_real - clk4_div_factor_int < 0) ? (clk4_div_factor_real - clk4_div_factor_int) * -1.0 : clk4_div_factor_real - clk4_div_factor_int;
                        clk5_div_factor_diff = (clk5_div_factor_real - clk5_div_factor_int < 0) ? (clk5_div_factor_real - clk5_div_factor_int) * -1.0 : clk5_div_factor_real - clk5_div_factor_int;
                        clk6_div_factor_diff = (clk6_div_factor_real - clk6_div_factor_int < 0) ? (clk6_div_factor_real - clk6_div_factor_int) * -1.0 : clk6_div_factor_real - clk6_div_factor_int;
                        clk7_div_factor_diff = (clk7_div_factor_real - clk7_div_factor_int < 0) ? (clk7_div_factor_real - clk7_div_factor_int) * -1.0 : clk7_div_factor_real - clk7_div_factor_int;
                        clk8_div_factor_diff = (clk8_div_factor_real - clk8_div_factor_int < 0) ? (clk8_div_factor_real - clk8_div_factor_int) * -1.0 : clk8_div_factor_real - clk8_div_factor_int;
                        clk9_div_factor_diff = (clk9_div_factor_real - clk9_div_factor_int < 0) ? (clk9_div_factor_real - clk9_div_factor_int) * -1.0 : clk9_div_factor_real - clk9_div_factor_int;
                        
        
                        if (((clk0_div_factor_diff < max_offset) || (clk0_used == "unused")) &&
                            ((clk1_div_factor_diff < max_offset) || (clk1_used == "unused")) &&
                            ((clk2_div_factor_diff < max_offset) || (clk2_used == "unused")) &&
                            ((clk3_div_factor_diff < max_offset) || (clk3_used == "unused")) &&
                            ((clk4_div_factor_diff < max_offset) || (clk4_used == "unused")) &&
                            ((clk5_div_factor_diff < max_offset) || (clk5_used == "unused")) &&
                            ((clk6_div_factor_diff < max_offset) || (clk6_used == "unused")) &&
                            ((clk7_div_factor_diff < max_offset) || (clk7_used == "unused")) &&
                            ((clk8_div_factor_diff < max_offset) || (clk8_used == "unused")) &&
                            ((clk9_div_factor_diff < max_offset) || (clk9_used == "unused")) )
                        begin                
                            if ((m_out != 0) && (n_out != 0))
                            begin
                                pfd_freq = 1000000 / (inclock_period * n_out);
                                vco_freq = (1000000 * m_out) / (inclock_period * n_out);
                                vco_ps_step_value = (inclock_period * n_out) / (8 * m_out);
                
                                if ( (m_out < max_m) && (n_out < max_n) && (pfd_freq >= min_pfd) && (pfd_freq <= max_pfd) &&
                                    (vco_freq >= min_vco) && (vco_freq <= max_vco) )
                                begin
                                    if (abs(vco_ps_step_value - vco_phase_shift_step) <= 2)
                                    begin
                                        pre_m = m_out;
                                        pre_n = n_out;
                                        disable LOOP_1;
                                    end
                                    else
                                    begin
                                        if ((closest_vco_step_value == 0) || (abs(vco_ps_step_value - vco_phase_shift_step) < abs(closest_vco_step_value - vco_phase_shift_step)))
                                        begin
                                            pre_m = m_out;
                                            pre_n = n_out;
                                            closest_vco_step_value = vco_ps_step_value;
                                        end
                                    end
                                end
                            end
                        end
                    end
                end
        end
        
        if ((pre_m != 0) && (pre_n != 0))
        begin
            find_simple_integer_fraction(pre_m, pre_n,
                        max_n, m, n);
        end
        else
        begin
            n = 1;
            m = lcm  (clk0_mult, clk1_mult, clk2_mult, clk3_mult,
                    clk4_mult, clk5_mult, clk6_mult,
                    clk7_mult, clk8_mult, clk9_mult, inclock_period);           
        end
    end
    endtask // find_m_and_n_4_manual_phase

    // find the factor of division of the output clock frequency
    // compared to the VCO
    function integer output_counter_value;
    input clk_divide, clk_mult, M, N;
    integer clk_divide, clk_mult, M, N;
    real r;
    integer r_int;
    begin
        r = (clk_divide * M * 1.0)/(clk_mult * N);
        r_int = r;
        output_counter_value = r_int;
    end
    endfunction

    // find the mode of each of the PLL counters - bypass, even or odd
    function [8*6:1] counter_mode;
    input duty_cycle;
    input output_counter_value;
    integer duty_cycle;
    integer output_counter_value;
    integer half_cycle_high;
    reg [8*6:1] R;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        if (output_counter_value == 1)
            R = "bypass";
        else if ((half_cycle_high % 2) == 0)
            R = "  even";
        else
            R = "   odd";
        counter_mode = R;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock high
    function integer counter_high;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle;
    integer half_cycle_high;
    integer tmp_counter_high;
    integer mode;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_high = tmp_counter_high + !mode;
    end
    endfunction

    // find the number of VCO clock cycles to hold the output clock low
    function integer counter_low;
    input output_counter_value, duty_cycle;
    integer output_counter_value, duty_cycle, counter_h;
    integer half_cycle_high;
    integer mode;
    integer tmp_counter_high;
    begin
        half_cycle_high = (2*duty_cycle*output_counter_value)/100.0;
        mode = ((half_cycle_high % 2) == 0);
        tmp_counter_high = half_cycle_high/2;
        counter_h = tmp_counter_high + !mode;
        counter_low =  output_counter_value - counter_h;
    end
    endfunction

    // find the smallest time delay amongst t1 to t10
    function integer mintimedelay;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2)
            m1 = t1;
        else
            m1 = t2;
        if (m1 < t3)
            m2 = m1;
        else
            m2 = t3;
        if (m2 < t4)
            m3 = m2;
        else
            m3 = t4;
        if (m3 < t5)
            m4 = m3;
        else
            m4 = t5;
        if (m4 < t6)
            m5 = m4;
        else
            m5 = t6;
        if (m5 < t7)
            m6 = m5;
        else
            m6 = t7;
        if (m6 < t8)
            m7 = m6;
        else
            m7 = t8;
        if (m7 < t9)
            m8 = m7;
        else
            m8 = t9;
        if (m8 < t10)
            m9 = m8;
        else
            m9 = t10;
        if (m9 > 0)
            mintimedelay = m9;
        else
            mintimedelay = 0;
    end
    endfunction

    // find the numerically largest negative number, and return its absolute value
    function integer maxnegabs;
    input t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer t1, t2, t3, t4, t5, t6, t7, t8, t9, t10;
    integer m1,m2,m3,m4,m5,m6,m7,m8,m9;
    begin
        if (t1 < t2) m1 = t1; else m1 = t2;
        if (m1 < t3) m2 = m1; else m2 = t3;
        if (m2 < t4) m3 = m2; else m3 = t4;
        if (m3 < t5) m4 = m3; else m4 = t5;
        if (m4 < t6) m5 = m4; else m5 = t6;
        if (m5 < t7) m6 = m5; else m6 = t7;
        if (m6 < t8) m7 = m6; else m7 = t8;
        if (m7 < t9) m8 = m7; else m8 = t9;
        if (m8 < t10) m9 = m8; else m9 = t10;
        maxnegabs = (m9 < 0) ? 0 - m9 : 0;
    end
    endfunction

    // adjust the given tap_phase by adding the largest negative number (ph_base) 
    function integer ph_adjust;
    input tap_phase, ph_base;
    integer tap_phase, ph_base;
    begin
        ph_adjust = tap_phase + ph_base;
    end
    endfunction

    // find the number of VCO clock cycles to wait initially before the first 
    // rising edge of the output clock
    function integer counter_initial;
    input tap_phase, m, n;
    integer tap_phase, m, n, phase;
    begin
        if (tap_phase < 0) tap_phase = 0 - tap_phase;
        // adding 0.5 for rounding correction (required in order to round
        // to the nearest integer instead of truncating)
        phase = ((tap_phase * m) / (360.0 * n)) + 0.6;
        counter_initial = phase;
    end
    endfunction

    // find which VCO phase tap to align the rising edge of the output clock to
    function integer counter_ph;
    input tap_phase;
    input m,n;
    integer m,n, phase;
    integer tap_phase;
    begin
    // adding 0.5 for rounding correction
        phase = (tap_phase * m / n) + 0.5;
        counter_ph = (phase % 360) / 45.0;

        if (counter_ph == 8)
            counter_ph = 0;
    end
    endfunction

    // convert the given string to length 6 by padding with spaces
    function [8*6:1] translate_string;
    input [8*6:1] mode;
    reg [8*6:1] new_mode;
    begin
        if (mode == "bypass")
            new_mode = "bypass";
        else if (mode == "even")
            new_mode = "  even";
        else if (mode == "odd")
            new_mode = "   odd";

        translate_string = new_mode;
    end
    endfunction

    // convert string to integer with sign
    function integer str2int; 
    input [8*16:1] s;

    reg [8*16:1] reg_s;
    reg [8:1] digit;
    reg [8:1] tmp;
    integer m, magnitude;
    integer sign;

    begin
        sign = 1;
        magnitude = 0;
        reg_s = s;
        for (m=1; m<=16; m=m+1)
        begin
            tmp = reg_s[128:121];
            digit = tmp & 8'b00001111;
            reg_s = reg_s << 8;
            // Accumulate ascii digits 0-9 only.
            if ((tmp>=48) && (tmp<=57)) 
                magnitude = (magnitude * 10) + digit;
            if (tmp == 45)
                sign = -1;  // Found a '-' character, i.e. number is negative.
        end
        str2int = sign*magnitude;
    end
    endfunction

    // this is for cycloneiiigl lvds only
    // convert phase delay to integer
    function integer get_int_phase_shift; 
    input [8*16:1] s;
    input i_phase_shift;
    integer i_phase_shift;

    begin
        if (i_phase_shift != 0)
        begin                   
            get_int_phase_shift = i_phase_shift;
        end       
        else
        begin
            get_int_phase_shift = str2int(s);
        end        
    end
    endfunction

    // calculate the given phase shift (in ps) in terms of degrees
    function integer get_phase_degree; 
    input phase_shift;
    integer phase_shift, result;
    begin
        result = (phase_shift * 360) / inclk0_input_frequency;
        // this is to round up the calculation result
        if ( result > 0 )
            result = result + 1;
        else if ( result < 0 )
            result = result - 1;
        else
            result = 0;

        // assign the rounded up result
        get_phase_degree = result;
    end
    endfunction

    // convert uppercase parameter values to lowercase
    // assumes that the maximum character length of a parameter is 18
    function [8*`CYCIIIGL_PLL_WORD_LENGTH:1] alpha_tolower;
    input [8*`CYCIIIGL_PLL_WORD_LENGTH:1] given_string;

    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] return_string;
    reg [8*`CYCIIIGL_PLL_WORD_LENGTH:1] reg_string;
    reg [8:1] tmp;
    reg [8:1] conv_char;
    integer byte_count;
    begin
        return_string = "                    "; // initialise strings to spaces
        conv_char = "        ";
        reg_string = given_string;
        for (byte_count = `CYCIIIGL_PLL_WORD_LENGTH; byte_count >= 1; byte_count = byte_count - 1)
        begin
            tmp = reg_string[8*`CYCIIIGL_PLL_WORD_LENGTH:(8*(`CYCIIIGL_PLL_WORD_LENGTH-1)+1)];
            reg_string = reg_string << 8;
            if ((tmp >= 65) && (tmp <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
            begin
                conv_char = tmp + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
                return_string = {return_string, conv_char};
            end
            else
                return_string = {return_string, tmp};
        end
    
        alpha_tolower = return_string;
    end
    endfunction

    function integer display_msg;
    input [8*2:1] cntr_name;
    input msg_code;
    integer msg_code;
    begin
        if (msg_code == 1)
            $display ("Warning : %s counter switched from BYPASS mode to enabled. PLL may lose lock.", cntr_name);
        else if (msg_code == 2)
            $display ("Warning : Illegal 1 value for %s counter. Instead, the %s counter should be BYPASSED. Reconfiguration may not work.", cntr_name, cntr_name);
        else if (msg_code == 3)
            $display ("Warning : Illegal value for counter %s in BYPASS mode. The LSB of the counter should be set to 0 in order to operate the counter in BYPASS mode. Reconfiguration may not work.", cntr_name);
        else if (msg_code == 4)
            $display ("Warning : %s counter switched from enabled to BYPASS mode. PLL may lose lock.", cntr_name);
        $display ("Time: %0t  Instance: %m", $time);
        display_msg = 1;
    end
    endfunction

    initial
    begin
        scandata_out = 1'b0;
        first_inclk0_edge_detect = 1'b0;
        first_inclk1_edge_detect = 1'b0;
        pll_reconfig_display_full_setting = 1'b0;
        initiate_reconfig = 1'b0;
    switch_over_count = 0;
        // convert string parameter values from uppercase to lowercase,
        // as expected in this model
        l_operation_mode             = alpha_tolower(operation_mode);
        l_pll_type                   = alpha_tolower(pll_type);
        l_compensate_clock           = alpha_tolower(compensate_clock);
        l_switch_over_type           = alpha_tolower(switch_over_type);
        l_bandwidth_type             = alpha_tolower(bandwidth_type);
        l_simulation_type            = alpha_tolower(simulation_type);
        l_sim_gate_lock_device_behavior = alpha_tolower(sim_gate_lock_device_behavior);
        l_vco_frequency_control      = alpha_tolower(vco_frequency_control);
        l_enable_switch_over_counter = alpha_tolower(enable_switch_over_counter);
        l_self_reset_on_loss_lock    = alpha_tolower(self_reset_on_loss_lock);
    
        real_lock_high = (l_sim_gate_lock_device_behavior == "on") ? lock_high : 0;    
        // initialize charge_pump_current, and loop_filter tables
        loop_filter_c_arr[0] = 0;
        loop_filter_c_arr[1] = 0;
        loop_filter_c_arr[2] = 0;
        loop_filter_c_arr[3] = 0;
        
        fpll_loop_filter_c_arr[0] = 0;
        fpll_loop_filter_c_arr[1] = 0;
        fpll_loop_filter_c_arr[2] = 0;
        fpll_loop_filter_c_arr[3] = 0;
        
        charge_pump_curr_arr[0] = 0;
        charge_pump_curr_arr[1] = 0;
        charge_pump_curr_arr[2] = 0;
        charge_pump_curr_arr[3] = 0;
        charge_pump_curr_arr[4] = 0;
        charge_pump_curr_arr[5] = 0;
        charge_pump_curr_arr[6] = 0;
        charge_pump_curr_arr[7] = 0;
        charge_pump_curr_arr[8] = 0;
        charge_pump_curr_arr[9] = 0;
        charge_pump_curr_arr[10] = 0;
        charge_pump_curr_arr[11] = 0;
        charge_pump_curr_arr[12] = 0;
        charge_pump_curr_arr[13] = 0;
        charge_pump_curr_arr[14] = 0;
        charge_pump_curr_arr[15] = 0;

        i_vco_max = vco_max * (vco_post_scale/2) * 1000;
        i_vco_min = vco_min * (vco_post_scale/2) * 1000;  


        if (m == 0)
        begin
            i_clk4_counter    = "c4" ;
            i_clk3_counter    = "c3" ;
            i_clk2_counter    = "c2" ;
            i_clk1_counter    = "c1" ;
            i_clk0_counter    = "c0" ;
        end
        else begin
            i_clk4_counter    = alpha_tolower(clk4_counter);
            i_clk3_counter    = alpha_tolower(clk3_counter);
            i_clk2_counter    = alpha_tolower(clk2_counter);
            i_clk1_counter    = alpha_tolower(clk1_counter);
            i_clk0_counter    = alpha_tolower(clk0_counter);
        end

        if (m == 0)
        begin 

            // set the limit of the divide_by value that can be returned by
            // the following function.
            max_d_value = 500;
            
            // scale down the multiply_by and divide_by values provided by the design
            // before attempting to use them in the calculations below
            find_simple_integer_fraction(clk0_multiply_by, clk0_divide_by,
                            max_d_value, i_clk0_mult_by, i_clk0_div_by);
            find_simple_integer_fraction(clk1_multiply_by, clk1_divide_by,
                            max_d_value, i_clk1_mult_by, i_clk1_div_by);
            find_simple_integer_fraction(clk2_multiply_by, clk2_divide_by,
                            max_d_value, i_clk2_mult_by, i_clk2_div_by);
            find_simple_integer_fraction(clk3_multiply_by, clk3_divide_by,
                            max_d_value, i_clk3_mult_by, i_clk3_div_by);
            find_simple_integer_fraction(clk4_multiply_by, clk4_divide_by,
                            max_d_value, i_clk4_mult_by, i_clk4_div_by);

            // convert user parameters to advanced
            if (l_vco_frequency_control == "manual_phase")
            begin
                find_m_and_n_4_manual_phase(inclk0_input_frequency, vco_phase_shift_step,
                            i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,i_clk4_mult_by,
                1, 1, 1, 1, 1, 
                            i_clk0_div_by, i_clk1_div_by,
                            i_clk2_div_by, i_clk3_div_by,i_clk4_div_by,
                1, 1, 1, 1, 1, 
                            clk0_counter, clk1_counter,
                            clk2_counter, clk3_counter,clk4_counter,
                "unused", "unused", "unused", "unused", "unused", 
                            i_m, i_n);
            end
            else if (((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right")) && (vco_multiply_by != 0) && (vco_divide_by != 0))
            begin
                i_n = vco_divide_by;
                i_m = vco_multiply_by;
            end
            else if ((dpa_multiply_by != 0) && (dpa_divide_by != 0))
            begin
                i_n = dpa_divide_by;
                i_m = dpa_multiply_by;
            end
            else begin
                i_n = 1;
                if (((l_pll_type == "fast") || (l_pll_type == "left_right")) && (l_compensate_clock == "lvdsclk"))
                    i_m = i_clk0_mult_by;
                else
                    i_m = lcm  (i_clk0_mult_by, i_clk1_mult_by,
                            i_clk2_mult_by, i_clk3_mult_by,i_clk4_mult_by,
                1, 1, 1, 1, 1, 
                            inclk0_input_frequency);
            end

            i_c_high[0] = counter_high (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by, i_m, i_n), clk0_duty_cycle);
            i_c_high[1] = counter_high (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by, i_m, i_n), clk1_duty_cycle);
            i_c_high[2] = counter_high (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by, i_m, i_n), clk2_duty_cycle);
            i_c_high[3] = counter_high (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by, i_m, i_n), clk3_duty_cycle);
            i_c_high[4] = counter_high (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);

            i_c_low[0]  = counter_low  (output_counter_value(i_clk0_div_by,
                                        i_clk0_mult_by,  i_m, i_n), clk0_duty_cycle);
            i_c_low[1]  = counter_low  (output_counter_value(i_clk1_div_by,
                                        i_clk1_mult_by,  i_m, i_n), clk1_duty_cycle);
            i_c_low[2]  = counter_low  (output_counter_value(i_clk2_div_by,
                                        i_clk2_mult_by,  i_m, i_n), clk2_duty_cycle);
            i_c_low[3]  = counter_low  (output_counter_value(i_clk3_div_by,
                                        i_clk3_mult_by,  i_m, i_n), clk3_duty_cycle);
            i_c_low[4]  = counter_low  (output_counter_value(i_clk4_div_by,
                                        i_clk4_mult_by,  i_m, i_n), clk4_duty_cycle);

            if (l_pll_type == "flvds")
            begin
                // Need to readjust phase shift values when the clock multiply value has been readjusted.
                new_multiplier = clk0_multiply_by / i_clk0_mult_by;
                i_clk0_phase_shift = (clk0_phase_shift_num * new_multiplier);
                i_clk1_phase_shift = (clk1_phase_shift_num * new_multiplier);
                i_clk2_phase_shift = (clk2_phase_shift_num * new_multiplier);
                i_clk3_phase_shift = 0;
                i_clk4_phase_shift = 0;
            end
            else
            begin
                i_clk0_phase_shift = get_int_phase_shift(clk0_phase_shift, clk0_phase_shift_num);
                i_clk1_phase_shift = get_int_phase_shift(clk1_phase_shift, clk1_phase_shift_num);
                i_clk2_phase_shift = get_int_phase_shift(clk2_phase_shift, clk2_phase_shift_num);
                i_clk3_phase_shift = get_int_phase_shift(clk3_phase_shift, clk3_phase_shift_num);
                i_clk4_phase_shift = get_int_phase_shift(clk4_phase_shift, clk4_phase_shift_num);
            end

            max_neg_abs = maxnegabs   ( i_clk0_phase_shift,
                                        i_clk1_phase_shift,
                                        i_clk2_phase_shift,
                                        i_clk3_phase_shift,
                                        i_clk4_phase_shift,
                                            0,
                                            0,
                                            0,
                                            0,
                                            0
                                        );

            i_c_initial[0] = counter_initial(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[1] = counter_initial(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[2] = counter_initial(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[3] = counter_initial(get_phase_degree(ph_adjust(i_clk3_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_initial[4] = counter_initial(get_phase_degree(ph_adjust(i_clk4_phase_shift, max_neg_abs)), i_m, i_n);

            i_c_mode[0] = counter_mode(clk0_duty_cycle,output_counter_value(i_clk0_div_by, i_clk0_mult_by,  i_m, i_n));
            i_c_mode[1] = counter_mode(clk1_duty_cycle,output_counter_value(i_clk1_div_by, i_clk1_mult_by,  i_m, i_n));
            i_c_mode[2] = counter_mode(clk2_duty_cycle,output_counter_value(i_clk2_div_by, i_clk2_mult_by,  i_m, i_n));
            i_c_mode[3] = counter_mode(clk3_duty_cycle,output_counter_value(i_clk3_div_by, i_clk3_mult_by,  i_m, i_n));
            i_c_mode[4] = counter_mode(clk4_duty_cycle,output_counter_value(i_clk4_div_by, i_clk4_mult_by,  i_m, i_n));

            i_m_ph    = counter_ph(get_phase_degree(max_neg_abs), i_m, i_n);
            i_m_initial = counter_initial(get_phase_degree(max_neg_abs), i_m, i_n);
            
            i_c_ph[0] = counter_ph(get_phase_degree(ph_adjust(i_clk0_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[1] = counter_ph(get_phase_degree(ph_adjust(i_clk1_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[2] = counter_ph(get_phase_degree(ph_adjust(i_clk2_phase_shift, max_neg_abs)), i_m, i_n);
            i_c_ph[3] = counter_ph(get_phase_degree(ph_adjust(i_clk3_phase_shift,max_neg_abs)), i_m, i_n);
            i_c_ph[4] = counter_ph(get_phase_degree(ph_adjust(i_clk4_phase_shift,max_neg_abs)), i_m, i_n);


        end
        else 
        begin //  m != 0

            i_n = n;
            i_m = m;
            i_c_high[0] = c0_high;
            i_c_high[1] = c1_high;
            i_c_high[2] = c2_high;
            i_c_high[3] = c3_high;
            i_c_high[4] = c4_high;
            i_c_low[0]  = c0_low;
            i_c_low[1]  = c1_low;
            i_c_low[2]  = c2_low;
            i_c_low[3]  = c3_low;
            i_c_low[4]  = c4_low;
            i_c_initial[0] = c0_initial;
            i_c_initial[1] = c1_initial;
            i_c_initial[2] = c2_initial;
            i_c_initial[3] = c3_initial;
            i_c_initial[4] = c4_initial;
            i_c_mode[0] = translate_string(alpha_tolower(c0_mode));
            i_c_mode[1] = translate_string(alpha_tolower(c1_mode));
            i_c_mode[2] = translate_string(alpha_tolower(c2_mode));
            i_c_mode[3] = translate_string(alpha_tolower(c3_mode));
            i_c_mode[4] = translate_string(alpha_tolower(c4_mode));
            i_c_ph[0]  = c0_ph;
            i_c_ph[1]  = c1_ph;
            i_c_ph[2]  = c2_ph;
            i_c_ph[3]  = c3_ph;
            i_c_ph[4]  = c4_ph;
            i_m_ph   = m_ph;        // default
            i_m_initial = m_initial;

        end // user to advanced conversion
        
        switch_clock = 1'b0;

        refclk_period = inclk0_freq * i_n;

        m_times_vco_period = refclk_period;
        new_m_times_vco_period = refclk_period;

        fbclk_period = 0;
        high_time = 0;
        low_time = 0;
        schedule_vco = 0;
        vco_out[7:0] = 8'b0;
        vco_tap[7:0] = 8'b0;
        fbclk_last_value = 0;
        offset = 0;
        temp_offset = 0;
        got_first_refclk = 0;
        got_first_fbclk = 0;
        fbclk_time = 0;
        first_fbclk_time = 0;
        refclk_time = 0;
        first_schedule = 1;
        sched_time = 0;
        vco_val = 0;
        gate_count = 0;
        gate_out = 0;
        initial_delay = 0;
        fbk_phase = 0;
        for (i = 0; i <= 7; i = i + 1)
        begin
            phase_shift[i] = 0;
            last_phase_shift[i] = 0;
        end
        fbk_delay = 0;
        inclk_n = 0;
        inclk_es = 0;
        inclk_man = 0;
        cycle_to_adjust = 0;
        m_delay = 0;
        total_pull_back = 0;
        pull_back_M = 0;
        vco_period_was_phase_adjusted = 0;
        phase_adjust_was_scheduled = 0;
        inclk_out_of_range = 0;
        scandone_tmp = 1'b0;
        schedule_vco_last_value = 0;

        scan_chain_length = SCAN_CHAIN;
        num_output_cntrs  = 5;

        
        phasestep_high_count = 0;
        update_phase = 0;
        // set initial values for counter parameters
        m_initial_val = i_m_initial;
        m_val[0] = i_m;
        n_val[0] = i_n;
        m_ph_val = i_m_ph;
        m_ph_val_orig = i_m_ph;
        m_ph_val_tmp = i_m_ph;
        m_val_tmp[0] = i_m;


        if (m_val[0] == 1)
            m_mode_val[0] = "bypass";
        else m_mode_val[0] = "";
        if (m_val[1] == 1)
            m_mode_val[1] = "bypass";
        if (n_val[0] == 1)
            n_mode_val[0] = "bypass";
        if (n_val[1] == 1)
            n_mode_val[1] = "bypass";

        for (i = 0; i < 10; i=i+1)
        begin
            c_high_val[i] = i_c_high[i];
            c_low_val[i] = i_c_low[i];
            c_initial_val[i] = i_c_initial[i];
            c_mode_val[i] = i_c_mode[i];
            c_ph_val[i] = i_c_ph[i];
            c_high_val_tmp[i] = i_c_high[i];
            c_hval[i] = i_c_high[i];
            c_low_val_tmp[i] = i_c_low[i];
            c_lval[i] = i_c_low[i];
            if (c_mode_val[i] == "bypass")
            begin
                if (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right")
                begin
                    c_high_val[i] = 5'b10000;
                    c_low_val[i] = 5'b10000;
                    c_high_val_tmp[i] = 5'b10000;
                    c_low_val_tmp[i] = 5'b10000;
                end
                else begin
                    c_high_val[i] = 9'b100000000;
                    c_low_val[i] = 9'b100000000;
                    c_high_val_tmp[i] = 9'b100000000;
                    c_low_val_tmp[i] = 9'b100000000;
                end
            end

            c_mode_val_tmp[i] = i_c_mode[i];
            c_ph_val_tmp[i] = i_c_ph[i];

            c_ph_val_orig[i] = i_c_ph[i];
            c_high_val_hold[i] = i_c_high[i];
            c_low_val_hold[i] = i_c_low[i];
            c_mode_val_hold[i] = i_c_mode[i];
        end

        lfc_val = loop_filter_c;
        lfr_val = loop_filter_r;
        cp_curr_val = charge_pump_current;
        vco_cur = vco_post_scale;

        i = 0;
        j = 0;
        inclk_last_value = 0;

    
        // initialize clkswitch variables

        clk0_is_bad = 0;
        clk1_is_bad = 0;
        inclk0_last_value = 0;
        inclk1_last_value = 0;
        other_clock_value = 0;
        other_clock_last_value = 0;
        primary_clk_is_bad = 0;
        current_clk_is_bad = 0;
        external_switch = 0;
        current_clock = 0;
        current_clock_man = 0;

        active_clock = 0;   // primary_clk is always inclk0
        if (l_pll_type == "fast" || (l_pll_type == "left_right"))
            l_switch_over_type = "manual";

        if (l_switch_over_type == "manual" && clkswitch_ipd === 1'b1)
        begin
            current_clock_man = 1;
            active_clock = 1;
        end
        got_curr_clk_falling_edge_after_clkswitch = 0;
        clk0_count = 0;
        clk1_count = 0;

        // initialize reconfiguration variables
        // quiet_time
        quiet_time = slowest_clk  ( c_high_val[0]+c_low_val[0], c_mode_val[0],
                                    c_high_val[1]+c_low_val[1], c_mode_val[1],
                                    c_high_val[2]+c_low_val[2], c_mode_val[2],
                                    c_high_val[3]+c_low_val[3], c_mode_val[3],
                                    c_high_val[4]+c_low_val[4], c_mode_val[4],
                                    c_high_val[5]+c_low_val[5], c_mode_val[5],
                                    c_high_val[6]+c_low_val[6], c_mode_val[6],
                                    c_high_val[7]+c_low_val[7], c_mode_val[7],
                                    c_high_val[8]+c_low_val[8], c_mode_val[8],
                                    c_high_val[9]+c_low_val[9], c_mode_val[9],
                                    refclk_period, m_val[0]);
        reconfig_err = 0;
        error = 0;
        
        
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        got_first_scanclk = 0;
        got_first_gated_scanclk = 0;
        gated_scanclk = 1;
        scanread_setup_violation = 0;
        index = 0;

        vco_over  = 1'b0;
        vco_under = 1'b0;
        
        // Initialize the scan chain 
        
        // LF unused : bit 1
        scan_data[-1:0] = 2'b00;
        // LF Capacitance : bits 1,2 : all values are legal
        scan_data[1:2] = loop_filter_c_bits;
        // LF Resistance : bits 3-7
        scan_data[3:7] = loop_filter_r_bits;
        
        // VCO post scale
        if(vco_post_scale == 1)
        begin
            scan_data[8] = 1'b1;
            vco_val_old_bit_setting = 1'b1;
        end
        else
        begin
            scan_data[8] = 1'b0;
            vco_val_old_bit_setting = 1'b0;
        end
            
        scan_data[9:13] = 5'b00000;
        // CP
        // Bit 8 : CRBYPASS
        // Bit 9-13 : unused
        // Bits 14-16 : all values are legal                 
                scan_data[14:16] = charge_pump_current_bits;
        // store as old values
        
        cp_curr_old_bit_setting = charge_pump_current_bits;
        lfc_val_old_bit_setting = loop_filter_c_bits;
        lfr_val_old_bit_setting = loop_filter_r_bits;
            
        // C counters (start bit 53) bit 1:mode(bypass),bit 2-9:high,bit 10:mode(odd/even),bit 11-18:low
        for (i = 0; i < num_output_cntrs; i = i + 1)
        begin
            // 1. Mode - bypass
            if (c_mode_val[i] == "bypass")
            begin
                scan_data[53 + i*18 + 0] = 1'b1;
                if (c_mode_val[i] == "   odd")
                    scan_data[53 + i*18 + 9] = 1'b1;
                else
                    scan_data[53 + i*18 + 9] = 1'b0;
            end
            else
            begin
                scan_data[53 + i*18 + 0] = 1'b0;
                // 3. Mode - odd/even
                if (c_mode_val[i] == "   odd")
                    scan_data[53 + i*18 + 9] = 1'b1;
                else
                    scan_data[53 + i*18 + 9] = 1'b0;
            end
            // 2. Hi
            c_val = c_high_val[i];
            for (j = 1; j <= 8; j = j + 1)
                scan_data[53 + i*18 + j]  = c_val[8 - j];
   
            // 4. Low
            c_val = c_low_val[i];
            for (j = 10; j <= 17; j = j + 1)
                scan_data[53 + i*18 + j] = c_val[17 - j];
        end
            
        // M counter
        // 1. Mode - bypass (bit 17)
        if (m_mode_val[0] == "bypass")
                scan_data[35] = 1'b1;
        else
                scan_data[35] = 1'b0;
       
        // 2. High (bit 18-25)
        // 3. Mode - odd/even (bit 26)
        if (m_val[0] % 2 == 0)
        begin
            // M is an even no. : set M high = low,
            // set odd/even bit to 0
                scan_data[36:43]= m_val[0]/2;
                scan_data[44] = 1'b0;
        end
        else 
        begin 
            // M is odd : M high = low + 1
                scan_data[36:43] = m_val[0]/2 + 1;
                scan_data[44] = 1'b1;             
        end
        // 4. Low (bit 27-34)
            scan_data[45:52] = m_val[0]/2;

        
        // N counter
        // 1. Mode - bypass (bit 35)
        if (n_mode_val[0] == "bypass")
                scan_data[17] = 1'b1;
        else 
                scan_data[17] = 1'b0;
        // 2. High (bit 36-43)
        // 3. Mode - odd/even (bit 44)
        if (n_val[0] % 2 == 0)
        begin
            // N is an even no. : set N high = low,
            // set odd/even bit to 0
                scan_data[18:25] = n_val[0]/2;
                scan_data[26] = 1'b0;         
        end
        else 
        begin // N is odd : N high = N low + 1
                scan_data[18:25] = n_val[0]/2+ 1;
                scan_data[26] = 1'b1;         
        end
        // 4. Low (bit 45-52)
                scan_data[27:34] = n_val[0]/2;


        l_index = 1;
        stop_vco = 0;
        cycles_to_lock = 0;
        cycles_to_unlock = 0;
        locked_tmp = 0;
        pll_is_locked = 0;
        no_warn = 1'b0;
        
        pfd_locked = 1'b0;
        cycles_pfd_high = 0;
        cycles_pfd_low  = 0;

        // check if pll is in test mode
        if (m_test_source != -1 || c0_test_source != -1 || c1_test_source != -1 || c2_test_source != -1 || c3_test_source != -1 || c4_test_source != -1)
            pll_in_test_mode = 1'b1;
        else
            pll_in_test_mode = 1'b0;

        pll_is_in_reset = 0;
        pll_has_just_been_reconfigured = 0;
        if (l_pll_type == "fast" || l_pll_type == "lvds" || l_pll_type == "left_right")
            is_fast_pll = 1;
        else is_fast_pll = 0;

        if (c1_use_casc_in == "on")
            ic1_use_casc_in = 1;
        else
            ic1_use_casc_in = 0;
        if (c2_use_casc_in == "on")
            ic2_use_casc_in = 1;
        else
            ic2_use_casc_in = 0;
        if (c3_use_casc_in == "on")
            ic3_use_casc_in = 1;
        else
            ic3_use_casc_in = 0;
        if (c4_use_casc_in == "on")
            ic4_use_casc_in = 1;
        else
            ic4_use_casc_in = 0;

        tap0_is_active = 1;
        
// To display clock mapping       
    case( i_clk0_counter)
            "c0" : clk_num[0] = "  clk0";
            "c1" : clk_num[0] = "  clk1";
            "c2" : clk_num[0] = "  clk2";
            "c3" : clk_num[0] = "  clk3";
            "c4" : clk_num[0] = "  clk4";
            default:clk_num[0] = "unused";
    endcase
    
        case( i_clk1_counter)
            "c0" : clk_num[1] = "  clk0";
            "c1" : clk_num[1] = "  clk1";
            "c2" : clk_num[1] = "  clk2";
            "c3" : clk_num[1] = "  clk3";
            "c4" : clk_num[1] = "  clk4";
            default:clk_num[1] = "unused";
    endcase
        
    case( i_clk2_counter)
            "c0" : clk_num[2] = "  clk0";
            "c1" : clk_num[2] = "  clk1";
            "c2" : clk_num[2] = "  clk2";
            "c3" : clk_num[2] = "  clk3";
            "c4" : clk_num[2] = "  clk4";
            default:clk_num[2] = "unused";
    endcase
        
    case( i_clk3_counter)
            "c0" : clk_num[3] = "  clk0";
            "c1" : clk_num[3] = "  clk1";
            "c2" : clk_num[3] = "  clk2";
            "c3" : clk_num[3] = "  clk3";
            "c4" : clk_num[3] = "  clk4";
            default:clk_num[3] = "unused";
    endcase
        
    case( i_clk4_counter)
            "c0" : clk_num[4] = "  clk0";
            "c1" : clk_num[4] = "  clk1";
            "c2" : clk_num[4] = "  clk2";
            "c3" : clk_num[4] = "  clk3";
            "c4" : clk_num[4] = "  clk4";
            default:clk_num[4] = "unused";
    endcase
        

        end


// Clock Switchover

always @(clkswitch_ipd)
begin
    if (clkswitch_ipd === 1'b1 && l_switch_over_type == "auto")
        external_switch = 1;
    else if (l_switch_over_type == "manual") 
    begin
        if(clkswitch_ipd === 1'b1)
            switch_clock = 1'b1;
        else
            switch_clock = 1'b0;
    end
end


always @(posedge inclk0_ipd)
begin
// Determine the inclk0 frequency
    if (first_inclk0_edge_detect == 1'b0)
        begin
            first_inclk0_edge_detect = 1'b1;
        end
    else
        begin
            last_inclk0_period = inclk0_period;
            inclk0_period = $realtime - last_inclk0_edge;
        end
    last_inclk0_edge = $realtime;

end

always @(posedge inclk1_ipd)
begin
// Determine the inclk1 frequency
    if (first_inclk1_edge_detect == 1'b0)
        begin
            first_inclk1_edge_detect = 1'b1;
        end
    else
        begin
            last_inclk1_period = inclk1_period;
            inclk1_period = $realtime - last_inclk1_edge;
        end
    last_inclk1_edge = $realtime;

end

    always @(inclk0_ipd or inclk1_ipd)
    begin
        if(switch_clock == 1'b1)
        begin
                if(current_clock_man == 0)
                begin
                    current_clock_man = 1;
                    active_clock = 1;
                end
                else
                begin
                    current_clock_man = 0;
                    active_clock = 0;
                end
                switch_clock = 1'b0;
            end

        if (current_clock_man == 0)
            inclk_man = inclk0_ipd;
        else
            inclk_man = inclk1_ipd;


        // save the inclk event value
        if (inclk0_ipd !== inclk0_last_value)
        begin
            if (current_clock != 0)
                other_clock_value = inclk0_ipd;
        end
        if (inclk1_ipd !== inclk1_last_value)
        begin
            if (current_clock != 1)
                other_clock_value = inclk1_ipd;
        end

        // check if either input clk is bad
        if (inclk0_ipd === 1'b1 && inclk0_ipd !== inclk0_last_value)
        begin
            clk0_count = clk0_count + 1;
            clk0_is_bad = 0;
            clk1_count = 0;
            if (clk0_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk1_is_bad = 1;
                if (current_clock == 1)
                    current_clk_is_bad = 1;
            end
        end
        if (inclk1_ipd === 1'b1 && inclk1_ipd !== inclk1_last_value)
        begin
            clk1_count = clk1_count + 1;
            clk1_is_bad = 0;
            clk0_count = 0;
            if (clk1_count > 2)
            begin
                // no event on other clk for 2 cycles
                clk0_is_bad = 1;
                if (current_clock == 0)
                    current_clk_is_bad = 1;
            end
        end

        // check if the bad clk is the primary clock, which is always clk0
        if (clk0_is_bad == 1'b1)
            primary_clk_is_bad = 1;
        else
            primary_clk_is_bad = 0;

        // actual switching -- manual switch
        if ((inclk0_ipd !== inclk0_last_value) && current_clock == 0)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk0_ipd === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_es = inclk0_ipd;
                end
            end
            else inclk_es = inclk0_ipd;
        end
        if ((inclk1_ipd !== inclk1_last_value) && current_clock == 1)
        begin
            if (external_switch == 1'b1)
            begin
                if (!got_curr_clk_falling_edge_after_clkswitch)
                begin
                    if (inclk1_ipd === 1'b0)
                        got_curr_clk_falling_edge_after_clkswitch = 1;
                    inclk_es = inclk1_ipd;
                end
            end
            else inclk_es = inclk1_ipd;
        end

        // actual switching -- automatic switch
        if ((other_clock_value == 1'b1) && (other_clock_value != other_clock_last_value) && l_enable_switch_over_counter == "on" && primary_clk_is_bad)
            switch_over_count = switch_over_count + 1;
        
        if ((other_clock_value == 1'b0) && (other_clock_value != other_clock_last_value))
        begin
            if ((external_switch && (got_curr_clk_falling_edge_after_clkswitch || current_clk_is_bad)) || (primary_clk_is_bad && (clkswitch_ipd !== 1'b1) && ((l_enable_switch_over_counter == "off" || switch_over_count == switch_over_counter))))
            begin
                if (areset_ipd === 1'b0)
                begin
                    if ((inclk0_period > inclk1_period) && (inclk1_period != 0))
                        diff_percent_period = (( inclk0_period - inclk1_period ) * 100) / inclk1_period;
                    else if (inclk0_period != 0)
                        diff_percent_period = (( inclk1_period - inclk0_period ) * 100) / inclk0_period;

                    if((diff_percent_period > 20)&& (l_switch_over_type == "auto"))
                    begin
                        $display ("Warning : The input clock frequencies specified for the specified PLL are too far apart for auto-switch-over feature to work properly. Please make sure that the clock frequencies are 20 percent apart for correct functionality.");
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                end

                got_curr_clk_falling_edge_after_clkswitch = 0;
                if (current_clock == 0)
                    current_clock = 1;
                else
                    current_clock = 0;
                    
                active_clock = ~active_clock;
                switch_over_count = 0;
                external_switch = 0;
                current_clk_is_bad = 0;
            end
            else if(l_switch_over_type == "auto")
                begin
                    if(current_clock == 0 && clk0_is_bad == 1'b1 && clk1_is_bad == 1'b0 )
                        begin
                            current_clock = 1;
                            active_clock = ~active_clock;
                        end 
                
                    if(current_clock == 1 && clk1_is_bad == 1'b1 && clk0_is_bad == 1'b0 )
                        begin
                            current_clock = 0;
                            active_clock = ~active_clock;
                        end
                end     
        end
        
        if(l_switch_over_type == "manual")
            inclk_n = inclk_man;
        else
            inclk_n = inclk_es;
            
        inclk0_last_value = inclk0_ipd;
        inclk1_last_value = inclk1_ipd;
        other_clock_last_value = other_clock_value;

    end

    and (clkbad[0], clk0_is_bad, 1'b1);
    and (clkbad[1], clk1_is_bad, 1'b1);
    and (activeclock, active_clock, 1'b1);


    assign inclk_m = (m_test_source == 0) ? fbclk : (m_test_source == 1) ? refclk : inclk_m_from_vco; 
                       

    MF_cycloneiiigl_m_cntr m1 (.clk(inclk_m),
                        .reset(areset_ipd || stop_vco),
                        .cout(fbclk),
                        .initial_value(m_initial_val),
                        .modulus(m_val[0]),
                        .time_delay(m_delay));

    MF_cycloneiiigl_n_cntr n1 (.clk(inclk_n),
                        .reset(areset_ipd),
                        .cout(refclk),
                        .modulus(n_val[0]));


    cycloneiiigl_post_divider d1 (.clk(inclk_m_from_vco),
                        .reset(areset_ipd),
                        .cout(icdr_clk));
    defparam d1.dpa_divider = dpa_divider;

    // Update clock on /o counters from corresponding VCO tap
    assign inclk_m_from_vco  = vco_tap[m_ph_val];
    assign inclk_c0_from_vco = vco_tap[c_ph_val[0]];
    assign inclk_c1_from_vco = vco_tap[c_ph_val[1]];
    assign inclk_c2_from_vco = vco_tap[c_ph_val[2]];
    assign inclk_c3_from_vco = vco_tap[c_ph_val[3]];
    assign inclk_c4_from_vco = vco_tap[c_ph_val[4]];
always @(vco_out)
    begin
        // check which VCO TAP has event
        for (x = 0; x <= 7; x = x + 1)
        begin
            if (vco_out[x] !== vco_out_last_value[x])
            begin
                // TAP 'X' has event
                if ((x == 0) && (!pll_is_in_reset) && (stop_vco !== 1'b1))
                begin
                    if (vco_out[0] == 1'b1)
                        tap0_is_active = 1;
                    if (tap0_is_active == 1'b1)
                        vco_tap[0] <= vco_out[0];
                end
                else if (tap0_is_active == 1'b1)
                    vco_tap[x] <= vco_out[x];
                if (stop_vco === 1'b1)
                    vco_out[x] <= 1'b0;
            end
        end
        vco_out_last_value = vco_out;
    end

    always @(vco_tap)
    begin
        // Update phase taps for C/M counters on negative edge of VCO clock output
        
        if (update_phase == 1'b1)
        begin
            for (x = 0; x <= 7; x = x + 1)
            begin
                if ((vco_tap[x] === 1'b0) && (vco_tap[x] !== vco_tap_last_value[x]))
                begin
                    for (y = 0; y < 10; y = y + 1)
                    begin
                        if (c_ph_val_tmp[y] == x)
                            c_ph_val[y] = c_ph_val_tmp[y];
                    end
                    if (m_ph_val_tmp == x)
                        m_ph_val = m_ph_val_tmp;
                end
            end
            update_phase <= #(0.5*scanclk_period) 1'b0;
        end

        // On reset, set all C/M counter phase taps to POF programmed values
        if (areset_ipd === 1'b1)
        begin
            m_ph_val = m_ph_val_orig;
            m_ph_val_tmp = m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
            begin
                c_ph_val[i] = c_ph_val_orig[i];
                c_ph_val_tmp[i] = c_ph_val_orig[i];
            end
        end

        vco_tap_last_value = vco_tap;
    end

    assign inclk_c0 = (c0_test_source == 0) ? fbclk : (c0_test_source == 1) ? refclk : inclk_c0_from_vco;

    MF_cycloneiiigl_scale_cntr c0 (.clk(inclk_c0),
                            .reset(areset_ipd  || stop_vco),
                            .cout(c0_clk),
                            .high(c_high_val[0]),
                            .low(c_low_val[0]),
                            .initial_value(c_initial_val[0]),
                            .mode(c_mode_val[0]),
                            .ph_tap(c_ph_val[0]));

    // Update /o counters mode and duty cycle immediately after configupdate is asserted
    always @(posedge scanclk_ipd)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[0] <= c_high_val_tmp[0];
            c_mode_val[0] <= c_mode_val_tmp[0];
            c0_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk_ipd)
    begin
        if (c0_rising_edge_transfer_done)
        begin
            c_low_val[0] <= c_low_val_tmp[0];
        end
    end

    assign inclk_c1 = (c1_test_source == 0) ? fbclk : (c1_test_source == 1) ? refclk : (ic1_use_casc_in == 1) ? c0_clk : inclk_c1_from_vco;
    
    MF_cycloneiiigl_scale_cntr c1 (.clk(inclk_c1),
                            .reset(areset_ipd || stop_vco),
                            .cout(c1_clk),
                            .high(c_high_val[1]),
                            .low(c_low_val[1]),
                            .initial_value(c_initial_val[1]),
                            .mode(c_mode_val[1]),
                            .ph_tap(c_ph_val[1]));

    always @(posedge scanclk_ipd)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[1] <= c_high_val_tmp[1];
            c_mode_val[1] <= c_mode_val_tmp[1];
            c1_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk_ipd)
    begin
        if (c1_rising_edge_transfer_done)
        begin
            c_low_val[1] <= c_low_val_tmp[1];
        end
    end

    assign inclk_c2 = (c2_test_source == 0) ? fbclk : (c2_test_source == 1) ? refclk :(ic2_use_casc_in == 1) ? c1_clk : inclk_c2_from_vco;

    MF_cycloneiiigl_scale_cntr c2 (.clk(inclk_c2),
                            .reset(areset_ipd || stop_vco),
                            .cout(c2_clk),
                            .high(c_high_val[2]),
                            .low(c_low_val[2]),
                            .initial_value(c_initial_val[2]),
                            .mode(c_mode_val[2]),
                            .ph_tap(c_ph_val[2]));

    always @(posedge scanclk_ipd)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[2] <= c_high_val_tmp[2];
            c_mode_val[2] <= c_mode_val_tmp[2];
            c2_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk_ipd)
    begin
        if (c2_rising_edge_transfer_done)
        begin
            c_low_val[2] <= c_low_val_tmp[2];
        end
    end

    assign inclk_c3 = (c3_test_source == 0) ? fbclk : (c3_test_source == 1) ? refclk : (ic3_use_casc_in == 1) ? c2_clk : inclk_c3_from_vco;
    
    MF_cycloneiiigl_scale_cntr c3 (.clk(inclk_c3),
                            .reset(areset_ipd  || stop_vco),
                            .cout(c3_clk),
                            .high(c_high_val[3]),
                            .low(c_low_val[3]),
                            .initial_value(c_initial_val[3]),
                            .mode(c_mode_val[3]),
                            .ph_tap(c_ph_val[3]));

    always @(posedge scanclk_ipd)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[3] <= c_high_val_tmp[3];
            c_mode_val[3] <= c_mode_val_tmp[3];
            c3_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk_ipd)
    begin
        if (c3_rising_edge_transfer_done)
        begin
            c_low_val[3] <= c_low_val_tmp[3];
        end
    end

    assign inclk_c4 = ((c4_test_source == 0) ? fbclk : (c4_test_source == 1) ? refclk :  (ic4_use_casc_in == 1) ? c3_clk : inclk_c4_from_vco);
    MF_cycloneiiigl_scale_cntr c4 (.clk(inclk_c4),
                            .reset(areset_ipd || stop_vco),
                            .cout(c4_clk),
                            .high(c_high_val[4]),
                            .low(c_low_val[4]),
                            .initial_value(c_initial_val[4]),
                            .mode(c_mode_val[4]),
                            .ph_tap(c_ph_val[4]));

    always @(posedge scanclk_ipd)
    begin
        if (update_conf_latches_reg == 1'b1)
        begin
            c_high_val[4] <= c_high_val_tmp[4];
            c_mode_val[4] <= c_mode_val_tmp[4];
            c4_rising_edge_transfer_done = 1;
        end
    end
    always @(negedge scanclk_ipd)
    begin
        if (c4_rising_edge_transfer_done)
        begin
            c_low_val[4] <= c_low_val_tmp[4];
        end
    end

    
assign locked = (test_bypass_lock_detect == "on") ? pfd_locked : locked_tmp;

// Register scanclk enable
    always @(negedge scanclk_ipd)
        scanclkena_reg <= scanclkena_ipd;
        
// Negative edge flip-flop in front of scan-chain

    always @(negedge scanclk_ipd)
    begin
        if (scanclkena_reg)
        begin
            scandata_in <= scandata_ipd;
        end
    end
   
// Scan chain
    always @(posedge scanclk_ipd)
    begin
        if (got_first_scanclk === 1'b0)
                got_first_scanclk = 1'b1;
        else
                scanclk_period = $time - scanclk_last_rising_edge;
        if (scanclkena_reg) 
        begin        
            for (j = scan_chain_length-2; j >= 0; j = j - 1)
                scan_data[j] = scan_data[j - 1];
            scan_data[-1] <= scandata_in;
        end
        scanclk_last_rising_edge = $realtime;
    end
    
// Scan output
    assign scandataout_tmp = scan_data[SCAN_CHAIN - 2];

// Negative edge flip-flop in rear of scan-chain

    always @(negedge scanclk_ipd)
    begin
        if (scanclkena_reg)
        begin
            scandata_out <= scandataout_tmp;
        end
    end
    
// Scan complete
    always @(negedge scandone_tmp)
    begin
            if (got_first_scanclk === 1'b1)
            begin
            if (reconfig_err == 1'b0)
            begin
                $display("NOTE : PLL Reprogramming completed with the following values (Values in parantheses are original values) : ");
                $display ("Time: %0t  Instance: %m", $time);

                $display("               N modulus =   %0d (%0d) ", n_val[0], n_val_old[0]);
                $display("               M modulus =   %0d (%0d) ", m_val[0], m_val_old[0]);
                

                for (i = 0; i < num_output_cntrs; i=i+1)
                begin
                    $display("              %s :    C%0d  high = %0d (%0d),       C%0d  low = %0d (%0d),       C%0d  mode = %s (%s)", clk_num[i],i, c_high_val[i], c_high_val_old[i], i, c_low_val_tmp[i], c_low_val_old[i], i, c_mode_val[i], c_mode_val_old[i]);
                end

                // display Charge pump and loop filter values
                if (pll_reconfig_display_full_setting == 1'b1)
                begin
                    $display ("               Charge Pump Current (uA) =   %0d (%0d) ", cp_curr_val, cp_curr_old);
                    $display ("               Loop Filter Capacitor (pF) =   %0d (%0d) ", lfc_val, lfc_old);
                    $display ("               Loop Filter Resistor (Kohm) =   %s (%s) ", lfr_val, lfr_old);
                    $display ("               VCO_Post_Scale  =   %0d (%0d) ", vco_cur, vco_old);
                end
                else
                begin
                    $display ("               Charge Pump Current  =   %0d (%0d) ", cp_curr_bit_setting, cp_curr_old_bit_setting);
                    $display ("               Loop Filter Capacitor  =   %0d (%0d) ", lfc_val_bit_setting, lfc_val_old_bit_setting);
                    $display ("               Loop Filter Resistor   =   %0d (%0d) ", lfr_val_bit_setting, lfr_val_old_bit_setting);
                    $display ("               VCO_Post_Scale   =   %b (%b) ", vco_val_bit_setting, vco_val_old_bit_setting);
                end
                cp_curr_old_bit_setting = cp_curr_bit_setting;
                lfc_val_old_bit_setting = lfc_val_bit_setting;
                lfr_val_old_bit_setting = lfr_val_bit_setting;
                vco_val_old_bit_setting = vco_val_bit_setting;
            end
            else begin
                $display("Warning : Errors were encountered during PLL reprogramming. Please refer to error/warning messages above.");
                $display ("Time: %0t  Instance: %m", $time);
            end
            end
    end

// ************ PLL Phase Reconfiguration ************* //

// Latch updown,counter values at pos edge of scan clock
always @(posedge scanclk_ipd)
begin
    if (phasestep_reg == 1'b1)
    begin
        if (phasestep_high_count == 1)
        begin
            phasecounterselect_reg <= phasecounterselect_ipd;
            phaseupdown_reg <= phaseupdown_ipd;
            // start reconfiguration
            if (phasecounterselect_ipd < 3'b111) // no counters selected
            begin
                if (phasecounterselect_ipd == 0) // all output counters selected
                begin
                    for (i = 0; i < num_output_cntrs; i = i + 1)
                        c_ph_val_tmp[i] = (phaseupdown_ipd == 1'b1) ? 
                                    (c_ph_val_tmp[i] + 1) % num_phase_taps :
                                    (c_ph_val_tmp[i] == 0) ? num_phase_taps - 1 : (c_ph_val_tmp[i] - 1) % num_phase_taps ;
                end
                else if (phasecounterselect_ipd == 1) // select M counter
                begin
                    m_ph_val_tmp = (phaseupdown_ipd == 1'b1) ? 
                                (m_ph_val + 1) % num_phase_taps :
                                (m_ph_val == 0) ? num_phase_taps - 1 : (m_ph_val - 1) % num_phase_taps ;
                end
                else // select C counters
                begin
                    select_counter = phasecounterselect_ipd - 2;
                    c_ph_val_tmp[select_counter] =  (phaseupdown_ipd == 1'b1) ? 
                                            (c_ph_val_tmp[select_counter] + 1) % num_phase_taps :
                                            (c_ph_val_tmp[select_counter] == 0) ? num_phase_taps - 1 : (c_ph_val_tmp[select_counter] - 1) % num_phase_taps ;
                end
                update_phase <= 1'b1;
            end 
           
        end
        phasestep_high_count = phasestep_high_count + 1;
       
    end
end

// Latch phase enable (same as phasestep) on neg edge of scan clock
always @(negedge scanclk_ipd)
begin
    phasestep_reg <= phasestep;
end

always @(posedge phasestep) 
begin
    if (update_phase == 1'b0) phasestep_high_count = 0; // phase adjustments must be 1 cycle apart
                                                        // if not, next phasestep cycle is skipped
end

// ************ PLL Full Reconfiguration ************* //
assign update_conf_latches = configupdate_ipd;


        // reset counter transfer flags
    always @(negedge scandone_tmp)
    begin
        c0_rising_edge_transfer_done = 0;
        c1_rising_edge_transfer_done = 0;
        c2_rising_edge_transfer_done = 0;
        c3_rising_edge_transfer_done = 0;
        c4_rising_edge_transfer_done = 0;
        update_conf_latches_reg <= 1'b0;
    end


    always @(posedge update_conf_latches)
    begin
        initiate_reconfig <= 1'b1;
    end
   
    always @(posedge areset_ipd)
    begin
        if (scandone_tmp == 1'b1) scandone_tmp = 1'b0;
    end
   
    always @(posedge scanclk_ipd)
    begin
        if (initiate_reconfig == 1'b1) 
        begin
            initiate_reconfig <= 1'b0;
            $display ("NOTE : PLL Reprogramming initiated ....");
            $display ("Time: %0t  Instance: %m", $time);

            scandone_tmp <= #(scanclk_period) 1'b1;
            update_conf_latches_reg <= update_conf_latches;

            error = 0;
            reconfig_err = 0;
            scanread_setup_violation = 0;

            // save old values
            cp_curr_old = cp_curr_val;
            lfc_old = lfc_val;
            lfr_old = lfr_val;
            vco_old = vco_cur;
            // save old values of bit settings
            cp_curr_bit_setting = scan_data[14:16];
            lfc_val_bit_setting = scan_data[1:2];
            lfr_val_bit_setting = scan_data[3:7];
            vco_val_bit_setting = scan_data[8];

            // LF unused : bit 1
            // LF Capacitance : bits 1,2 : all values are legal
            if ((l_pll_type == "fast") || (l_pll_type == "lvds") || (l_pll_type == "left_right"))
                lfc_val = fpll_loop_filter_c_arr[scan_data[1:2]];
            else
                lfc_val = loop_filter_c_arr[scan_data[1:2]];

            // LF Resistance : bits 3-7
            // valid values - 00000,00100,10000,10100,11000,11011,11100,11110
            if (((scan_data[3:7] == 5'b00000) || (scan_data[3:7] == 5'b00100)) || 
                ((scan_data[3:7] == 5'b10000) || (scan_data[3:7] == 5'b10100)) ||
                ((scan_data[3:7] == 5'b11000) || (scan_data[3:7] == 5'b11011)) ||
                ((scan_data[3:7] == 5'b11100) || (scan_data[3:7] == 5'b11110))
            )
            begin
                lfr_val =   (scan_data[3:7] == 5'b00000) ? "20" :
                            (scan_data[3:7] == 5'b00100) ? "16" :
                            (scan_data[3:7] == 5'b10000) ? "12" :
                            (scan_data[3:7] == 5'b10100) ? "8" :
                            (scan_data[3:7] == 5'b11000) ? "6" :
                            (scan_data[3:7] == 5'b11011) ? "4" : 
                            (scan_data[3:7] == 5'b11100) ? "2" : "1";
            end

            //VCO post scale value
            if (scan_data[8] === 1'b1)  // vco_post_scale = 1
            begin
                if ((vco_max != 0) && (vco_min != 0))
                begin
                    i_vco_max = vco_max/2 +500;
                    i_vco_min = vco_min/2 -500;
                end
                vco_cur = 1;
            end
            else
            begin
                i_vco_max = vco_max * 1000;
                i_vco_min = vco_min * 1000;
                vco_cur = 2;
            end          

            // CP
            // Bit 8 : CRBYPASS
            // Bit 9-13 : unused
            // Bits 14-16 : all values are legal
            cp_curr_val = scan_data[14:16];

            // save old values for display info.
            for (i=0; i<=1; i=i+1)
            begin
                m_val_old[i] = m_val[i];
                n_val_old[i] = n_val[i];
                m_mode_val_old[i] = m_mode_val[i];
                n_mode_val_old[i] = n_mode_val[i];
            end
            for (i=0; i< num_output_cntrs; i=i+1)
            begin
                c_high_val_old[i] = c_high_val[i];
                c_low_val_old[i] = c_low_val[i];
                c_mode_val_old[i] = c_mode_val[i];
            end

            // M counter
            // 1. Mode - bypass (bit 17)
            if (scan_data[17] == 1'b1)
                n_mode_val[0] = "bypass";
            // 3. Mode - odd/even (bit 26)
            else if (scan_data[26] == 1'b1)
                n_mode_val[0] = "   odd";         
            else
                n_mode_val[0] = "  even";         
            // 2. High (bit 18-25)
                n_hi = scan_data[18:25];
            // 4. Low (bit 27-34)
                n_lo = scan_data[27:34]; 


            // N counter
            // 1. Mode - bypass (bit 35)
            if (scan_data[35] == 1'b1)
                m_mode_val[0] = "bypass";
            // 3. Mode - odd/even (bit 44)
            else if (scan_data[44] == 1'b1)
                m_mode_val[0] = "   odd";
            else
                m_mode_val[0] = "  even";
            
            // 2. High (bit 36-43)
                m_hi = scan_data[36:43];
            
            // 4. Low (bit 45-52)
                m_lo = scan_data[45:52]; 


            
//Update the current M and N counter values if the counters are NOT bypassed

if (m_mode_val[0] != "bypass")
m_val[0] = m_hi + m_lo;
if (n_mode_val[0] != "bypass")  
n_val[0] = n_hi + n_lo;
            


            // C counters (start bit 53) bit 1:mode(bypass),bit 2-9:high,bit 10:mode(odd/even),bit 11-18:low

            for (i = 0; i < num_output_cntrs; i = i + 1)
            begin
                // 1. Mode - bypass
                if (scan_data[53 + i*18 + 0] == 1'b1)
                        c_mode_val_tmp[i] = "bypass";
                // 3. Mode - odd/even
                else if (scan_data[53 + i*18 + 9] == 1'b1)
                    c_mode_val_tmp[i] = "   odd";
                else
                    c_mode_val_tmp[i] = "  even";
                    
                // 2. Hi
                for (j = 1; j <= 8; j = j + 1)
                    c_val[8-j] = scan_data[53 + i*18 + j];
                c_hval[i] = c_val[7:0];
                if (c_hval[i] !== 32'h00000000)
                    c_high_val_tmp[i] = c_hval[i];
                else
                    c_high_val_tmp[i] = 9'b100000000;
                // 4. Low 
                for (j = 10; j <= 17; j = j + 1)
                    c_val[17 - j] = scan_data[53 + i*18 + j]; 
                c_lval[i] = c_val[7:0];
                if (c_lval[i] !== 32'h00000000)
                    c_low_val_tmp[i] = c_lval[i];  
                else
                    c_low_val_tmp[i] = 9'b100000000; 
            end

            // Legality Checks
            
            if (m_mode_val[0] != "bypass")
            begin
            if ((m_hi !== m_lo) && (m_mode_val[0] != "   odd"))
            begin
                    reconfig_err = 1;
                    $display ("Warning : The M counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
            end
            else if (m_hi !== 8'b00000000)
            begin
                    // counter value
                    m_val_tmp[0] = m_hi + m_lo;
            end
            else
                m_val_tmp[0] =  9'b100000000; 
            end
            else
                m_val_tmp[0] = 8'b00000001;
                
            if (n_mode_val[0] != "bypass")
            begin
            if ((n_hi !== n_lo) && (n_mode_val[0] != "   odd"))
            begin
                    reconfig_err = 1;
                    $display ("Warning : The N counter of the %s Fast PLL should be configured for 50%% duty cycle only. In this case the HIGH and LOW moduli programmed will result in a duty cycle other than 50%%, which is illegal. Reconfiguration may not work", family_name);
                    $display ("Time: %0t  Instance: %m", $time);
            end
            else if (n_hi !== 8'b00000000)
            begin
                    // counter value
                    n_val[0] = n_hi + n_lo;
            end
            else
                n_val[0] =  9'b100000000; 
            end
            else
                n_val[0] = 8'b00000001;
                           
                 

// TODO : Give warnings/errors in the following cases?
// 1. Illegal counter values (error)
// 2. Change of mode (warning)
// 3. Only 50% duty cycle allowed for M counter (odd mode - hi-lo=1,even - hi-lo=0)

        end
    end
    
    // Self reset on loss of lock
    assign reset_self = (l_self_reset_on_loss_lock == "on") ? ~pll_is_locked : 1'b0;

    always @(posedge reset_self)
    begin
        $display (" Note : %s PLL self reset due to loss of lock", family_name);
        $display ("Time: %0t  Instance: %m", $time);
    end
    
    // Phase shift on /o counters
    
    always @(schedule_vco or areset_ipd)
    begin
        sched_time = 0;
    
        for (i = 0; i <= 7; i=i+1)
            last_phase_shift[i] = phase_shift[i];
     
        cycle_to_adjust = 0;
        l_index = 1;
        m_times_vco_period = new_m_times_vco_period;
            
        // give appropriate messages
        // if areset was asserted
        if (areset_ipd === 1'b1 && areset_ipd_last_value !== areset_ipd)
        begin
            $display (" Note : %s PLL was reset", family_name);
            $display ("Time: %0t  Instance: %m", $time);
            // reset lock parameters
            locked_tmp = 0;
            pll_is_locked = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
            tap0_is_active = 0;
            for (x = 0; x <= 7; x=x+1)
                vco_tap[x] <= 1'b0;
        end
    
        // illegal value on areset_ipd
        if (areset_ipd === 1'bx && (areset_ipd_last_value === 1'b0 || areset_ipd_last_value === 1'b1))
        begin
            $display("Warning : Illegal value 'X' detected on ARESET input");
            $display ("Time: %0t  Instance: %m", $time);
        end
    
        if ((areset_ipd == 1'b1))
        begin
            pll_is_in_reset = 1;
            got_first_refclk = 0;
            got_second_refclk = 0;
        end
                            
        if ((schedule_vco !== schedule_vco_last_value) && (areset_ipd == 1'b1 || stop_vco == 1'b1))
        begin
   
            // drop VCO taps to 0
            for (i = 0; i <= 7; i=i+1)
            begin
                for (j = 0; j <= last_phase_shift[i] + 1; j=j+1)
                    vco_out[i] <= #(j) 1'b0;
                phase_shift[i] = 0;
                last_phase_shift[i] = 0;
            end
    
            // reset lock parameters
            locked_tmp = 0;
            pll_is_locked = 0;
            cycles_to_lock = 0;
            cycles_to_unlock = 0;
    
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = 0;
            got_first_fbclk = 0;
            fbclk_time = 0;
            first_fbclk_time = 0;
            fbclk_period = 0;
    
            first_schedule = 1;
            vco_val = 0;
            vco_period_was_phase_adjusted = 0;
            phase_adjust_was_scheduled = 0;

            // reset all counter phase tap values to POF programmed values
            m_ph_val = m_ph_val_orig;
            for (i=0; i<= 5; i=i+1)
                c_ph_val[i] = c_ph_val_orig[i];
    
        end else if (areset_ipd === 1'b0 && stop_vco === 1'b0)
        begin
            // else note areset deassert time
            // note it as refclk_time to prevent false triggering
            // of stop_vco after areset
            if (areset_ipd === 1'b0 && areset_ipd_last_value === 1'b1 && pll_is_in_reset === 1'b1)
            begin
                refclk_time = $time;
                pll_is_in_reset = 0;
                locked_tmp = 1'b0;
            end
    
            // calculate loop_xplier : this will be different from m_val in ext. fbk mode
            loop_xplier = m_val[0];
            loop_initial = i_m_initial - 1;
            loop_ph = m_ph_val;
    
            // convert initial value to delay
            initial_delay = (loop_initial * m_times_vco_period)/loop_xplier;
    
            // convert loop ph_tap to delay
            rem = m_times_vco_period % loop_xplier;
            vco_per = m_times_vco_period/loop_xplier;
            if (rem != 0)
                vco_per = vco_per + 1;
            fbk_phase = (loop_ph * vco_per)/8;
    
            pull_back_M = initial_delay + fbk_phase;
    
            total_pull_back = pull_back_M;
            if (l_simulation_type == "timing")
                total_pull_back = total_pull_back + (pll_compensation_delay * 1000);
    
            while (total_pull_back > refclk_period)
                total_pull_back = total_pull_back - refclk_period;
    
            if (total_pull_back > 0)
                offset = refclk_period - total_pull_back;
            else
                offset = 0;
    
            fbk_delay = total_pull_back - fbk_phase;
            if (fbk_delay < 0)
            begin
                offset = offset - fbk_phase;
                fbk_delay = total_pull_back;
            end
    
            // assign m_delay
            m_delay = fbk_delay;
    
            for (i = 1; i <= loop_xplier; i=i+1)
            begin
                // adjust cycles
                tmp_vco_per = m_times_vco_period/loop_xplier;
                if (rem != 0 && l_index <= rem)
                begin
                    tmp_rem = (loop_xplier * l_index) % rem;
                    cycle_to_adjust = (loop_xplier * l_index) / rem;
                    if (tmp_rem != 0)
                        cycle_to_adjust = cycle_to_adjust + 1;
                end
                if (cycle_to_adjust == i)
                begin
                    tmp_vco_per = tmp_vco_per + 1;
                    l_index = l_index + 1;
                end
    
                // calculate high and low periods
                high_time = tmp_vco_per/2;
                if (tmp_vco_per % 2 != 0)
                    high_time = high_time + 1;
                low_time = tmp_vco_per - high_time;
    
                // schedule the rising and falling egdes
                for (j=0; j<=1; j=j+1)
                begin
                    vco_val = ~vco_val;
                    if (vco_val == 1'b0)
                        sched_time = sched_time + high_time;
                    else
                        sched_time = sched_time + low_time;
    
                    // schedule taps with appropriate phase shifts
                    for (k = 0; k <= 7; k=k+1)
                    begin
                        phase_shift[k] = (k*tmp_vco_per)/8;
                        if (first_schedule)
                            vco_out[k] <= #(sched_time + phase_shift[k]) vco_val;
                        else
                            vco_out[k] <= #(sched_time + last_phase_shift[k]) vco_val;
                    end
                end
            end
            if (first_schedule)
            begin
                vco_val = ~vco_val;
                if (vco_val == 1'b0)
                    sched_time = sched_time + high_time;
                else
                    sched_time = sched_time + low_time;
                for (k = 0; k <= 7; k=k+1)
                begin
                    phase_shift[k] = (k*tmp_vco_per)/8;
                    vco_out[k] <= #(sched_time+phase_shift[k]) vco_val;
                end
                first_schedule = 0;
            end

            schedule_vco <= #(sched_time) ~schedule_vco;
            if (vco_period_was_phase_adjusted)
            begin
                m_times_vco_period = refclk_period;
                new_m_times_vco_period = refclk_period;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 1;
    
                tmp_vco_per = m_times_vco_period/loop_xplier;
                for (k = 0; k <= 7; k=k+1)
                    phase_shift[k] = (k*tmp_vco_per)/8;
            end
        end
    
        areset_ipd_last_value = areset_ipd;
        schedule_vco_last_value = schedule_vco;
    
    end

    // PFD enable
    always @(pfdena_ipd)
    begin
        if (pfdena_ipd === 1'b0)
        begin
            if (pll_is_locked)
                locked_tmp = 1'bx;
            pll_is_locked = 0;
            cycles_to_lock = 0;
            $display (" Note : PFDENA was deasserted");
            $display ("Time: %0t  Instance: %m", $time);
        end
        else if (pfdena_ipd === 1'b1 && pfdena_ipd_last_value === 1'b0)
        begin
            // PFD was disabled, now enabled again
            got_first_refclk = 0;
            got_second_refclk = 0;
            refclk_time = $time;
        end
        pfdena_ipd_last_value = pfdena_ipd;
    end

    always @(negedge refclk or negedge fbclk)
    begin
        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    // Bypass lock detect
        
    always @(posedge refclk)
    begin
    if (test_bypass_lock_detect == "on")
        begin
            if (pfdena_ipd === 1'b1)
            begin
                    cycles_pfd_low = 0;
                    if (pfd_locked == 1'b0)
                    begin
                    if (cycles_pfd_high == lock_high)
                    begin
                        $display ("Note : %s PLL locked in test mode on PFD enable assert", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        pfd_locked <= 1'b1;
                    end
                    cycles_pfd_high = cycles_pfd_high + 1;
                        end
                end
            if (pfdena_ipd === 1'b0)
            begin
                    cycles_pfd_high = 0;
                    if (pfd_locked == 1'b1)
                    begin
                    if (cycles_pfd_low == lock_low)
                    begin
                        $display ("Note : %s PLL lost lock in test mode on PFD enable deassert", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        pfd_locked <= 1'b0;
                    end
                    cycles_pfd_low = cycles_pfd_low + 1;
                        end
                end
        end
    end
    
    always @(posedge scandone_tmp or posedge locked_tmp)
    begin
        if(scandone_tmp == 1)
            pll_has_just_been_reconfigured <= 1;
        else
            pll_has_just_been_reconfigured <= 0;
    end
    
    // VCO Frequency Range check
    always @(posedge refclk or posedge fbclk)
    begin
        if (refclk == 1'b1 && refclk_last_value !== refclk && areset_ipd === 1'b0)
        begin
            if (! got_first_refclk)
            begin
                got_first_refclk = 1;
            end else
            begin
                got_second_refclk = 1;
                refclk_period = $time - refclk_time;

                // check if incoming freq. will cause VCO range to be
                // exceeded
                if ((i_vco_max != 0 && i_vco_min != 0) && (pfdena_ipd === 1'b1) &&        
                    ((refclk_period/loop_xplier > i_vco_max) || 
                    (refclk_period/loop_xplier < i_vco_min)) ) 
                begin
                    if (pll_is_locked == 1'b1)
                    begin
                        if (refclk_period/loop_xplier > i_vco_max)
                        begin
                            $display ("Warning : Input clock freq. is over VCO range. %s PLL may lose lock", family_name);
                            vco_over = 1'b1;
                        end
                        if (refclk_period/loop_xplier < i_vco_min)
                        begin
                            $display ("Warning : Input clock freq. is under VCO range. %s PLL may lose lock", family_name);
                            vco_under = 1'b1;
                        end

                        $display ("Time: %0t  Instance: %m", $time);
                        if (inclk_out_of_range === 1'b1)
                        begin
                            // unlock
                            pll_is_locked = 0;
                            locked_tmp = 0;
                            cycles_to_lock = 0;
                            $display ("Note : %s PLL lost lock", family_name);
                            $display ("Time: %0t  Instance: %m", $time);
                            vco_period_was_phase_adjusted = 0;
                            phase_adjust_was_scheduled = 0;
                        end
                    end
                    else begin
                        if (no_warn == 1'b0)
                        begin
                            if (refclk_period/loop_xplier > i_vco_max)
                            begin
                                $display ("Warning : Input clock freq. is over VCO range. %s PLL may lose lock", family_name);
                                vco_over = 1'b1;
                            end
                            if (refclk_period/loop_xplier < i_vco_min)
                            begin
                                $display ("Warning : Input clock freq. is under VCO range. %s PLL may lose lock", family_name);
                                vco_under = 1'b1;
                            end
                            $display ("Time: %0t  Instance: %m", $time);
                            no_warn = 1'b1;
                        end
                    end
                    inclk_out_of_range = 1;
                end
                else begin
                    vco_over  = 1'b0;
                    vco_under = 1'b0;
                    inclk_out_of_range = 0;
                    no_warn = 1'b0;
                end

            end
            if (stop_vco == 1'b1)
            begin
                stop_vco = 0;
                schedule_vco = ~schedule_vco;
            end
            refclk_time = $time;
        end

        // Update M counter value on feedback clock edge
        
        if (fbclk == 1'b1 && fbclk_last_value !== fbclk)
        begin
            if (update_conf_latches === 1'b1)
            begin
                m_val[0] <= m_val_tmp[0];
                m_val[1] <= m_val_tmp[1];
            end
            if (!got_first_fbclk)
            begin
                got_first_fbclk = 1;
                first_fbclk_time = $time;
            end
            else
                fbclk_period = $time - fbclk_time;

            // need refclk_period here, so initialized to proper value above
            if ( ( ($time - refclk_time > 1.5 * refclk_period) && pfdena_ipd === 1'b1 && pll_is_locked === 1'b1) ||
                ( ($time - refclk_time > 5 * refclk_period) && (pfdena_ipd === 1'b1) && (pll_has_just_been_reconfigured == 0) ) ||
                ( ($time - refclk_time > 50 * refclk_period) && (pfdena_ipd === 1'b1) && (pll_has_just_been_reconfigured == 1) ) )
            begin
                stop_vco = 1;
                // reset
                got_first_refclk = 0;
                got_first_fbclk = 0;
                got_second_refclk = 0;
                if (pll_is_locked == 1'b1)
                begin
                    pll_is_locked = 0;
                    locked_tmp = 0;
                    $display ("Note : %s PLL lost lock due to loss of input clock or the input clock is not detected within the allowed time frame.", family_name);
                    if ((i_vco_max == 0) && (i_vco_min == 0))
                        $display ("Note : Please run timing simulation to check whether the input clock is operating within the supported VCO range or not.");
                    $display ("Time: %0t  Instance: %m", $time);
                end
                cycles_to_lock = 0;
                cycles_to_unlock = 0;
                first_schedule = 1;
                vco_period_was_phase_adjusted = 0;
                phase_adjust_was_scheduled = 0;
                tap0_is_active = 0;
                for (x = 0; x <= 7; x=x+1)
                    vco_tap[x] <= 1'b0;
            end
            fbclk_time = $time;
        end
        
                
        // Core lock functionality
        
        if (got_second_refclk && pfdena_ipd === 1'b1 && (!inclk_out_of_range))
        begin
            // now we know actual incoming period
            if (abs(fbclk_time - refclk_time) <= lock_window || (got_first_fbclk && abs(refclk_period - abs(fbclk_time - refclk_time)) <= lock_window))
            begin
                // considered in phase
                if (cycles_to_lock == real_lock_high)
                begin
                    if (pll_is_locked === 1'b0)
                    begin
                        $display (" Note : %s PLL locked to incoming clock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                    end
                    pll_is_locked = 1;
                    locked_tmp = 1;
                    cycles_to_unlock = 0;
                end
                // increment lock counter only if the second part of the above
                // time check is not true
                if (!(abs(refclk_period - abs(fbclk_time - refclk_time)) <= lock_window))
                begin
                    cycles_to_lock = cycles_to_lock + 1;
                end

                // adjust m_times_vco_period
                new_m_times_vco_period = refclk_period;

            end else
            begin
                // if locked, begin unlock
                if (pll_is_locked)
                begin
                    cycles_to_unlock = cycles_to_unlock + 1;
                    if (cycles_to_unlock == lock_low)
                    begin
                        pll_is_locked = 0;
                        locked_tmp = 0;
                        cycles_to_lock = 0;
                        $display ("Note : %s PLL lost lock", family_name);
                        $display ("Time: %0t  Instance: %m", $time);
                        vco_period_was_phase_adjusted = 0;
                        phase_adjust_was_scheduled = 0;
                        got_first_refclk = 0;
                        got_first_fbclk = 0;
                        got_second_refclk = 0;
                    end
                end
                if (abs(refclk_period - fbclk_period) <= 2000)
                begin
                    // frequency is still good
                    if ($time == fbclk_time && (!phase_adjust_was_scheduled))
                    begin
                        if (abs(fbclk_time - refclk_time) > refclk_period/2)
                        begin
                            new_m_times_vco_period = abs(m_times_vco_period + (refclk_period - abs(fbclk_time - refclk_time)));
                            vco_period_was_phase_adjusted = 1;
                        end else
                        begin
                            new_m_times_vco_period = abs(m_times_vco_period - abs(fbclk_time - refclk_time));
                            vco_period_was_phase_adjusted = 1;
                        end
                    end
                end else
                begin
                    new_m_times_vco_period = refclk_period;
                    phase_adjust_was_scheduled = 0;
                end
            end
        end

        if (reconfig_err == 1'b1)
        begin
            locked_tmp = 0;
        end

        refclk_last_value = refclk;
        fbclk_last_value = fbclk;
    end

    assign clk_tmp[0] = i_clk0_counter == "c0" ? c0_clk : i_clk0_counter == "c1" ? c1_clk : i_clk0_counter == "c2" ? c2_clk : i_clk0_counter == "c3" ? c3_clk : i_clk0_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[1] = i_clk1_counter == "c0" ? c0_clk : i_clk1_counter == "c1" ? c1_clk : i_clk1_counter == "c2" ? c2_clk : i_clk1_counter == "c3" ? c3_clk : i_clk1_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[2] = i_clk2_counter == "c0" ? c0_clk : i_clk2_counter == "c1" ? c1_clk : i_clk2_counter == "c2" ? c2_clk : i_clk2_counter == "c3" ? c3_clk : i_clk2_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[3] = i_clk3_counter == "c0" ? c0_clk : i_clk3_counter == "c1" ? c1_clk : i_clk3_counter == "c2" ? c2_clk : i_clk3_counter == "c3" ? c3_clk : i_clk3_counter == "c4" ? c4_clk : 1'b0;
    assign clk_tmp[4] = i_clk4_counter == "c0" ? c0_clk : i_clk4_counter == "c1" ? c1_clk : i_clk4_counter == "c2" ? c2_clk : i_clk4_counter == "c3" ? c3_clk : i_clk4_counter == "c4" ? c4_clk : 1'b0;

assign clk_out_pfd[0] = (pfd_locked == 1'b1) ? clk_tmp[0] : 1'bx;
assign clk_out_pfd[1] = (pfd_locked == 1'b1) ? clk_tmp[1] : 1'bx;
assign clk_out_pfd[2] = (pfd_locked == 1'b1) ? clk_tmp[2] : 1'bx;
assign clk_out_pfd[3] = (pfd_locked == 1'b1) ? clk_tmp[3] : 1'bx;
assign clk_out_pfd[4] = (pfd_locked == 1'b1) ? clk_tmp[4] : 1'bx;

    assign clk_out[0] = (test_bypass_lock_detect == "on") ? clk_out_pfd[0] : ((areset_ipd === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[0] : 1'bx);
    assign clk_out[1] = (test_bypass_lock_detect == "on") ? clk_out_pfd[1] : ((areset_ipd === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[1] : 1'bx);
    assign clk_out[2] = (test_bypass_lock_detect == "on") ? clk_out_pfd[2] : ((areset_ipd === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[2] : 1'bx);
    assign clk_out[3] = (test_bypass_lock_detect == "on") ? clk_out_pfd[3] : ((areset_ipd === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[3] : 1'bx);
    assign clk_out[4] = (test_bypass_lock_detect == "on") ? clk_out_pfd[4] : ((areset_ipd === 1'b1 || pll_in_test_mode === 1'b1) || (locked == 1'b1 && !reconfig_err) ? clk_tmp[4] : 1'bx);

    // ACCELERATE OUTPUTS
    and (clk[0], 1'b1, clk_out[0]);
    and (clk[1], 1'b1, clk_out[1]);
    and (clk[2], 1'b1, clk_out[2]);
    and (clk[3], 1'b1, clk_out[3]);
    and (clk[4], 1'b1, clk_out[4]);

    and (scandataout, 1'b1, scandata_out);
    and (scandone, 1'b1, scandone_tmp);

assign fbout = fbclk;
assign vcooverrange  = (vco_range_detector_high_bits == -1) ? 1'bz : vco_over;
assign vcounderrange = (vco_range_detector_low_bits == -1) ? 1'bz :vco_under;
assign phasedone = ~update_phase;
assign fref = refclk;
assign icdrclk = icdr_clk;

endmodule // MF_cycloneiiigl_pll

// START MODULE NAME -----------------------------------------------------------
//
// Module Name : ALTPLL
//
// Description : Phase-Locked Loop (PLL) behavioral model. Model supports basic
//               PLL features such as clock division and multiplication,
//               programmable duty cycle and phase shifts, various feedback modes
//               and clock delays. Also supports real-time reconfiguration of
//               PLL "parameters" and clock switchover between the 2 input
//               reference clocks. Up to 10 clock outputs may be used.
//
// Limitations : Applicable to Stratix, Stratix-GX, Stratix II and Cyclone II device families only
//               There is no support in the model for spread-spectrum feature
//
// Expected results : Up to 10 output clocks, each defined by its own set of
//                    parameters. Locked output (active high) indicates when the
//                    PLL locks. clkbad, clkloss and activeclock are used for
//                    clock switchover to inidicate which input clock has gone
//                    bad, when the clock switchover initiates and which input
//                    clock is being used as the reference, respectively.
//                    scandataout is the data output of the serial scan chain.

//END MODULE NAME --------------------------------------------------------------

`timescale 1 ps / 1ps
`define STR_LENGTH 18

// MODULE DECLARATION
module altpll (
    inclk,      // input reference clock - up to 2 can be used
    fbin,       // external feedback input port
    pllena,     // PLL enable signal
    clkswitch,  // switch between inclk0 and inclk1
    areset,     // asynchronous reset
    pfdena,     // enable the Phase Frequency Detector (PFD)
    clkena,     // enable clk0 to clk5 clock outputs
    extclkena,  // enable extclk0 to extclk3 clock outputs
    scanclk,    // clock for the serial scan chain
    scanaclr,   // asynchronous clear the serial scan chain
    scanclkena,
    scanread,   // determines when the scan chain can read in data from the scandata port
    scanwrite,  // determines when the scan chain can write out data into pll
    scandata,    // data for the scan chain
    phasecounterselect,
    phaseupdown,
    phasestep,
    configupdate,
    fbmimicbidir,
    clk,         // internal clock outputs (feeds the core)
    extclk,      // external clock outputs (feeds pins)
    clkbad,      // indicates if inclk0/inclk1 has gone bad
    enable0,     // load enable pulse 0 for lvds
    enable1,     // load enable pulse l for lvds
    activeclock, // indicates which input clock is being used
    clkloss,     // indicates when clock switchover initiates
    locked,      // indicates when the PLL locks onto the input clock
    scandataout, // data output of the serial scan chain
    scandone,    // indicates when pll reconfiguration is complete
    sclkout0,    // serial clock output 0 for lvds
    sclkout1,     // serial clock output 1 for lvds
    phasedone,
    vcooverrange,
    vcounderrange,
    fbout,
    fref,
    icdrclk
);

// GLOBAL PARAMETER DECLARATION
parameter   intended_device_family    = "Stratix" ;
parameter   operation_mode            = "NORMAL" ;
parameter   pll_type                  = "AUTO" ;
parameter   qualify_conf_done         = "OFF" ;
parameter   compensate_clock          = "CLK0" ;
parameter   scan_chain                = "LONG";
parameter   primary_clock             = "inclk0";
parameter   inclk0_input_frequency    = 1000;
parameter   inclk1_input_frequency    = 0;
parameter   gate_lock_signal          = "NO";
parameter   gate_lock_counter         = 0;
parameter   lock_high                 = 1;
parameter   lock_low                  = 0;
parameter   valid_lock_multiplier     = 1;
parameter   invalid_lock_multiplier   = 5;
parameter   switch_over_type          = "AUTO";
parameter   switch_over_on_lossclk    = "OFF" ;
parameter   switch_over_on_gated_lock = "OFF" ;
parameter   enable_switch_over_counter = "OFF";
parameter   switch_over_counter       = 0;
parameter   feedback_source           = "EXTCLK0" ;
parameter   bandwidth                 = 0;
parameter   bandwidth_type            = "UNUSED";
parameter   lpm_hint                  = "UNUSED";
parameter   spread_frequency          = 0;
parameter   down_spread               = "0.0";
parameter   self_reset_on_gated_loss_lock = "OFF";
parameter   self_reset_on_loss_lock = "OFF";
parameter   lock_window_ui           = "0.05";
parameter   width_clock              = 6;
parameter   width_phasecounterselect = 4;
parameter charge_pump_current_bits = 9999;
parameter loop_filter_c_bits = 9999;
parameter loop_filter_r_bits = 9999;
parameter scan_chain_mif_file = "UNUSED";

// SIMULATION_ONLY_PARAMETERS_BEGIN

parameter   simulation_type           = "functional";
parameter   source_is_pll             = "off";

// SIMULATION_ONLY_PARAMETERS_END

parameter   skip_vco                    = "off";

//  internal clock specifications
parameter   clk9_multiply_by        = 1;
parameter   clk8_multiply_by        = 1;
parameter   clk7_multiply_by        = 1;
parameter   clk6_multiply_by        = 1;
parameter   clk5_multiply_by        = 1;
parameter   clk4_multiply_by        = 1;
parameter   clk3_multiply_by        = 1;
parameter   clk2_multiply_by        = 1;
parameter   clk1_multiply_by        = 1;
parameter   clk0_multiply_by        = 1;
parameter   clk9_divide_by          = 1;
parameter   clk8_divide_by          = 1;
parameter   clk7_divide_by          = 1;
parameter   clk6_divide_by          = 1;
parameter   clk5_divide_by          = 1;
parameter   clk4_divide_by          = 1;
parameter   clk3_divide_by          = 1;
parameter   clk2_divide_by          = 1;
parameter   clk1_divide_by          = 1;
parameter   clk0_divide_by          = 1;
parameter   clk9_phase_shift        = "0";
parameter   clk8_phase_shift        = "0";
parameter   clk7_phase_shift        = "0";
parameter   clk6_phase_shift        = "0";
parameter   clk5_phase_shift        = "0";
parameter   clk4_phase_shift        = "0";
parameter   clk3_phase_shift        = "0";
parameter   clk2_phase_shift        = "0";
parameter   clk1_phase_shift        = "0";
parameter   clk0_phase_shift        = "0";

parameter   clk5_time_delay         = "0";  // For stratix pll use only
parameter   clk4_time_delay         = "0";  // For stratix pll use only
parameter   clk3_time_delay         = "0";  // For stratix pll use only
parameter   clk2_time_delay         = "0";  // For stratix pll use only
parameter   clk1_time_delay         = "0";  // For stratix pll use only
parameter   clk0_time_delay         = "0";  // For stratix pll use only
parameter   clk9_duty_cycle         = 50;
parameter   clk8_duty_cycle         = 50;
parameter   clk7_duty_cycle         = 50;
parameter   clk6_duty_cycle         = 50;
parameter   clk5_duty_cycle         = 50;
parameter   clk4_duty_cycle         = 50;
parameter   clk3_duty_cycle         = 50;
parameter   clk2_duty_cycle         = 50;
parameter   clk1_duty_cycle         = 50;
parameter   clk0_duty_cycle         = 50;

parameter   clk9_use_even_counter_mode    = "OFF";
parameter   clk8_use_even_counter_mode    = "OFF";
parameter   clk7_use_even_counter_mode    = "OFF";
parameter   clk6_use_even_counter_mode    = "OFF";
parameter   clk5_use_even_counter_mode    = "OFF";
parameter   clk4_use_even_counter_mode    = "OFF";
parameter   clk3_use_even_counter_mode    = "OFF";
parameter   clk2_use_even_counter_mode    = "OFF";
parameter   clk1_use_even_counter_mode    = "OFF";
parameter   clk0_use_even_counter_mode    = "OFF";
parameter   clk9_use_even_counter_value   = "OFF";
parameter   clk8_use_even_counter_value   = "OFF";
parameter   clk7_use_even_counter_value   = "OFF";
parameter   clk6_use_even_counter_value   = "OFF";
parameter   clk5_use_even_counter_value   = "OFF";
parameter   clk4_use_even_counter_value   = "OFF";
parameter   clk3_use_even_counter_value   = "OFF";
parameter   clk2_use_even_counter_value   = "OFF";
parameter   clk1_use_even_counter_value   = "OFF";
parameter   clk0_use_even_counter_value   = "OFF";

parameter   clk2_output_frequency   = 0;
parameter   clk1_output_frequency   = 0;
parameter   clk0_output_frequency   = 0;

//  external clock specifications (for stratix pll use only)
parameter   extclk3_multiply_by     = 1;
parameter   extclk2_multiply_by     = 1;
parameter   extclk1_multiply_by     = 1;
parameter   extclk0_multiply_by     = 1;
parameter   extclk3_divide_by       = 1;
parameter   extclk2_divide_by       = 1;
parameter   extclk1_divide_by       = 1;
parameter   extclk0_divide_by       = 1;
parameter   extclk3_phase_shift     = "0";
parameter   extclk2_phase_shift     = "0";
parameter   extclk1_phase_shift     = "0";
parameter   extclk0_phase_shift     = "0";
parameter   extclk3_time_delay      = "0";
parameter   extclk2_time_delay      = "0";
parameter   extclk1_time_delay      = "0";
parameter   extclk0_time_delay      = "0";
parameter   extclk3_duty_cycle      = 50;
parameter   extclk2_duty_cycle      = 50;
parameter   extclk1_duty_cycle      = 50;
parameter   extclk0_duty_cycle      = 50;

// The following 4 parameters are for Stratix II pll in lvds mode only 
parameter vco_multiply_by = 0;
parameter vco_divide_by = 0;
parameter sclkout0_phase_shift = "0";
parameter sclkout1_phase_shift = "0";

parameter dpa_multiply_by = 0;
parameter dpa_divide_by = 0;
parameter dpa_divider = 0;

//  advanced user parameters
parameter   vco_min             = 0;
parameter   vco_max             = 0;
parameter   vco_center          = 0;
parameter   pfd_min             = 0;
parameter   pfd_max             = 0;
parameter   m_initial           = 1;
parameter   m                   = 0; // m must default to 0 in order for altpll to calculate advanced parameters for itself
parameter   n                   = 1;
parameter   m2                  = 1;
parameter   n2                  = 1;
parameter   ss                  = 0;
parameter   l0_high             = 1;
parameter   l1_high             = 1;
parameter   g0_high             = 1;
parameter   g1_high             = 1;
parameter   g2_high             = 1;
parameter   g3_high             = 1;
parameter   e0_high             = 1;
parameter   e1_high             = 1;
parameter   e2_high             = 1;
parameter   e3_high             = 1;
parameter   l0_low              = 1;
parameter   l1_low              = 1;
parameter   g0_low              = 1;
parameter   g1_low              = 1;
parameter   g2_low              = 1;
parameter   g3_low              = 1;
parameter   e0_low              = 1;
parameter   e1_low              = 1;
parameter   e2_low              = 1;
parameter   e3_low              = 1;
parameter   l0_initial          = 1;
parameter   l1_initial          = 1;
parameter   g0_initial          = 1;
parameter   g1_initial          = 1;
parameter   g2_initial          = 1;
parameter   g3_initial          = 1;
parameter   e0_initial          = 1;
parameter   e1_initial          = 1;
parameter   e2_initial          = 1;
parameter   e3_initial          = 1;
parameter   l0_mode             = "bypass";
parameter   l1_mode             = "bypass";
parameter   g0_mode             = "bypass";
parameter   g1_mode             = "bypass";
parameter   g2_mode             = "bypass";
parameter   g3_mode             = "bypass";
parameter   e0_mode             = "bypass";
parameter   e1_mode             = "bypass";
parameter   e2_mode             = "bypass";
parameter   e3_mode             = "bypass";
parameter   l0_ph               = 0;
parameter   l1_ph               = 0;
parameter   g0_ph               = 0;
parameter   g1_ph               = 0;
parameter   g2_ph               = 0;
parameter   g3_ph               = 0;
parameter   e0_ph               = 0;
parameter   e1_ph               = 0;
parameter   e2_ph               = 0;
parameter   e3_ph               = 0;
parameter   m_ph                = 0;
parameter   l0_time_delay       = 0;
parameter   l1_time_delay       = 0;
parameter   g0_time_delay       = 0;
parameter   g1_time_delay       = 0;
parameter   g2_time_delay       = 0;
parameter   g3_time_delay       = 0;
parameter   e0_time_delay       = 0;
parameter   e1_time_delay       = 0;
parameter   e2_time_delay       = 0;
parameter   e3_time_delay       = 0;
parameter   m_time_delay        = 0;
parameter   n_time_delay        = 0;
parameter   extclk3_counter     = "e3" ;
parameter   extclk2_counter     = "e2" ;
parameter   extclk1_counter     = "e1" ;
parameter   extclk0_counter     = "e0" ;
parameter   clk9_counter        = "c9" ;
parameter   clk8_counter        = "c8" ;
parameter   clk7_counter        = "c7" ;
parameter   clk6_counter        = "c6" ;
parameter   clk5_counter        = "l1" ;
parameter   clk4_counter        = "l0" ;
parameter   clk3_counter        = "g3" ;
parameter   clk2_counter        = "g2" ;
parameter   clk1_counter        = "g1" ;
parameter   clk0_counter        = "g0" ;
parameter   enable0_counter     = "l0";
parameter   enable1_counter     = "l0";
parameter   charge_pump_current = 2;
parameter   loop_filter_r       = "1.0";
parameter   loop_filter_c       = 5;
parameter   vco_post_scale      = 0;
parameter   vco_frequency_control = "AUTO";
parameter   vco_phase_shift_step = 0;
parameter   lpm_type            = "altpll";

// The following parameter are used to define the connectivity for some of the input
// and output ports.
parameter port_clkena0 = "PORT_CONNECTIVITY";
parameter port_clkena1 = "PORT_CONNECTIVITY";
parameter port_clkena2 = "PORT_CONNECTIVITY";
parameter port_clkena3 = "PORT_CONNECTIVITY";
parameter port_clkena4 = "PORT_CONNECTIVITY";
parameter port_clkena5 = "PORT_CONNECTIVITY";
parameter port_extclkena0 = "PORT_CONNECTIVITY";
parameter port_extclkena1 = "PORT_CONNECTIVITY";
parameter port_extclkena2 = "PORT_CONNECTIVITY";
parameter port_extclkena3 = "PORT_CONNECTIVITY";
parameter port_extclk0 = "PORT_CONNECTIVITY";
parameter port_extclk1 = "PORT_CONNECTIVITY";
parameter port_extclk2 = "PORT_CONNECTIVITY";
parameter port_extclk3 = "PORT_CONNECTIVITY";
parameter port_clk0 = "PORT_CONNECTIVITY";
parameter port_clk1 = "PORT_CONNECTIVITY";
parameter port_clk2 = "PORT_CONNECTIVITY";
parameter port_clk3 = "PORT_CONNECTIVITY";
parameter port_clk4 = "PORT_CONNECTIVITY";
parameter port_clk5 = "PORT_CONNECTIVITY";
parameter port_clk6 = "PORT_CONNECTIVITY";
parameter port_clk7 = "PORT_CONNECTIVITY";
parameter port_clk8 = "PORT_CONNECTIVITY";
parameter port_clk9 = "PORT_CONNECTIVITY";
parameter port_scandata = "PORT_CONNECTIVITY";
parameter port_scandataout = "PORT_CONNECTIVITY";
parameter port_scandone = "PORT_CONNECTIVITY";
parameter port_sclkout1 = "PORT_CONNECTIVITY";
parameter port_sclkout0 = "PORT_CONNECTIVITY";
parameter port_clkbad0 = "PORT_CONNECTIVITY";
parameter port_clkbad1 = "PORT_CONNECTIVITY";
parameter port_activeclock = "PORT_CONNECTIVITY";
parameter port_clkloss = "PORT_CONNECTIVITY";
parameter port_inclk1 = "PORT_CONNECTIVITY";
parameter port_inclk0 = "PORT_CONNECTIVITY";
parameter port_fbin = "PORT_CONNECTIVITY";
parameter port_fbout = "PORT_CONNECTIVITY";
parameter port_pllena = "PORT_CONNECTIVITY";
parameter port_clkswitch = "PORT_CONNECTIVITY";
parameter port_areset = "PORT_CONNECTIVITY";
parameter port_pfdena = "PORT_CONNECTIVITY";
parameter port_scanclk = "PORT_CONNECTIVITY";
parameter port_scanaclr = "PORT_CONNECTIVITY";
parameter port_scanread = "PORT_CONNECTIVITY";
parameter port_scanwrite = "PORT_CONNECTIVITY";
parameter port_enable0 = "PORT_CONNECTIVITY";
parameter port_enable1 = "PORT_CONNECTIVITY";
parameter port_locked = "PORT_CONNECTIVITY";
parameter port_configupdate = "PORT_CONNECTIVITY";
parameter port_phasecounterselect = "PORT_CONNECTIVITY";
parameter port_phasedone = "PORT_CONNECTIVITY";
parameter port_phasestep = "PORT_CONNECTIVITY";
parameter port_phaseupdown = "PORT_CONNECTIVITY";
parameter port_vcooverrange = "PORT_CONNECTIVITY";
parameter port_vcounderrange = "PORT_CONNECTIVITY";
parameter port_scanclkena = "PORT_CONNECTIVITY";
parameter using_fbmimicbidir_port = "ON";

//For Stratixii pll use only
parameter   c0_high             = 1;
parameter   c1_high             = 1;
parameter   c2_high             = 1;
parameter   c3_high             = 1;
parameter   c4_high             = 1;
parameter   c5_high             = 1;
parameter   c6_high             = 1;
parameter   c7_high             = 1;
parameter   c8_high             = 1;
parameter   c9_high             = 1;
parameter   c0_low              = 1;
parameter   c1_low              = 1;
parameter   c2_low              = 1;
parameter   c3_low              = 1;
parameter   c4_low              = 1;
parameter   c5_low              = 1;
parameter   c6_low              = 1;
parameter   c7_low              = 1;
parameter   c8_low              = 1;
parameter   c9_low              = 1;
parameter   c0_initial          = 1;
parameter   c1_initial          = 1;
parameter   c2_initial          = 1;
parameter   c3_initial          = 1;
parameter   c4_initial          = 1;
parameter   c5_initial          = 1;
parameter   c6_initial          = 1;
parameter   c7_initial          = 1;
parameter   c8_initial          = 1;
parameter   c9_initial          = 1;
parameter   c0_mode             = "bypass";
parameter   c1_mode             = "bypass";
parameter   c2_mode             = "bypass";
parameter   c3_mode             = "bypass";
parameter   c4_mode             = "bypass";
parameter   c5_mode             = "bypass";
parameter   c6_mode             = "bypass";
parameter   c7_mode             = "bypass";
parameter   c8_mode             = "bypass";
parameter   c9_mode             = "bypass";
parameter   c0_ph               = 0;
parameter   c1_ph               = 0;
parameter   c2_ph               = 0;
parameter   c3_ph               = 0;
parameter   c4_ph               = 0;
parameter   c5_ph               = 0;
parameter   c6_ph               = 0;
parameter   c7_ph               = 0;
parameter   c8_ph               = 0;
parameter   c9_ph               = 0;
parameter   c1_use_casc_in      = "off";
parameter   c2_use_casc_in      = "off";
parameter   c3_use_casc_in      = "off";
parameter   c4_use_casc_in      = "off";
parameter   c5_use_casc_in      = "off";
parameter   c6_use_casc_in      = "off";
parameter   c7_use_casc_in      = "off";
parameter   c8_use_casc_in      = "off";
parameter   c9_use_casc_in      = "off";
parameter   m_test_source       = 5;
parameter   c0_test_source      = 5;
parameter   c1_test_source      = 5;
parameter   c2_test_source      = 5;
parameter   c3_test_source      = 5;
parameter   c4_test_source      = 5;
parameter   c5_test_source      = 5;
parameter   c6_test_source      = 5;
parameter   c7_test_source      = 5;
parameter   c8_test_source      = 5;
parameter   c9_test_source      = 5;
parameter   sim_gate_lock_device_behavior = "OFF";

// INPUT PORT DECLARATION
input       [1:0] inclk;
input       fbin;
input       pllena;
input       clkswitch;
input       areset;
input       pfdena;
input       [5:0] clkena;
input       [3:0] extclkena;
input       scanclk;
input       scanclkena;
input       scanaclr;
input       scanread;
input       scanwrite;
input       scandata;
input       [width_phasecounterselect-1:0] phasecounterselect;
input       phaseupdown;
input       phasestep;
input       configupdate;

// INOUT PORT DECLARATION
inout fbmimicbidir;

// OUTPUT PORT DECLARATION
output        [width_clock-1:0] clk;
output        [3:0] extclk;
output        [1:0] clkbad;
output        activeclock;
output        enable0;
output        enable1;
output        clkloss;
output        locked;
output        scandataout;
output        scandone;
output        sclkout0;
output        sclkout1;
output        phasedone;
output        vcooverrange;
output        vcounderrange;
output        fbout;
output        fref;
output        icdrclk;

// pullups
tri1 ena_pullup;
tri1 pfdena_pullup;
tri1 [5:0] clkena_pullup;
tri1 [3:0] extclkena_pullup;
tri1 scanclkena_pullup;

// pulldowns
tri0 fbin_pulldown;
tri0 [1:0] inclk_pulldown;
tri0 clkswitch_pulldown;
tri0 areset_pulldown;
tri0 scanclk_pulldown;
tri0 scanclr_pulldown;
tri0 scanread_pulldown;
tri0 scanwrite_pulldown;
tri0 scandata_pulldown;
tri0 comparator_pulldown;
tri0 configupdate_pulldown;
tri0 [3:0] phasecounterselect_pulldown;
tri0 phaseupdown_pulldown;
tri0 phasestep_pulldown;

// For fast mode, the stratix pll atom model will give active low signal on locked output.
// Therefore, need to invert the lock signal for fast mode as in user view, locked signal is
// always active high.
wire locked_tmp;
wire pll_lock;
wire [1:0] stratix_inclk;
wire stratix_fbin;
wire stratix_ena;
wire stratix_clkswitch;
wire stratix_areset;
wire stratix_pfdena;
wire [5:0] stratix_clkena;
wire [3:0] stratix_extclkena;
wire stratix_scanclk;
wire stratix_scanclr;
wire stratix_scandata;
wire [5:0] stratix_clk;
wire [3:0] stratix_extclk;
wire [1:0] stratix_clkbad;
wire stratix_activeclock;
wire stratix_locked;
wire stratix_clkloss;
wire stratix_scandataout;
wire stratix_enable0;
wire stratix_enable1;

wire [1:0] stratixii_inclk;
wire stratixii_fbin;
wire stratixii_ena;
wire stratixii_clkswitch;
wire stratixii_areset;
wire stratixii_pfdena;
wire stratixii_scanread;
wire stratixii_scanwrite;
wire stratixii_scanclk;
wire stratixii_scandata;
wire stratixii_scandone;
wire [5:0] stratixii_clk;
wire [1:0] stratixii_clkbad;
wire stratixii_activeclock;
wire stratixii_locked;
wire stratixii_clkloss;
wire stratixii_scandataout;
wire stratixii_enable0;
wire stratixii_enable1;
wire stratixii_sclkout0;
wire stratixii_sclkout1;
wire [1:0] stratix3_inclk;
wire stratix3_clkswitch;
wire stratix3_areset;
wire stratix3_pfdena;
wire stratix3_scanclk;
wire [9:0] stratix3_clk;
wire [1:0] stratix3_clkbad;
wire stratix3_activeclock;
wire stratix3_locked;
wire stratix3_scandataout;
wire stratix3_scandone;
wire stratix3_phasedone;
wire stratix3_vcooverrange;
wire stratix3_vcounderrange;
wire stratix3_fbin;
wire stratix3_fbout;
wire [3:0] stratix3_phasecounterselect;

wire [1:0] cyclone3_inclk;
wire cyclone3_clkswitch;
wire cyclone3_areset;
wire cyclone3_pfdena;
wire cyclone3_scanclk;
wire [4:0] cyclone3_clk;
wire [1:0] cyclone3_clkbad;
wire cyclone3_activeclock;
wire cyclone3_locked;
wire cyclone3_scandataout;
wire cyclone3_scandone;
wire cyclone3_phasedone;
wire cyclone3_vcooverrange;
wire cyclone3_vcounderrange;
wire cyclone3_fbout;
wire [2:0] cyclone3_phasecounterselect;

wire [1:0] cyclone3gl_inclk;
wire cyclone3gl_clkswitch;
wire cyclone3gl_areset;
wire cyclone3gl_pfdena;
wire cyclone3gl_scanclk;
wire [4:0] cyclone3gl_clk;
wire [1:0] cyclone3gl_clkbad;
wire cyclone3gl_activeclock;
wire cyclone3gl_locked;
wire cyclone3gl_scandataout;
wire cyclone3gl_scandone;
wire cyclone3gl_phasedone;
wire cyclone3gl_vcooverrange;
wire cyclone3gl_vcounderrange;
wire cyclone3gl_fbout;
wire [2:0] cyclone3gl_phasecounterselect;
wire cyclone3gl_fref;
wire cyclone3gl_icdrclk;
wire[9:0] clk_wire;
wire[9:0] clk_tmp;
wire[1:0] clkbad_wire;
wire activeclock_wire;
wire clkloss_wire;
wire scandataout_wire;
wire scandone_wire;
wire sclkout0_wire;
wire sclkout1_wire;
wire locked_wire;
wire phasedone_wire;
wire vcooverrange_wire;
wire vcounderrange_wire;
wire fbout_wire;
wire iobuf_io;
wire iobuf_o;

reg pll_lock_sync;

reg family_stratixiii;
reg family_cycloneiii;
reg family_cycloneiiigl;
reg family_base_cycloneii;
reg family_arriaii;
reg family_has_stratix_style_pll;
reg family_has_stratixii_style_pll;

ALTERA_DEVICE_FAMILIES dev ();

// FUNCTION DECLARATION

// convert uppercase parameter values to lowercase
// assumes that the maximum character length of a parameter is 18
function [8*`STR_LENGTH:1] alpha_tolower;
input [8*`STR_LENGTH:1] given_string;

reg [8*`STR_LENGTH:1] return_string;
reg [8*`STR_LENGTH:1] reg_string;
reg [8:1] tmp;
reg [8:1] conv_char;
integer byte_count;
begin
    return_string = "                    "; // initialise strings to spaces
    conv_char = "        ";
    reg_string = given_string;
    for (byte_count = `STR_LENGTH; byte_count >= 1; byte_count = byte_count - 1)
    begin
        tmp = reg_string[8*`STR_LENGTH:(8*(`STR_LENGTH-1)+1)];
        reg_string = reg_string << 8;
        if ((tmp >= 65) && (tmp <= 90)) // ASCII number of 'A' is 65, 'Z' is 90
        begin
            conv_char = tmp + 32; // 32 is the difference in the position of 'A' and 'a' in the ASCII char set
            return_string = {return_string, conv_char};
        end
        else
            return_string = {return_string, tmp};
    end

    alpha_tolower = return_string;
end
endfunction

// INITIAL BLOCK
initial
begin

    // Begin of parameter checking

    if (clk5_multiply_by <= 0)
    begin
        $display("ERROR: The clk5_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (clk4_multiply_by <= 0)
    begin
        $display("ERROR: The clk4_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (clk3_multiply_by <= 0)
    begin
        $display("ERROR: The clk3_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (clk2_multiply_by <= 0)
    begin
        $display("ERROR: The clk2_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (clk1_multiply_by <= 0)
    begin
        $display("ERROR: The clk1_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (clk0_multiply_by <= 0)
    begin
        $display("ERROR: The clk0_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (clk5_divide_by <= 0)
    begin
        $display("ERROR: The clk5_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (clk4_divide_by <= 0)
    begin
        $display("ERROR: The clk4_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (clk3_divide_by <= 0)
    begin
        $display("ERROR: The clk3_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (clk2_divide_by <= 0)
    begin
        $display("ERROR: The clk2_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (clk1_divide_by <= 0)
    begin
        $display("ERROR: The clk1_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (clk0_divide_by <= 0)
    begin
        $display("ERROR: The clk0_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (extclk3_multiply_by <= 0)
    begin
        $display("ERROR: The extclk3_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (extclk2_multiply_by <= 0)
    begin
        $display("ERROR: The extclk2_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (extclk1_multiply_by <= 0)
    begin
        $display("ERROR: The extclk1_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (extclk0_multiply_by <= 0)
    begin
        $display("ERROR: The extclk0_multiply_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (extclk3_divide_by <= 0)
    begin
        $display("ERROR: The extclk3_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (extclk2_divide_by <= 0)
    begin
        $display("ERROR: The extclk2_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (extclk1_divide_by <= 0)
    begin
        $display("ERROR: The extclk1_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end


    if (extclk0_divide_by <= 0)
    begin
        $display("ERROR: The extclk0_divide_by must be greater than 0");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (!((primary_clock == "inclk0") || (primary_clock == "INCLK0") || 
        (primary_clock == "inclk1") || (primary_clock == "INCLK1"))) 
    begin
        $display("ERROR: The primary clock is set to an illegal value");
        $display("Time: %0t  Instance: %m", $time);
        $stop;
    end

    if (dev.IS_VALID_FAMILY(intended_device_family) == 0)
    begin
        $display ("Error! Unknown INTENDED_DEVICE_FAMILY=%s.", intended_device_family);
        $stop;
    end
    
    family_stratixiii = dev.FEATURE_FAMILY_STRATIXIII(intended_device_family);
    family_cycloneiiigl = dev.FEATURE_FAMILY_CYCLONEIVGX(intended_device_family);
    family_cycloneiii = !family_cycloneiiigl && dev.FEATURE_FAMILY_CYCLONEIII(intended_device_family);
    family_base_cycloneii = dev.FEATURE_FAMILY_BASE_CYCLONEII(intended_device_family);
    family_arriaii = dev.FEATURE_FAMILY_ARRIAIIGX(intended_device_family);
    family_has_stratix_style_pll = dev.FEATURE_FAMILY_HAS_STRATIX_STYLE_PLL(intended_device_family);
    family_has_stratixii_style_pll = dev.FEATURE_FAMILY_HAS_STRATIXII_STYLE_PLL(intended_device_family);

    if((family_arriaii) && (operation_mode == "external_feedback"))
    begin
        $display ("ERROR: The external feedback mode is not supported for the ARRIA II family.");
        $stop;
    end
    
    if((family_arriaii) && ((pll_type == "top_bottom") || (pll_type == "left_right")))
    begin
        $display ("WARNING: A pll_type specification is not supported for the ARRIA II family.  It will be ignored.");
        $display ("Time: %0t  Instance: %m", $time);
    end
    
    if((family_arriaii) && ((port_clk7 != "PORT_UNUSED") || (port_clk8 != "PORT_UNUSED") || (port_clk9 != "PORT_UNUSED")))
    begin
        $display ("ERROR: One or more clock outputs used in the design are not supported in ARRIA II family.");
        $stop;
    end
    
    // End of parameter checking

    pll_lock_sync = 1'b1;

end

// COMPONENT INSTANTIATION
MF_stratix_pll pll0
(
    .inclk (stratix_inclk),
    .fbin (stratix_fbin),
    .ena (stratix_ena),
    .clkswitch (stratix_clkswitch),
    .areset (stratix_areset),
    .pfdena (stratix_pfdena),
    .clkena (stratix_clkena),
    .extclkena (stratix_extclkena),
    .scanclk (stratix_scanclk),
    .scanaclr (stratix_scanclr),
    .scandata (stratix_scandata),
    .comparator(),
    .clk (stratix_clk),
    .extclk (stratix_extclk),
    .clkbad (stratix_clkbad),
    .activeclock (stratix_activeclock),
    .locked (locked_tmp),
    .clkloss (stratix_clkloss),
    .scandataout (stratix_scandataout),
    .enable0 (stratix_enable0),
    .enable1 (stratix_enable1)
);
    defparam
        pll0.operation_mode         = operation_mode,
        pll0.pll_type               = pll_type,
        pll0.qualify_conf_done      = qualify_conf_done,
        pll0.compensate_clock       = compensate_clock,
        pll0.scan_chain             = scan_chain,
        pll0.primary_clock          = primary_clock,
        pll0.inclk0_input_frequency = inclk0_input_frequency,
        pll0.inclk1_input_frequency = inclk1_input_frequency,
        pll0.gate_lock_signal       = gate_lock_signal,
        pll0.gate_lock_counter      = gate_lock_counter,
        pll0.valid_lock_multiplier  = valid_lock_multiplier,
        pll0.invalid_lock_multiplier = invalid_lock_multiplier,
        pll0.switch_over_on_lossclk = switch_over_on_lossclk,
        pll0.switch_over_on_gated_lock = switch_over_on_gated_lock,
        pll0.enable_switch_over_counter = enable_switch_over_counter,
        pll0.switch_over_counter    = switch_over_counter,
        pll0.feedback_source        = feedback_source,
        pll0.bandwidth              = bandwidth,
        pll0.bandwidth_type         = bandwidth_type,
        pll0.spread_frequency       = spread_frequency,
        pll0.down_spread            = down_spread,
        pll0.simulation_type        = simulation_type,
        pll0.skip_vco               = skip_vco,
        pll0.family_name            = intended_device_family,

        //  internal clock specifications
        pll0.clk5_multiply_by       = clk5_multiply_by,
        pll0.clk4_multiply_by       = clk4_multiply_by,
        pll0.clk3_multiply_by       = clk3_multiply_by,
        pll0.clk2_multiply_by       = clk2_multiply_by,
        pll0.clk1_multiply_by       = clk1_multiply_by,
        pll0.clk0_multiply_by       = clk0_multiply_by,
        pll0.clk5_divide_by         = clk5_divide_by,
        pll0.clk4_divide_by         = clk4_divide_by,
        pll0.clk3_divide_by         = clk3_divide_by,
        pll0.clk2_divide_by         = clk2_divide_by,
        pll0.clk1_divide_by         = clk1_divide_by,
        pll0.clk0_divide_by         = clk0_divide_by,
        pll0.clk5_phase_shift       = clk5_phase_shift,
        pll0.clk4_phase_shift       = clk4_phase_shift,
        pll0.clk3_phase_shift       = clk3_phase_shift,
        pll0.clk2_phase_shift       = clk2_phase_shift,
        pll0.clk1_phase_shift       = clk1_phase_shift,
        pll0.clk0_phase_shift       = clk0_phase_shift,
        pll0.clk5_time_delay        = clk5_time_delay,
        pll0.clk4_time_delay        = clk4_time_delay,
        pll0.clk3_time_delay        = clk3_time_delay,
        pll0.clk2_time_delay        = clk2_time_delay,
        pll0.clk1_time_delay        = clk1_time_delay,
        pll0.clk0_time_delay        = clk0_time_delay,
        pll0.clk5_duty_cycle        = clk5_duty_cycle,
        pll0.clk4_duty_cycle        = clk4_duty_cycle,
        pll0.clk3_duty_cycle        = clk3_duty_cycle,
        pll0.clk2_duty_cycle        = clk2_duty_cycle,
        pll0.clk1_duty_cycle        = clk1_duty_cycle,
        pll0.clk0_duty_cycle        = clk0_duty_cycle,

        //  external clock specifications
        pll0.extclk3_multiply_by    = extclk3_multiply_by,
        pll0.extclk2_multiply_by    = extclk2_multiply_by,
        pll0.extclk1_multiply_by    = extclk1_multiply_by,
        pll0.extclk0_multiply_by    = extclk0_multiply_by,
        pll0.extclk3_divide_by      = extclk3_divide_by,
        pll0.extclk2_divide_by      = extclk2_divide_by,
        pll0.extclk1_divide_by      = extclk1_divide_by,
        pll0.extclk0_divide_by      = extclk0_divide_by,
        pll0.extclk3_phase_shift    = extclk3_phase_shift,
        pll0.extclk2_phase_shift    = extclk2_phase_shift,
        pll0.extclk1_phase_shift    = extclk1_phase_shift,
        pll0.extclk0_phase_shift    = extclk0_phase_shift,
        pll0.extclk3_time_delay     = extclk3_time_delay,
        pll0.extclk2_time_delay     = extclk2_time_delay,
        pll0.extclk1_time_delay     = extclk1_time_delay,
        pll0.extclk0_time_delay     = extclk0_time_delay,
        pll0.extclk3_duty_cycle     = extclk3_duty_cycle,
        pll0.extclk2_duty_cycle     = extclk2_duty_cycle,
        pll0.extclk1_duty_cycle     = extclk1_duty_cycle,
        pll0.extclk0_duty_cycle     = extclk0_duty_cycle,

        // advanced parameters
        pll0.vco_min                = (vco_min == 0 && m != 0)? 1000 : vco_min,
        pll0.vco_max                = (vco_max == 0 && m != 0)? 3600 : vco_max,
        pll0.vco_center             = vco_center,
        pll0.pfd_min                = pfd_min,
        pll0.pfd_max                = pfd_max,
        pll0.m_initial              = m_initial,
        pll0.m                      = m,
        pll0.n                      = n,
        pll0.m2                     = m2,
        pll0.n2                     = n2,
        pll0.ss                     = ss,
        pll0.l0_high                = l0_high,
        pll0.l1_high                = l1_high,
        pll0.g0_high                = g0_high,
        pll0.g1_high                = g1_high,
        pll0.g2_high                = g2_high,
        pll0.g3_high                = g3_high,
        pll0.e0_high                = e0_high,
        pll0.e1_high                = e1_high,
        pll0.e2_high                = e2_high,
        pll0.e3_high                = e3_high,
        pll0.l0_low                 = l0_low,
        pll0.l1_low                 = l1_low,
        pll0.g0_low                 = g0_low,
        pll0.g1_low                 = g1_low,
        pll0.g2_low                 = g2_low,
        pll0.g3_low                 = g3_low,
        pll0.e0_low                 = e0_low,
        pll0.e1_low                 = e1_low,
        pll0.e2_low                 = e2_low,
        pll0.e3_low                 = e3_low,
        pll0.l0_initial             = l0_initial,
        pll0.l1_initial             = l1_initial,
        pll0.g0_initial             = g0_initial,
        pll0.g1_initial             = g1_initial,
        pll0.g2_initial             = g2_initial,
        pll0.g3_initial             = g3_initial,
        pll0.e0_initial             = e0_initial,
        pll0.e1_initial             = e1_initial,
        pll0.e2_initial             = e2_initial,
        pll0.e3_initial             = e3_initial,
        pll0.l0_mode                = l0_mode,
        pll0.l1_mode                = l1_mode,
        pll0.g0_mode                = g0_mode,
        pll0.g1_mode                = g1_mode,
        pll0.g2_mode                = g2_mode,
        pll0.g3_mode                = g3_mode,
        pll0.e0_mode                = e0_mode,
        pll0.e1_mode                = e1_mode,
        pll0.e2_mode                = e2_mode,
        pll0.e3_mode                = e3_mode,
        pll0.l0_ph                  = l0_ph,
        pll0.l1_ph                  = l1_ph,
        pll0.g0_ph                  = g0_ph,
        pll0.g1_ph                  = g1_ph,
        pll0.g2_ph                  = g2_ph,
        pll0.g3_ph                  = g3_ph,
        pll0.e0_ph                  = e0_ph,
        pll0.e1_ph                  = e1_ph,
        pll0.e2_ph                  = e2_ph,
        pll0.e3_ph                  = e3_ph,
        pll0.m_ph                   = m_ph,
        pll0.l0_time_delay          = l0_time_delay,
        pll0.l1_time_delay          = l1_time_delay,
        pll0.g0_time_delay          = g0_time_delay,
        pll0.g1_time_delay          = g1_time_delay,
        pll0.g2_time_delay          = g2_time_delay,
        pll0.g3_time_delay          = g3_time_delay,
        pll0.e0_time_delay          = e0_time_delay,
        pll0.e1_time_delay          = e1_time_delay,
        pll0.e2_time_delay          = e2_time_delay,
        pll0.e3_time_delay          = e3_time_delay,
        pll0.m_time_delay           = m_time_delay,
        pll0.n_time_delay           = n_time_delay,
        pll0.extclk3_counter        = extclk3_counter,
        pll0.extclk2_counter        = extclk2_counter,
        pll0.extclk1_counter        = extclk1_counter,
        pll0.extclk0_counter        = extclk0_counter,
        pll0.clk5_counter           = clk5_counter,
        pll0.clk4_counter           = clk4_counter,
        pll0.clk3_counter           = clk3_counter,
        pll0.clk2_counter           = clk2_counter,
        pll0.clk1_counter           = clk1_counter,
        pll0.clk0_counter           = clk0_counter,
        pll0.enable0_counter        = enable0_counter,
        pll0.enable1_counter        = enable1_counter,
        pll0.charge_pump_current    = charge_pump_current,
        pll0.loop_filter_r          = loop_filter_r,
        pll0.loop_filter_c          = loop_filter_c;

MF_stratixii_pll pll1
(
    .inclk (stratixii_inclk),
    .fbin (stratixii_fbin),
    .ena (stratixii_ena),
    .clkswitch (stratixii_clkswitch),
    .areset (stratixii_areset),
    .pfdena (stratixii_pfdena),
    .scanclk (stratixii_scanclk),
    .scanread (stratixii_scanread),
    .scanwrite (stratixii_scanwrite),
    .scandata (stratixii_scandata),
    .testin(),
    .scandone (stratixii_scandone),
    .clk (stratixii_clk),
    .clkbad (stratixii_clkbad),
    .activeclock (stratixii_activeclock),
    .locked (stratixii_locked),
    .clkloss (stratixii_clkloss),
    .scandataout (stratixii_scandataout),
    .enable0 (stratixii_enable0),
    .enable1 (stratixii_enable1),
    .testupout (),
    .testdownout (),
    .sclkout({stratixii_sclkout1, stratixii_sclkout0})
);
    defparam
        pll1.operation_mode         = operation_mode,
        pll1.pll_type               = pll_type,
        pll1.qualify_conf_done      = qualify_conf_done,
        pll1.compensate_clock       = compensate_clock,
        pll1.inclk0_input_frequency = inclk0_input_frequency,
        pll1.inclk1_input_frequency = inclk1_input_frequency,
        pll1.gate_lock_signal       = gate_lock_signal,
        pll1.gate_lock_counter      = gate_lock_counter,
        pll1.valid_lock_multiplier  = valid_lock_multiplier,
        pll1.invalid_lock_multiplier = invalid_lock_multiplier,
        pll1.switch_over_type       = switch_over_type,
        pll1.switch_over_on_lossclk = switch_over_on_lossclk,
        pll1.switch_over_on_gated_lock = switch_over_on_gated_lock,
        pll1.enable_switch_over_counter = enable_switch_over_counter,
        pll1.switch_over_counter    = switch_over_counter,
        pll1.feedback_source        = (feedback_source == "EXTCLK0") ? "CLK0" : feedback_source,
        pll1.bandwidth              = bandwidth,
        pll1.bandwidth_type         = bandwidth_type,
        pll1.spread_frequency       = spread_frequency,
        pll1.down_spread            = down_spread,
        pll1.self_reset_on_gated_loss_lock = self_reset_on_gated_loss_lock,
        pll1.simulation_type        = simulation_type,
        pll1.family_name            = intended_device_family,

        //  internal clock specifications
        pll1.clk5_multiply_by       = clk5_multiply_by,
        pll1.clk4_multiply_by       = clk4_multiply_by,
        pll1.clk3_multiply_by       = clk3_multiply_by,
        pll1.clk2_multiply_by       = clk2_multiply_by,
        pll1.clk1_multiply_by       = clk1_multiply_by,
        pll1.clk0_multiply_by       = clk0_multiply_by,
        pll1.clk5_divide_by         = clk5_divide_by,
        pll1.clk4_divide_by         = clk4_divide_by,
        pll1.clk3_divide_by         = clk3_divide_by,
        pll1.clk2_divide_by         = clk2_divide_by,
        pll1.clk1_divide_by         = clk1_divide_by,
        pll1.clk0_divide_by         = clk0_divide_by,
        pll1.clk5_phase_shift       = clk5_phase_shift,
        pll1.clk4_phase_shift       = clk4_phase_shift,
        pll1.clk3_phase_shift       = clk3_phase_shift,
        pll1.clk2_phase_shift       = clk2_phase_shift,
        pll1.clk1_phase_shift       = clk1_phase_shift,
        pll1.clk0_phase_shift       = clk0_phase_shift,
        pll1.clk5_duty_cycle        = clk5_duty_cycle,
        pll1.clk4_duty_cycle        = clk4_duty_cycle,
        pll1.clk3_duty_cycle        = clk3_duty_cycle,
        pll1.clk2_duty_cycle        = clk2_duty_cycle,
        pll1.clk1_duty_cycle        = clk1_duty_cycle,
        pll1.clk0_duty_cycle        = clk0_duty_cycle,
        pll1.vco_multiply_by        = vco_multiply_by,
        pll1.vco_divide_by          = vco_divide_by,
        pll1.clk2_output_frequency  = clk2_output_frequency,
        pll1.clk1_output_frequency  = clk1_output_frequency,
        pll1.clk0_output_frequency  = clk0_output_frequency,

        // advanced parameters
        pll1.vco_min                = (vco_min == 0 && m != 0)? 700 : vco_min,
        pll1.vco_max                = (vco_max == 0 && m != 0)? 3600 : vco_max,
        pll1.vco_center             = vco_center,
        pll1.pfd_min                = pfd_min,
        pll1.pfd_max                = pfd_max,
        pll1.m_initial              = m_initial,
        pll1.m                      = m,
        pll1.n                      = n,
        pll1.m2                     = m2,
        pll1.n2                     = n2,
        pll1.ss                     = ss,
        pll1.c0_high                = c0_high,
        pll1.c1_high                = c1_high,
        pll1.c2_high                = c2_high,
        pll1.c3_high                = c3_high,
        pll1.c4_high                = c4_high,
        pll1.c5_high                = c5_high,
        pll1.c0_low                 = c0_low,
        pll1.c1_low                 = c1_low,
        pll1.c2_low                 = c2_low,
        pll1.c3_low                 = c3_low,
        pll1.c4_low                 = c4_low,
        pll1.c5_low                 = c5_low,
        pll1.c0_initial             = c0_initial,
        pll1.c1_initial             = c1_initial,
        pll1.c2_initial             = c2_initial,
        pll1.c3_initial             = c3_initial,
        pll1.c4_initial             = c4_initial,
        pll1.c5_initial             = c5_initial,
        pll1.c0_mode                = c0_mode,
        pll1.c1_mode                = c1_mode,
        pll1.c2_mode                = c2_mode,
        pll1.c3_mode                = c3_mode,
        pll1.c4_mode                = c4_mode,
        pll1.c5_mode                = c5_mode,
        pll1.c0_ph                  = c0_ph,
        pll1.c1_ph                  = c1_ph,
        pll1.c2_ph                  = c2_ph,
        pll1.c3_ph                  = c3_ph,
        pll1.c4_ph                  = c4_ph,
        pll1.c5_ph                  = c5_ph,
        pll1.m_ph                   = m_ph,
        pll1.c1_use_casc_in         = c1_use_casc_in,
        pll1.c2_use_casc_in         = c2_use_casc_in,
        pll1.c3_use_casc_in         = c3_use_casc_in,
        pll1.c4_use_casc_in         = c4_use_casc_in,
        pll1.c5_use_casc_in         = c5_use_casc_in,
        pll1.clk5_counter           = (clk5_counter == "l1") ? "c5" : clk5_counter,
        pll1.clk4_counter           = (clk4_counter == "l0") ? "c4" : clk4_counter,
        pll1.clk3_counter           = (clk3_counter == "g3") ? "c3" : clk3_counter,
        pll1.clk2_counter           = (clk2_counter == "g2") ? "c2" : clk2_counter,
        pll1.clk1_counter           = (clk1_counter == "g1") ? "c1" : clk1_counter,
        pll1.clk0_counter           = (clk0_counter == "g0") ? "c0" : clk0_counter,
        pll1.enable0_counter        = (enable0_counter == "l0") ? "c0" : enable0_counter,
        pll1.enable1_counter        = (enable1_counter == "l0") ? "c1" : enable1_counter,
        pll1.charge_pump_current    = (m == 0)? 52 : charge_pump_current,
        pll1.loop_filter_r          = loop_filter_r,
        pll1.loop_filter_c          = (m == 0)? 16 : loop_filter_c,
        pll1.m_test_source          = m_test_source,
        pll1.c0_test_source         = c0_test_source,
        pll1.c1_test_source         = c1_test_source,
        pll1.c2_test_source         = c2_test_source,
        pll1.c3_test_source         = c3_test_source,
        pll1.c4_test_source         = c4_test_source,
        pll1.c5_test_source         = c5_test_source,
        pll1.sim_gate_lock_device_behavior = sim_gate_lock_device_behavior;

MF_stratixiii_pll pll2
(
    .inclk (stratix3_inclk),
    .fbin (stratix3_fbin),
    .clkswitch (stratix3_clkswitch),
    .areset (stratix3_areset),
    .pfdena (stratix3_pfdena),
    .scanclk (stratix3_scanclk),
    .scandata (scandata),
    .scanclkena (scanclkena_pullup),
    .configupdate (configupdate_pulldown),
    .clk (stratix3_clk),
    .phasecounterselect (stratix3_phasecounterselect),
    .phaseupdown (phaseupdown_pulldown),
    .phasestep (phasestep_pulldown),
    .clkbad (stratix3_clkbad),
    .activeclock (stratix3_activeclock),
    .locked (stratix3_locked),
    .scandataout (stratix3_scandataout),
    .scandone (stratix3_scandone),
    .phasedone (stratix3_phasedone),
    .vcooverrange (stratix3_vcooverrange),
    .vcounderrange (stratix3_vcounderrange),
    .fbout (stratix3_fbout)
);
    defparam
        pll2.operation_mode         = operation_mode,
        pll2.pll_type               = pll_type,
        pll2.compensate_clock       = compensate_clock,
        pll2.inclk0_input_frequency = inclk0_input_frequency,
        pll2.inclk1_input_frequency = inclk1_input_frequency,
        pll2.self_reset_on_loss_lock = self_reset_on_loss_lock,
        pll2.switch_over_type       = switch_over_type,
        pll2.enable_switch_over_counter = enable_switch_over_counter,
        pll2.switch_over_counter    = switch_over_counter,
        pll2.bandwidth              = bandwidth,
        pll2.bandwidth_type         = bandwidth_type,
        pll2.lock_high              = lock_high,
        pll2.lock_low               = lock_low,
        pll2.lock_window_ui         = lock_window_ui,
        pll2.simulation_type        = simulation_type,
        pll2.vco_frequency_control  = vco_frequency_control,
        pll2.vco_phase_shift_step   = vco_phase_shift_step,
        pll2.family_name            = intended_device_family,

        //  internal clock specifications
        pll2.clk9_multiply_by       = clk9_multiply_by,
        pll2.clk8_multiply_by       = clk8_multiply_by,
        pll2.clk7_multiply_by       = clk7_multiply_by,
        pll2.clk6_multiply_by       = clk6_multiply_by,
        pll2.clk5_multiply_by       = clk5_multiply_by,
        pll2.clk4_multiply_by       = clk4_multiply_by,
        pll2.clk3_multiply_by       = clk3_multiply_by,
        pll2.clk2_multiply_by       = clk2_multiply_by,
        pll2.clk1_multiply_by       = clk1_multiply_by,
        pll2.clk0_multiply_by       = clk0_multiply_by,
        pll2.clk9_divide_by         = clk9_divide_by,
        pll2.clk8_divide_by         = clk8_divide_by,
        pll2.clk7_divide_by         = clk7_divide_by,
        pll2.clk6_divide_by         = clk6_divide_by,
        pll2.clk5_divide_by         = clk5_divide_by,
        pll2.clk4_divide_by         = clk4_divide_by,
        pll2.clk3_divide_by         = clk3_divide_by,
        pll2.clk2_divide_by         = clk2_divide_by,
        pll2.clk1_divide_by         = clk1_divide_by,
        pll2.clk0_divide_by         = clk0_divide_by,
        pll2.clk9_phase_shift       = clk9_phase_shift,
        pll2.clk8_phase_shift       = clk8_phase_shift,
        pll2.clk7_phase_shift       = clk7_phase_shift,
        pll2.clk6_phase_shift       = clk6_phase_shift,
        pll2.clk5_phase_shift       = clk5_phase_shift,
        pll2.clk4_phase_shift       = clk4_phase_shift,
        pll2.clk3_phase_shift       = clk3_phase_shift,
        pll2.clk2_phase_shift       = clk2_phase_shift,
        pll2.clk1_phase_shift       = clk1_phase_shift,
        pll2.clk0_phase_shift       = clk0_phase_shift,
        pll2.clk9_duty_cycle        = clk9_duty_cycle,
        pll2.clk8_duty_cycle        = clk8_duty_cycle,
        pll2.clk7_duty_cycle        = clk7_duty_cycle,
        pll2.clk6_duty_cycle        = clk6_duty_cycle,
        pll2.clk5_duty_cycle        = clk5_duty_cycle,
        pll2.clk4_duty_cycle        = clk4_duty_cycle,
        pll2.clk3_duty_cycle        = clk3_duty_cycle,
        pll2.clk2_duty_cycle        = clk2_duty_cycle,
        pll2.clk1_duty_cycle        = clk1_duty_cycle,
        pll2.clk0_duty_cycle        = clk0_duty_cycle,
        pll2.vco_multiply_by        = vco_multiply_by,
        pll2.vco_divide_by          = vco_divide_by,
        pll2.dpa_multiply_by        = dpa_multiply_by,
        pll2.dpa_divide_by          = dpa_divide_by,
        pll2.dpa_divider            = dpa_divider,
        pll2.clk2_output_frequency  = clk2_output_frequency,
        pll2.clk1_output_frequency  = clk1_output_frequency,
        pll2.clk0_output_frequency  = clk0_output_frequency,
        pll2.clk9_use_even_counter_mode    = clk9_use_even_counter_mode,
        pll2.clk8_use_even_counter_mode    = clk8_use_even_counter_mode,
        pll2.clk7_use_even_counter_mode    = clk7_use_even_counter_mode,
        pll2.clk6_use_even_counter_mode    = clk6_use_even_counter_mode,
        pll2.clk5_use_even_counter_mode    = clk5_use_even_counter_mode,
        pll2.clk4_use_even_counter_mode    = clk4_use_even_counter_mode,
        pll2.clk3_use_even_counter_mode    = clk3_use_even_counter_mode,
        pll2.clk2_use_even_counter_mode    = clk2_use_even_counter_mode,
        pll2.clk1_use_even_counter_mode    = clk1_use_even_counter_mode,
        pll2.clk0_use_even_counter_mode    = clk0_use_even_counter_mode,
        pll2.clk9_use_even_counter_value   = clk9_use_even_counter_value,
        pll2.clk8_use_even_counter_value   = clk8_use_even_counter_value,
        pll2.clk7_use_even_counter_value   = clk7_use_even_counter_value,
        pll2.clk6_use_even_counter_value   = clk6_use_even_counter_value,
        pll2.clk5_use_even_counter_value   = clk5_use_even_counter_value,
        pll2.clk4_use_even_counter_value   = clk4_use_even_counter_value,
        pll2.clk3_use_even_counter_value   = clk3_use_even_counter_value,
        pll2.clk2_use_even_counter_value   = clk2_use_even_counter_value,
        pll2.clk1_use_even_counter_value   = clk1_use_even_counter_value,
        pll2.clk0_use_even_counter_value   = clk0_use_even_counter_value,

        // advanced parameters
        pll2.vco_min                = (vco_min == 0 && m != 0)? 100 : vco_min,
        pll2.vco_max                = (vco_max == 0 && m != 0)? 3600 : vco_max,
        pll2.vco_center             = vco_center,
        pll2.pfd_min                = pfd_min,
        pll2.pfd_max                = pfd_max,
        pll2.m_initial              = m_initial,
        pll2.m                      = m,
        pll2.n                      = n,
        pll2.c0_high                = c0_high,
        pll2.c1_high                = c1_high,
        pll2.c2_high                = c2_high,
        pll2.c3_high                = c3_high,
        pll2.c4_high                = c4_high,
        pll2.c5_high                = c5_high,
        pll2.c6_high                = c6_high,
        pll2.c7_high                = c7_high,
        pll2.c8_high                = c8_high,
        pll2.c9_high                = c9_high,
        pll2.c0_low                 = c0_low,
        pll2.c1_low                 = c1_low,
        pll2.c2_low                 = c2_low,
        pll2.c3_low                 = c3_low,
        pll2.c4_low                 = c4_low,
        pll2.c5_low                 = c5_low,
        pll2.c6_low                 = c6_low,
        pll2.c7_low                 = c7_low,
        pll2.c8_low                 = c8_low,
        pll2.c9_low                 = c9_low,
        pll2.c0_initial             = c0_initial,
        pll2.c1_initial             = c1_initial,
        pll2.c2_initial             = c2_initial,
        pll2.c3_initial             = c3_initial,
        pll2.c4_initial             = c4_initial,
        pll2.c5_initial             = c5_initial,
        pll2.c6_initial             = c6_initial,
        pll2.c7_initial             = c7_initial,
        pll2.c8_initial             = c8_initial,
        pll2.c9_initial             = c9_initial,
        pll2.c0_mode                = c0_mode,
        pll2.c1_mode                = c1_mode,
        pll2.c2_mode                = c2_mode,
        pll2.c3_mode                = c3_mode,
        pll2.c4_mode                = c4_mode,
        pll2.c5_mode                = c5_mode,
        pll2.c6_mode                = c6_mode,
        pll2.c7_mode                = c7_mode,
        pll2.c8_mode                = c8_mode,
        pll2.c9_mode                = c9_mode,
        pll2.c0_ph                  = c0_ph,
        pll2.c1_ph                  = c1_ph,
        pll2.c2_ph                  = c2_ph,
        pll2.c3_ph                  = c3_ph,
        pll2.c4_ph                  = c4_ph,
        pll2.c5_ph                  = c5_ph,
        pll2.c6_ph                  = c6_ph,
        pll2.c7_ph                  = c7_ph,
        pll2.c8_ph                  = c8_ph,
        pll2.c9_ph                  = c9_ph,
        pll2.m_ph                   = m_ph,
        pll2.c1_use_casc_in         = c1_use_casc_in,
        pll2.c2_use_casc_in         = c2_use_casc_in,
        pll2.c3_use_casc_in         = c3_use_casc_in,
        pll2.c4_use_casc_in         = c4_use_casc_in,
        pll2.c5_use_casc_in         = c5_use_casc_in,
        pll2.c6_use_casc_in         = c6_use_casc_in,
        pll2.c7_use_casc_in         = c7_use_casc_in,
        pll2.c8_use_casc_in         = c8_use_casc_in,
        pll2.c9_use_casc_in         = c9_use_casc_in,
        pll2.clk9_counter           = (port_clk9 != "PORT_USED") ? "unused" : clk9_counter,
        pll2.clk8_counter           = (port_clk8 != "PORT_USED") ? "unused" : clk8_counter,
        pll2.clk7_counter           = (port_clk7 != "PORT_USED") ? "unused" : clk7_counter,
        pll2.clk6_counter           = (port_clk6 != "PORT_USED") ? "unused" : clk6_counter,
        pll2.clk5_counter           = (port_clk5 != "PORT_USED") ? "unused" : (clk5_counter == "l1") ? "c5" : clk5_counter,
        pll2.clk4_counter           = (port_clk4 != "PORT_USED") ? "unused" : (clk4_counter == "l0") ? "c4" : clk4_counter,
        pll2.clk3_counter           = (port_clk3 != "PORT_USED") ? "unused" : (clk3_counter == "g3") ? "c3" : clk3_counter,
        pll2.clk2_counter           = (port_clk2 != "PORT_USED") ? "unused" : (clk2_counter == "g2") ? "c2" : clk2_counter,
        pll2.clk1_counter           = (port_clk1 != "PORT_USED") ? "unused" : (clk1_counter == "g1") ? "c1" : clk1_counter,
        pll2.clk0_counter           = (port_clk0 != "PORT_USED") ? "unused" : (clk0_counter == "g0") ? "c0" : clk0_counter,
        pll2.charge_pump_current    = charge_pump_current,
        pll2.loop_filter_r          = loop_filter_r,
        pll2.loop_filter_c          = loop_filter_c,
        pll2.charge_pump_current_bits = charge_pump_current_bits,
        pll2.loop_filter_c_bits     = loop_filter_c_bits,
        pll2.loop_filter_r_bits     = loop_filter_r_bits,
        pll2.m_test_source          = (m_test_source == 5)  ? -1 : m_test_source,
        pll2.c0_test_source         = (c0_test_source == 5) ? -1 : c0_test_source,
        pll2.c1_test_source         = (c1_test_source == 5) ? -1 : c1_test_source,
        pll2.c2_test_source         = (c2_test_source == 5) ? -1 : c2_test_source,
        pll2.c3_test_source         = (c3_test_source == 5) ? -1 : c3_test_source,
        pll2.c4_test_source         = (c4_test_source == 5) ? -1 : c4_test_source,
        pll2.c5_test_source         = (c5_test_source == 5) ? -1 : c5_test_source,
        pll2.c6_test_source         = (c6_test_source == 5) ? -1 : c6_test_source,
        pll2.c7_test_source         = (c7_test_source == 5) ? -1 : c7_test_source,
        pll2.c8_test_source         = (c8_test_source == 5) ? -1 : c8_test_source,
        pll2.c9_test_source         = (c9_test_source == 5) ? -1 : c9_test_source;

// cycloneiii_msg
MF_cycloneiii_pll pll3
(
    .inclk (cyclone3_inclk),
    .fbin (fbin),
    .clkswitch (cyclone3_clkswitch),
    .areset (cyclone3_areset),
    .pfdena (cyclone3_pfdena),
    .scanclk (cyclone3_scanclk),
    .scandata (scandata),
    .scanclkena (scanclkena_pullup),
    .configupdate (configupdate_pulldown),
    .clk (cyclone3_clk),
    .phasecounterselect (cyclone3_phasecounterselect),
    .phaseupdown (phaseupdown_pulldown),
    .phasestep (phasestep_pulldown),
    .clkbad (cyclone3_clkbad),
    .activeclock (cyclone3_activeclock),
    .locked (cyclone3_locked),
    .scandataout (cyclone3_scandataout),
    .scandone (cyclone3_scandone),
    .phasedone (cyclone3_phasedone),
    .vcooverrange (cyclone3_vcooverrange),
    .vcounderrange (cyclone3_vcounderrange),
    .fbout (cyclone3_fbout)
);
    defparam
        pll3.operation_mode         = operation_mode,
        pll3.pll_type               = pll_type,
        pll3.compensate_clock       = compensate_clock,
        pll3.inclk0_input_frequency = inclk0_input_frequency,
        pll3.inclk1_input_frequency = inclk1_input_frequency,
        pll3.self_reset_on_loss_lock = self_reset_on_loss_lock,
        pll3.switch_over_type       = switch_over_type,
        pll3.enable_switch_over_counter = enable_switch_over_counter,
        pll3.switch_over_counter    = switch_over_counter,
        pll3.bandwidth              = bandwidth,
        pll3.bandwidth_type         = bandwidth_type,
        pll3.lock_high              = lock_high,
        pll3.lock_low               = lock_low,
        pll3.lock_window_ui         = lock_window_ui,
        pll3.simulation_type        = simulation_type,
        pll3.vco_frequency_control  = vco_frequency_control,
        pll3.vco_phase_shift_step   = vco_phase_shift_step,
        pll3.family_name            = intended_device_family,

        //  internal clock specifications
        pll3.clk4_multiply_by       = clk4_multiply_by,
        pll3.clk3_multiply_by       = clk3_multiply_by,
        pll3.clk2_multiply_by       = clk2_multiply_by,
        pll3.clk1_multiply_by       = clk1_multiply_by,
        pll3.clk0_multiply_by       = clk0_multiply_by,
        pll3.clk4_divide_by         = clk4_divide_by,
        pll3.clk3_divide_by         = clk3_divide_by,
        pll3.clk2_divide_by         = clk2_divide_by,
        pll3.clk1_divide_by         = clk1_divide_by,
        pll3.clk0_divide_by         = clk0_divide_by,
        pll3.clk4_phase_shift       = clk4_phase_shift,
        pll3.clk3_phase_shift       = clk3_phase_shift,
        pll3.clk2_phase_shift       = clk2_phase_shift,
        pll3.clk1_phase_shift       = clk1_phase_shift,
        pll3.clk0_phase_shift       = clk0_phase_shift,
        pll3.clk4_duty_cycle        = clk4_duty_cycle,
        pll3.clk3_duty_cycle        = clk3_duty_cycle,
        pll3.clk2_duty_cycle        = clk2_duty_cycle,
        pll3.clk1_duty_cycle        = clk1_duty_cycle,
        pll3.clk0_duty_cycle        = clk0_duty_cycle,
        pll3.vco_multiply_by        = vco_multiply_by,
        pll3.vco_divide_by          = vco_divide_by,
        pll3.clk2_output_frequency  = clk2_output_frequency,
        pll3.clk1_output_frequency  = clk1_output_frequency,
        pll3.clk0_output_frequency  = clk0_output_frequency,
        pll3.clk4_use_even_counter_mode    = clk4_use_even_counter_mode,
        pll3.clk3_use_even_counter_mode    = clk3_use_even_counter_mode,
        pll3.clk2_use_even_counter_mode    = clk2_use_even_counter_mode,
        pll3.clk1_use_even_counter_mode    = clk1_use_even_counter_mode,
        pll3.clk0_use_even_counter_mode    = clk0_use_even_counter_mode,
        pll3.clk4_use_even_counter_value   = clk4_use_even_counter_value,
        pll3.clk3_use_even_counter_value   = clk3_use_even_counter_value,
        pll3.clk2_use_even_counter_value   = clk2_use_even_counter_value,
        pll3.clk1_use_even_counter_value   = clk1_use_even_counter_value,
        pll3.clk0_use_even_counter_value   = clk0_use_even_counter_value,

        // advanced parameters
        pll3.vco_min                = (vco_min == 0 && m != 0)? 200 : vco_min,
        pll3.vco_max                = (vco_max == 0 && m != 0)? 3600 : vco_max,
        pll3.vco_center             = vco_center,
        pll3.pfd_min                = pfd_min,
        pll3.pfd_max                = pfd_max,
        pll3.m_initial              = m_initial,
        pll3.m                      = m,
        pll3.n                      = n,
        pll3.c0_high                = c0_high,
        pll3.c1_high                = c1_high,
        pll3.c2_high                = c2_high,
        pll3.c3_high                = c3_high,
        pll3.c4_high                = c4_high,
        pll3.c0_low                 = c0_low,
        pll3.c1_low                 = c1_low,
        pll3.c2_low                 = c2_low,
        pll3.c3_low                 = c3_low,
        pll3.c4_low                 = c4_low,
        pll3.c0_initial             = c0_initial,
        pll3.c1_initial             = c1_initial,
        pll3.c2_initial             = c2_initial,
        pll3.c3_initial             = c3_initial,
        pll3.c4_initial             = c4_initial,
        pll3.c0_mode                = c0_mode,
        pll3.c1_mode                = c1_mode,
        pll3.c2_mode                = c2_mode,
        pll3.c3_mode                = c3_mode,
        pll3.c4_mode                = c4_mode,
        pll3.c0_ph                  = c0_ph,
        pll3.c1_ph                  = c1_ph,
        pll3.c2_ph                  = c2_ph,
        pll3.c3_ph                  = c3_ph,
        pll3.c4_ph                  = c4_ph,
        pll3.m_ph                   = m_ph,
        pll3.c1_use_casc_in         = c1_use_casc_in,
        pll3.c2_use_casc_in         = c2_use_casc_in,
        pll3.c3_use_casc_in         = c3_use_casc_in,
        pll3.c4_use_casc_in         = c4_use_casc_in,
        pll3.clk4_counter           = (port_clk4 != "PORT_USED") ? "unused" : (clk4_counter == "l0") ? "c4" : clk4_counter,
        pll3.clk3_counter           = (port_clk3 != "PORT_USED") ? "unused" : (clk3_counter == "g3") ? "c3" : clk3_counter,
        pll3.clk2_counter           = (port_clk2 != "PORT_USED") ? "unused" : (clk2_counter == "g2") ? "c2" : clk2_counter,
        pll3.clk1_counter           = (port_clk1 != "PORT_USED") ? "unused" : (clk1_counter == "g1") ? "c1" : clk1_counter,
        pll3.clk0_counter           = (port_clk0 != "PORT_USED") ? "unused" : (clk0_counter == "g0") ? "c0" : clk0_counter,
        pll3.charge_pump_current    = charge_pump_current,
        pll3.loop_filter_r          = loop_filter_r,
        pll3.loop_filter_c          = loop_filter_c,
        pll3.charge_pump_current_bits = charge_pump_current_bits,
        pll3.loop_filter_c_bits     = loop_filter_c_bits,
        pll3.loop_filter_r_bits     = loop_filter_r_bits,
        pll3.m_test_source          = (m_test_source == 5)  ? -1 : m_test_source,
        pll3.c0_test_source         = (c0_test_source == 5) ? -1 : c0_test_source,
        pll3.c1_test_source         = (c1_test_source == 5) ? -1 : c1_test_source,
        pll3.c2_test_source         = (c2_test_source == 5) ? -1 : c2_test_source,
        pll3.c3_test_source         = (c3_test_source == 5) ? -1 : c3_test_source,
        pll3.c4_test_source         = (c4_test_source == 5) ? -1 : c4_test_source;
// cycloneiii_msg

MF_cycloneiiigl_pll pll4
(
    .inclk (cyclone3gl_inclk),
    .fbin (fbin),
    .clkswitch (cyclone3gl_clkswitch),
    .areset (cyclone3gl_areset),
    .pfdena (cyclone3gl_pfdena),
    .scanclk (cyclone3gl_scanclk),
    .scandata (scandata),
    .scanclkena (scanclkena_pullup),
    .configupdate (configupdate_pulldown),
    .clk (cyclone3gl_clk),
    .phasecounterselect (cyclone3gl_phasecounterselect),
    .phaseupdown (phaseupdown_pulldown),
    .phasestep (phasestep_pulldown),
    .clkbad (cyclone3gl_clkbad),
    .activeclock (cyclone3gl_activeclock),
    .locked (cyclone3gl_locked),
    .scandataout (cyclone3gl_scandataout),
    .scandone (cyclone3gl_scandone),
    .phasedone (cyclone3gl_phasedone),
    .vcooverrange (cyclone3gl_vcooverrange),
    .vcounderrange (cyclone3gl_vcounderrange),
    .fbout (cyclone3gl_fbout),
    .fref (cyclone3gl_fref),
    .icdrclk (cyclone3gl_icdrclk)
);
    defparam
        pll4.operation_mode         = operation_mode,
        pll4.pll_type               = pll_type,
        pll4.compensate_clock       = compensate_clock,
        pll4.inclk0_input_frequency = inclk0_input_frequency,
        pll4.inclk1_input_frequency = inclk1_input_frequency,
        pll4.self_reset_on_loss_lock = self_reset_on_loss_lock,
        pll4.switch_over_type       = switch_over_type,
        pll4.enable_switch_over_counter = enable_switch_over_counter,
        pll4.switch_over_counter    = switch_over_counter,
        pll4.bandwidth              = bandwidth,
        pll4.bandwidth_type         = bandwidth_type,
        pll4.lock_high              = lock_high,
        pll4.lock_low               = lock_low,
        pll4.lock_window_ui         = lock_window_ui,
        pll4.simulation_type        = simulation_type,
        pll4.vco_frequency_control  = vco_frequency_control,
        pll4.vco_phase_shift_step   = vco_phase_shift_step,
        pll4.family_name            = intended_device_family,

        //  internal clock specifications
        pll4.clk4_multiply_by       = clk4_multiply_by,
        pll4.clk3_multiply_by       = clk3_multiply_by,
        pll4.clk2_multiply_by       = clk2_multiply_by,
        pll4.clk1_multiply_by       = clk1_multiply_by,
        pll4.clk0_multiply_by       = clk0_multiply_by,
        pll4.clk4_divide_by         = clk4_divide_by,
        pll4.clk3_divide_by         = clk3_divide_by,
        pll4.clk2_divide_by         = clk2_divide_by,
        pll4.clk1_divide_by         = clk1_divide_by,
        pll4.clk0_divide_by         = clk0_divide_by,
        pll4.clk4_phase_shift       = clk4_phase_shift,
        pll4.clk3_phase_shift       = clk3_phase_shift,
        pll4.clk2_phase_shift       = clk2_phase_shift,
        pll4.clk1_phase_shift       = clk1_phase_shift,
        pll4.clk0_phase_shift       = clk0_phase_shift,
        pll4.clk4_duty_cycle        = clk4_duty_cycle,
        pll4.clk3_duty_cycle        = clk3_duty_cycle,
        pll4.clk2_duty_cycle        = clk2_duty_cycle,
        pll4.clk1_duty_cycle        = clk1_duty_cycle,
        pll4.clk0_duty_cycle        = clk0_duty_cycle,
        pll4.dpa_multiply_by        = dpa_multiply_by,
        pll4.dpa_divide_by          = dpa_divide_by,
        pll4.vco_multiply_by        = vco_multiply_by,
        pll4.vco_divide_by          = vco_divide_by,
        pll4.clk2_output_frequency  = clk2_output_frequency,
        pll4.clk1_output_frequency  = clk1_output_frequency,
        pll4.clk0_output_frequency  = clk0_output_frequency,
        pll4.clk4_use_even_counter_mode    = clk4_use_even_counter_mode,
        pll4.clk3_use_even_counter_mode    = clk3_use_even_counter_mode,
        pll4.clk2_use_even_counter_mode    = clk2_use_even_counter_mode,
        pll4.clk1_use_even_counter_mode    = clk1_use_even_counter_mode,
        pll4.clk0_use_even_counter_mode    = clk0_use_even_counter_mode,
        pll4.clk4_use_even_counter_value   = clk4_use_even_counter_value,
        pll4.clk3_use_even_counter_value   = clk3_use_even_counter_value,
        pll4.clk2_use_even_counter_value   = clk2_use_even_counter_value,
        pll4.clk1_use_even_counter_value   = clk1_use_even_counter_value,
        pll4.clk0_use_even_counter_value   = clk0_use_even_counter_value,

        // advanced parameters
        pll4.vco_min                = (vco_min == 0 && m != 0)? 200 : vco_min,
        pll4.vco_max                = (vco_max == 0 && m != 0)? 3600 : vco_max,
        pll4.vco_center             = vco_center,
        pll4.dpa_divider            = dpa_divider,
        pll4.pfd_min                = pfd_min,
        pll4.pfd_max                = pfd_max,
        pll4.m_initial              = m_initial,
        pll4.m                      = m,
        pll4.n                      = n,
        pll4.c0_high                = c0_high,
        pll4.c1_high                = c1_high,
        pll4.c2_high                = c2_high,
        pll4.c3_high                = c3_high,
        pll4.c4_high                = c4_high,
        pll4.c0_low                 = c0_low,
        pll4.c1_low                 = c1_low,
        pll4.c2_low                 = c2_low,
        pll4.c3_low                 = c3_low,
        pll4.c4_low                 = c4_low,
        pll4.c0_initial             = c0_initial,
        pll4.c1_initial             = c1_initial,
        pll4.c2_initial             = c2_initial,
        pll4.c3_initial             = c3_initial,
        pll4.c4_initial             = c4_initial,
        pll4.c0_mode                = c0_mode,
        pll4.c1_mode                = c1_mode,
        pll4.c2_mode                = c2_mode,
        pll4.c3_mode                = c3_mode,
        pll4.c4_mode                = c4_mode,
        pll4.c0_ph                  = c0_ph,
        pll4.c1_ph                  = c1_ph,
        pll4.c2_ph                  = c2_ph,
        pll4.c3_ph                  = c3_ph,
        pll4.c4_ph                  = c4_ph,
        pll4.m_ph                   = m_ph,
        pll4.c1_use_casc_in         = c1_use_casc_in,
        pll4.c2_use_casc_in         = c2_use_casc_in,
        pll4.c3_use_casc_in         = c3_use_casc_in,
        pll4.c4_use_casc_in         = c4_use_casc_in,
        pll4.clk4_counter           = (port_clk4 != "PORT_USED") ? "unused" : (clk4_counter == "l0") ? "c4" : clk4_counter,
        pll4.clk3_counter           = (port_clk3 != "PORT_USED") ? "unused" : (clk3_counter == "g3") ? "c3" : clk3_counter,
        pll4.clk2_counter           = (port_clk2 != "PORT_USED") ? "unused" : (clk2_counter == "g2") ? "c2" : clk2_counter,
        pll4.clk1_counter           = (port_clk1 != "PORT_USED") ? "unused" : (clk1_counter == "g1") ? "c1" : clk1_counter,
        pll4.clk0_counter           = (port_clk0 != "PORT_USED") ? "unused" : (clk0_counter == "g0") ? "c0" : clk0_counter,
        pll4.charge_pump_current    = charge_pump_current,
        pll4.loop_filter_r          = loop_filter_r,
        pll4.loop_filter_c          = loop_filter_c,
        pll4.charge_pump_current_bits = charge_pump_current_bits,
        pll4.loop_filter_c_bits     = loop_filter_c_bits,
        pll4.loop_filter_r_bits     = loop_filter_r_bits,
        pll4.m_test_source          = (m_test_source == 5)  ? -1 : m_test_source,
        pll4.c0_test_source         = (c0_test_source == 5) ? -1 : c0_test_source,
        pll4.c1_test_source         = (c1_test_source == 5) ? -1 : c1_test_source,
        pll4.c2_test_source         = (c2_test_source == 5) ? -1 : c2_test_source,
        pll4.c3_test_source         = (c3_test_source == 5) ? -1 : c3_test_source,
        pll4.c4_test_source         = (c4_test_source == 5) ? -1 : c4_test_source;

            
pll_iobuf iobuf1
(
    .i (stratix3_fbout),
    .oe (1'b1),
    .io (iobuf_io),
    .o (iobuf_o)
);

// ALWAYS CONSTRUCT BLOCK
always @(posedge pll_lock or posedge areset)
begin
    if (areset)
        pll_lock_sync <= 1'b0;
    else
        pll_lock_sync <= 1'b1;
end

// CONTINOUS ASSIGNMENT
assign ena_pullup = ((port_pllena == "PORT_CONNECTIVITY") ||
                        (port_pllena == "PORT_USED")) ? pllena : 1'b1;
assign pfdena_pullup = ((port_pfdena == "PORT_CONNECTIVITY") ||
                        (port_pfdena == "PORT_USED")) ? pfdena : 1'b1;
assign clkena_pullup[0] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_clkena0 == "PORT_USED")) &&
                            (port_clkena0 != "PORT_UNUSED") ? clkena[0] : 1'b1;
assign clkena_pullup[1] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_clkena1 == "PORT_USED")) &&
                            (port_clkena1 != "PORT_UNUSED") ? clkena[1] : 1'b1;
assign clkena_pullup[2] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_clkena2 == "PORT_USED")) &&
                            (port_clkena2 != "PORT_UNUSED") ? clkena[2] : 1'b1;
assign clkena_pullup[3] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_clkena3 == "PORT_USED")) &&
                            (port_clkena3 != "PORT_UNUSED") ? clkena[3] : 1'b1;
assign clkena_pullup[4] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_clkena4 == "PORT_USED")) &&
                            (port_clkena4 != "PORT_UNUSED") ? clkena[4] : 1'b1;
assign clkena_pullup[5] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_clkena5 == "PORT_USED")) &&
                            (port_clkena5 != "PORT_UNUSED") ? clkena[5] : 1'b1;

assign extclkena_pullup[0] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_extclkena0 == "PORT_USED")) &&
                            (port_extclkena0 != "PORT_UNUSED") ? extclkena[0] : 1'b1;
assign extclkena_pullup[1] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_extclkena1 == "PORT_USED")) &&
                            (port_extclkena1 != "PORT_UNUSED") ? extclkena[1] : 1'b1;
assign extclkena_pullup[2] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_extclkena2 == "PORT_USED")) &&
                            (port_extclkena2 != "PORT_UNUSED") ? extclkena[2] : 1'b1;
assign extclkena_pullup[3] = (!(alpha_tolower(pll_type) == "fast") ||
                            (port_extclkena3 == "PORT_USED")) &&
                            (port_extclkena3 != "PORT_UNUSED") ? extclkena[3] : 1'b1;
assign scanclkena_pullup = ((port_scanclkena == "PORT_CONNECTIVITY") ||
                            (port_scanclkena == "PORT_USED")) ? scanclkena : 1'b1;

assign fbin_pulldown = ((port_fbin == "PORT_CONNECTIVITY") ||
                        (port_fbin == "PORT_USED")) ? fbin : 1'b0;

assign phasecounterselect_pulldown[width_phasecounterselect-1 :0] = ((port_phasecounterselect == "PORT_CONNECTIVITY") ||
                            (port_phasecounterselect == "PORT_USED")) ? phasecounterselect[width_phasecounterselect-1 :0] : {width_phasecounterselect{1'b0}};
assign phaseupdown_pulldown = ((port_phaseupdown == "PORT_CONNECTIVITY") ||
                            (port_phaseupdown == "PORT_USED")) ? phaseupdown : 1'b0;
assign phasestep_pulldown = ((port_phasestep == "PORT_CONNECTIVITY") ||
                            (port_phasestep == "PORT_USED")) ? phasestep : 1'b0;
assign configupdate_pulldown = ((port_configupdate == "PORT_CONNECTIVITY") ||
                            (port_configupdate == "PORT_USED")) ? configupdate : 1'b0;
                            
assign scanclk_pulldown = ((port_scanclk != "PORT_UNUSED")) ? scanclk : 1'b0;
assign scanread_pulldown = ((port_scanread == "PORT_CONNECTIVITY") ||
                        (port_scanread == "PORT_USED")) ? scanread : 1'b0;
assign scanwrite_pulldown = ((port_scanwrite == "PORT_CONNECTIVITY") ||
                        (port_scanwrite == "PORT_USED")) ? scanwrite : 1'b0;
assign scandata_pulldown = ((port_scandata == "PORT_CONNECTIVITY") ||
                        (port_scandata == "PORT_USED")) ? scandata : 1'b0;
assign inclk_pulldown = inclk;
assign clkswitch_pulldown = ((port_clkswitch == "PORT_CONNECTIVITY") ||
                        (port_clkswitch == "PORT_USED")) ? clkswitch : 1'b0;
assign areset_pulldown = ((port_areset == "PORT_CONNECTIVITY") ||
                        (port_areset == "PORT_USED")) ? areset : 1'b0;
assign scanclr_pulldown = ((port_scanaclr == "PORT_CONNECTIVITY") ||
                        (port_scanaclr == "PORT_USED")) ? scanaclr : 1'b0;

assign stratix_inclk = (family_has_stratix_style_pll) ? inclk_pulldown : {2{1'b0}};
assign stratix_fbin  = (family_has_stratix_style_pll) ? fbin_pulldown : 1'b0;
assign stratix_ena   = (family_has_stratix_style_pll) ? ena_pullup : 1'bZ;
assign stratix_clkswitch = (family_has_stratix_style_pll) ? clkswitch_pulldown : 1'b0;
assign stratix_areset  = (family_has_stratix_style_pll) ? areset_pulldown : 1'b0;
assign stratix_pfdena = (family_has_stratix_style_pll) ? pfdena_pullup : 1'b1;
assign stratix_clkena = (family_has_stratix_style_pll) ? clkena_pullup : {5{1'b0}};
assign stratix_extclkena = (family_has_stratix_style_pll) ? extclkena_pullup : {3{1'b0}};
assign stratix_scanclk = (family_has_stratix_style_pll) ? scanclk_pulldown : 1'b0;
assign stratix_scanclr = (family_has_stratix_style_pll) ? scanclr_pulldown : 1'b0;
assign stratix_scandata = (family_has_stratix_style_pll) ? scandata_pulldown : 1'b0;
assign stratixii_inclk = (family_has_stratixii_style_pll) ? inclk_pulldown : {2{1'b0}};
assign stratixii_fbin  = (family_has_stratixii_style_pll) ? fbin_pulldown : 1'b0;
assign stratixii_ena   = (family_has_stratixii_style_pll) ? ena_pullup : 1'bZ;
assign stratixii_clkswitch = (family_has_stratixii_style_pll) ? clkswitch_pulldown : 1'b0;
assign stratixii_areset = (family_has_stratixii_style_pll) ? areset_pulldown : 1'b0;
assign stratixii_pfdena = (family_has_stratixii_style_pll) ? pfdena_pullup : 1'b1;
assign stratixii_scanread = (family_has_stratixii_style_pll) ? scanread_pulldown : 1'b0;
assign stratixii_scanwrite = (family_has_stratixii_style_pll) ? scanwrite_pulldown : 1'b0;                        
assign stratixii_scanclk = (family_has_stratixii_style_pll) ? scanclk_pulldown : 1'b0;
assign stratixii_scandata = (family_has_stratixii_style_pll) ? scandata_pulldown : 1'b0;
assign stratix3_inclk = (family_stratixiii) ? inclk_pulldown : {2{1'b0}};
assign stratix3_clkswitch =  (family_stratixiii) ? clkswitch_pulldown : 1'b0;
assign stratix3_areset   = (family_stratixiii) ? areset_pulldown : 1'b0;
assign stratix3_pfdena  = (family_stratixiii) ? pfdena_pullup : 1'b1;
assign stratix3_scanclk = (family_stratixiii) ? scanclk_pulldown : 1'b0;
assign stratix3_phasecounterselect = (family_stratixiii) ? phasecounterselect_pulldown : {4{1'b0}};
assign cyclone3_inclk = (family_cycloneiii) ? inclk_pulldown : {2{1'b0}};
assign cyclone3_clkswitch =  (family_cycloneiii) ? clkswitch_pulldown : 1'b0;
assign cyclone3_areset   = (family_cycloneiii) ? areset_pulldown : 1'b0;
assign cyclone3_pfdena  = (family_cycloneiii) ? pfdena_pullup : 1'b1;
assign cyclone3_scanclk = (family_cycloneiii) ? scanclk_pulldown : 1'b0;
assign cyclone3_phasecounterselect = (family_cycloneiii) ? phasecounterselect_pulldown[2:0] : {3{1'b0}};
assign cyclone3gl_inclk = (family_cycloneiiigl) ? inclk_pulldown : {2{1'b0}};
assign cyclone3gl_clkswitch =  (family_cycloneiiigl) ? clkswitch_pulldown : 1'b0;
assign cyclone3gl_areset   = (family_cycloneiiigl) ? areset_pulldown : 1'b0;
assign cyclone3gl_pfdena  = (family_cycloneiiigl) ? pfdena_pullup : 1'b1;
assign cyclone3gl_scanclk = (family_cycloneiiigl) ? scanclk_pulldown : 1'b0;
assign cyclone3gl_phasecounterselect = (family_cycloneiiigl) ? phasecounterselect_pulldown[2:0] : {3{1'b0}};
assign scandone_wire =  (family_has_stratixii_style_pll) ? stratixii_scandone :
                        (family_stratixiii) ? stratix3_scandone :
                        (family_cycloneiii) ? cyclone3_scandone :
                        (family_cycloneiiigl) ? cyclone3gl_scandone :
                        1'b0;
assign scandone = (port_scandone != "PORT_UNUSED") ? scandone_wire : 1'b0;
assign clk_wire = (family_base_cycloneii) ? {7'b0, stratixii_clk[2:0]} :
                (family_has_stratixii_style_pll) ? {4'b0, stratixii_clk} :
                (family_stratixiii) ? {stratix3_clk} :
                (family_cycloneiii) ? {5'b0, cyclone3_clk} :
                (family_cycloneiiigl) ? {5'b0, cyclone3gl_clk} :
                {4'b0, stratix_clk};
assign clk_tmp[0] = (port_clk0 != "PORT_UNUSED") ? clk_wire[0] : 1'b0;
assign clk_tmp[1] = (port_clk1 != "PORT_UNUSED") ? clk_wire[1] : 1'b0;
assign clk_tmp[2] = (port_clk2 != "PORT_UNUSED") ? clk_wire[2] : 1'b0;
assign clk_tmp[3] = (port_clk3 != "PORT_UNUSED") ? clk_wire[3] : 1'b0;
assign clk_tmp[4] = (port_clk4 != "PORT_UNUSED") ? clk_wire[4] : 1'b0;
assign clk_tmp[5] = (port_clk5 != "PORT_UNUSED") ? clk_wire[5] : 1'b0;
assign clk_tmp[6] = (port_clk6 != "PORT_UNUSED") ? clk_wire[6] : 1'b0;
assign clk_tmp[7] = (port_clk7 != "PORT_UNUSED") ? clk_wire[7] : 1'b0;
assign clk_tmp[8] = (port_clk8 != "PORT_UNUSED") ? clk_wire[8] : 1'b0;
assign clk_tmp[9] = (port_clk9 != "PORT_UNUSED") ? clk_wire[9] : 1'b0;
assign clk = clk_tmp[width_clock-1:0];
assign extclk[0] = (port_extclk0 != "PORT_UNUSED") ? stratix_extclk[0] : 1'b0;
assign extclk[1] = (port_extclk1 != "PORT_UNUSED") ? stratix_extclk[1] : 1'b0;
assign extclk[2] = (port_extclk2 != "PORT_UNUSED") ? stratix_extclk[2] : 1'b0;
assign extclk[3] = (port_extclk3 != "PORT_UNUSED") ? stratix_extclk[3] : 1'b0;
assign clkbad_wire = (family_base_cycloneii) ? 2'b0 :
                (family_has_stratixii_style_pll) ? stratixii_clkbad :
                (family_stratixiii) ? stratix3_clkbad :
                (family_cycloneiii) ? cyclone3_clkbad :
                (family_cycloneiiigl) ? cyclone3gl_clkbad :
                stratix_clkbad;
assign clkbad[0] = (port_clkbad0 != "PORT_UNUSED") ? clkbad_wire[0] : 1'b0;
assign clkbad[1] = (port_clkbad1 != "PORT_UNUSED") ? clkbad_wire[1] : 1'b0;
assign activeclock_wire = (family_base_cycloneii) ? 1'b0 :
                    (family_has_stratixii_style_pll) ? stratixii_activeclock :
                    (family_stratixiii) ? stratix3_activeclock :
                    (family_cycloneiii) ? cyclone3_activeclock :
                    (family_cycloneiiigl) ? cyclone3gl_activeclock :
                    stratix_activeclock;
assign activeclock = (port_activeclock != "PORT_UNUSED") ? activeclock_wire : 1'b0;

assign pll_lock    = (family_stratixiii) ? stratix3_locked :
                    (family_cycloneiii) ? cyclone3_locked :
                    (family_cycloneiiigl) ? cyclone3gl_locked : 1'b0;

assign locked_wire = (family_has_stratixii_style_pll) ? stratixii_locked :
                    (family_stratixiii) ? stratix3_locked & pll_lock_sync:
                    (family_cycloneiii) ? cyclone3_locked & pll_lock_sync: 
                    (family_cycloneiiigl) ? cyclone3gl_locked : 
                    stratix_locked;
assign locked = (port_locked != "PORT_UNUSED") ? locked_wire : 1'b0;
assign stratix_locked = (alpha_tolower(pll_type) == "fast") ? (!locked_tmp) : locked_tmp;
assign clkloss_wire = (family_base_cycloneii) ? 1'b0 :
                    (family_has_stratixii_style_pll) ? stratixii_clkloss :
                    stratix_clkloss;
assign clkloss = (port_clkloss != "PORT_UNUSED") ? clkloss_wire : 1'b0;
assign scandataout_wire = (family_base_cycloneii) ? 1'b0 :
                    (family_has_stratixii_style_pll) ? stratixii_scandataout :
                    (family_stratixiii) ? stratix3_scandataout :
                    (family_cycloneiii) ? cyclone3_scandataout :
                    (family_cycloneiiigl) ? cyclone3gl_scandataout :
                    stratix_scandataout;
assign scandataout = (port_scandataout != "PORT_UNUSED") ? scandataout_wire : 1'b0;
assign enable0 = (family_base_cycloneii) ? 1'b0 :
                    (family_has_stratixii_style_pll) ? stratixii_enable0 :
                    stratix_enable0;
assign enable1 = (family_base_cycloneii) ? 1'b0 :
                    (family_has_stratixii_style_pll) ? stratixii_enable1 :
                    stratix_enable1;
assign sclkout0_wire = (family_has_stratixii_style_pll) ? stratixii_sclkout0 : 1'b0;
assign sclkout0 = (port_sclkout0 != "PORT_UNUSED") ? sclkout0_wire : 1'b0;
assign sclkout1_wire = (family_has_stratixii_style_pll) ? stratixii_sclkout1 : 1'b0;
assign sclkout1 = (port_sclkout1 != "PORT_UNUSED") ? sclkout1_wire : 1'b0;
assign phasedone_wire =  (family_stratixiii) ? stratix3_phasedone : 
            (family_cycloneiii) ? cyclone3_phasedone :
            (family_cycloneiiigl) ? cyclone3gl_phasedone :
            1'b0;
assign phasedone = (port_phasedone != "PORT_UNUSED") ? phasedone_wire : 1'b0;
assign vcooverrange_wire =  (family_stratixiii) ? stratix3_vcooverrange : 
            (family_cycloneiii) ? cyclone3_vcooverrange :
            (family_cycloneiiigl) ? cyclone3gl_vcooverrange :
            1'b0;
assign vcooverrange = (port_vcooverrange != "PORT_UNUSED") ? vcooverrange_wire : 1'b0;
assign vcounderrange_wire = (family_stratixiii) ? stratix3_vcounderrange : 
            (family_cycloneiii) ? cyclone3_vcounderrange :
            (family_cycloneiiigl) ? cyclone3gl_vcounderrange :
            1'b0;
assign vcounderrange = (port_vcounderrange != "PORT_UNUSED") ? vcounderrange_wire : 1'b0;
assign fbout_wire =  (family_stratixiii) ? stratix3_fbout : 
            (family_cycloneiii) ? cyclone3_fbout :
            (family_cycloneiiigl) ? cyclone3gl_fbout :
            1'b0;
assign fbout = (port_fbout != "PORT_UNUSED") ? fbout_wire : 1'b0;
assign fbmimicbidir = ((using_fbmimicbidir_port == "ON") && (alpha_tolower(operation_mode) == "zero_delay_buffer") && family_stratixiii && (family_arriaii == 0)) ? iobuf_io : 1'b0;
assign stratix3_fbin = ((using_fbmimicbidir_port == "ON") && (alpha_tolower(operation_mode) == "zero_delay_buffer") && family_stratixiii && (family_arriaii == 0)) ? iobuf_o : ((alpha_tolower(operation_mode) == "zero_delay_buffer") && family_arriaii) ? fbout_wire : fbin;

assign fref = cyclone3gl_fref;
assign icdrclk = cyclone3gl_icdrclk;

endmodule //altpll
