`include "mips789_defs.v"
module assert_ctl_fsm(input clk, rst,
                      input [2:0] id_cmd,
    				  input id2ra_ins_clr,
    				  input id2ra_ins_cls,
    				  input id2ra_ctl_clr,
    				  input id2ra_ctl_cls,
                      input ra2exec_ctl_clr,
                      input zz_is_nop,
                      input irq,
                      input iack,
                      input [3:0] pc_prectl,
                      input [4:0] CurrState,
                      input pause);

   initial $display("%m binded");

    parameter
        ID_CUR   = `FSM_CUR,   ID_LD    = `FSM_LD ,
        ID_MUL   = `FSM_MUL,   ID_NOI   = `FSM_NOI,
        ID_RET   = `FSM_RET,

        PC_IGN   = `PC_IGN ,   PC_IRQ   = `PC_IRQ,
        PC_KEP   = `PC_KEP ,   PC_RST   = `PC_RST;

   wire [5:0] ra_out = {id2ra_ins_clr,
                        id2ra_ins_cls,
                        id2ra_ctl_clr,
                        id2ra_ctl_cls,
                        ra2exec_ctl_clr,
                        zz_is_nop};
   
   
   property state_IDLE;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `IDLE)
          |->
          (ra_out == 6'b000000);
   endproperty

   property to_IDLE;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `RET) || (CurrState == `IRQ) || (CurrState == `RST) || (CurrState == `LD) ||
          ((CurrState == `NOI) && (~|id_cmd))
          |=>
          (CurrState == `IDLE) ;
   endproperty
   
   property state_IRQ;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `IRQ)
          |->
          (ra_out == 6'b101010);
   endproperty

   property to_IRQ;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `IDLE) && (irq && ~iack)
          |=>
          (CurrState == `IRQ);
   endproperty

   //assume property
   // (@(posedge clk) ~pause);

   property state_RET;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `RET)
          |->
          (ra_out == 6'b000000);
   endproperty

   property to_RET;
      @(posedge clk)
        disable iff(!rst)
          ((CurrState == `IDLE) && (id_cmd == ID_RET) && (!irq))
          |=>
          (CurrState == `RET);
   endproperty

   property state_LD;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `LD)
          |->
          (ra_out == 6'b101001);
   endproperty

   property to_LD;
      @(posedge clk)
        disable iff(!rst)
          ((CurrState == `IDLE) && (id_cmd == ID_LD) && (!irq))
          |=>
          (CurrState == `LD);
   endproperty

   property state_CUR;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `CUR)
          |->
          (ra_out == 6'b010111);
   endproperty

   property to_CUR;
      @(posedge clk)
        disable iff(!rst)
          ((CurrState == `IDLE) && (id_cmd == ID_CUR) && (!irq))
          |=>
          (CurrState == `CUR);
   endproperty

   property state_MUL;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `MUL)
          |->
          (ra_out == 6'b101000);
   endproperty

   property to_MUL;
      @(posedge clk)
        disable iff(!rst)
          ((CurrState == `IDLE) && (id_cmd == ID_MUL) && (!irq))
          |=>
          (CurrState == `MUL);
   endproperty

   property state_NOI;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `NOI)
          |->
          (ra_out == 6'b000000);
   endproperty

   property to_NOI;
      @(posedge clk)
        disable iff(!rst)
          (CurrState == `CUR)
          |=>
          (CurrState == `NOI);
   endproperty

   property delay_MUL;
      @(posedge clk)
        disable iff(!rst)
          $rose(CurrState == `MUL)
          |->
          ##33 (CurrState == `IDLE);
   endproperty

   
   // Assertions
   _a_state_IDLE: assert property (state_IDLE);
   //_a_to_IDLE:    assert property (to_IDLE);
   _a_state_IRQ:  assert property (state_IRQ);
   _a_to_IRQ:     assert property (to_IRQ);
   _a_state_RET:  assert property (state_RET);
   _a_to_RET:     assert property (to_RET);
   _a_state_LD:   assert property (state_LD);
   _a_to_LD:      assert property (to_LD);
   _a_state_CUR:  assert property (state_CUR);
   _a_to_CUR:     assert property (to_CUR);
   _a_state_MUL:  assert property (state_MUL);
   _a_to_MUL:     assert property (to_MUL);
   _a_state_NOI:  assert property (state_NOI);
   _a_to_NOI:     assert property (to_NOI);
   _a_delay_MUL:  assert property (delay_MUL);
  

   paused_transitions :
     assert property(
                     @(posedge clk)
                     disable iff(~rst) if (!$isunknown(CurrState))
                     (pause |=> (CurrState == $past(CurrState))));

   idle_to_noi :
     assert property(
                     @(posedge clk)
                     disable iff (~rst)
                     (CurrState == `IDLE) && ~irq && ~pause && (id_cmd == ID_NOI) |=> (CurrState == `NOI));

   property noi_to_state(cmd, state);
      @(posedge clk)
        disable iff(~rst)
          (CurrState == `NOI) && ~pause && (id_cmd == cmd) |=> (CurrState == state);
   endproperty

   noi_to_noi : assert property (noi_to_state(ID_NOI, `NOI));
   noi_to_cur : assert property (noi_to_state(ID_CUR, `CUR));
   noi_to_mul : assert property (noi_to_state(ID_MUL, `MUL));
   noi_to_ld  : assert property (noi_to_state(ID_LD, `LD));
   noi_to_ret : assert property (noi_to_state(ID_RET, `RET));

   noi_to_idle :
     assert property(
                     @(posedge clk)
                     disable iff(~rst)
                     (CurrState == `NOI)
                     && ~pause
                     && (id_cmd != ID_NOI)
                     && (id_cmd != ID_CUR)
                     && (id_cmd != ID_MUL)
                     && (id_cmd != ID_LD)
                     && (id_cmd != ID_RET) |=> (CurrState == `IDLE));

   noi_state_outputs :
     assert property(
                     @(posedge clk)
                     disable iff(~rst)
                     (CurrState == `NOI) |->
                     (id2ra_ins_clr == 0) && (id2ra_ins_cls == 0) && (id2ra_ctl_clr == 0) &&
                     (id2ra_ctl_cls == 0) && (ra2exec_ctl_clr == 0) &&
                     (pc_prectl == PC_IGN) && (zz_is_nop == 0));

   mul_to_idle :
     assert property(
                     @(posedge clk)
                     disable iff(~rst)
                     ((CurrState == `MUL) && ~pause)[*33] ##1 ~pause |-> (CurrState == `IDLE)); 

   idle_to_mul :
     assert property(
                     @(posedge clk)
                     disable iff(~rst)
                     (CurrState == `IDLE) && ~irq && ~pause && (id_cmd == ID_MUL) |=> (CurrState == `MUL));

   //Evean: Comment this out because 0in bug, refer to #4396
   //updating_iack :
   //  assert property(
   //                  @(posedge clk)
   //                  disable iff(~rst)
   //                  if (CurrState == `IRQ)
   //                  (iack)
   //                  else if (CurrState == `RET)
   //                  (~iack)
   //                  else
   //                  (iack == $past(iack)));

   idle_to_irq :
     assert property(
                     @(posedge clk)
                     disable iff(~rst)
                     (CurrState == `IDLE) && irq && ~pause && ~$past(iack) |=> (CurrState == `IRQ));

   property back_to_idle(state);
      @(posedge clk)
        disable iff(~rst)
          (CurrState == state) && ~pause |=> (CurrState == `IDLE);
   endproperty

   irq_to_idle : assert property(back_to_idle(`IRQ));
   ret_to_idle : assert property(back_to_idle(`RET));
   rst_to_idle : assert property(back_to_idle(`RST));
   ld_to_idle : assert property(back_to_idle(`LD));

   cur_to_noi :
     assert property(
                     @(posedge clk)
                     disable iff(~rst)
                     (CurrState == `CUR) && ~pause |=> (CurrState == `NOI));


   // Assumption
   assume property  (@(posedge clk) (CurrState == `RST)||(CurrState == `IDLE) || (CurrState == `CUR) |-> ~pause[*2]);


endmodule // assert_ctl_fsm

bind ctl_FSM assert_ctl_fsm chk_ctl_fsm(.*);


   
