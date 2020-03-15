//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:  
// Date:    
//////////////////////////////////////////////////

/* The assertions_hdlc module is a test module containing the concurrent
   assertions. It is used by binding the signals of assertions_hdlc to the
   corresponding signals in the test_hdlc testbench. This is already done in
   bind_hdlc.sv 

   For this exercise you will write concurrent assertions for the Rx module:
   - Verify that Rx_FlagDetect is asserted two cycles after a flag is received
   - Verify that Rx_AbortSignal is asserted after receiving an abort flag
*/

module assertions_hdlc (
  output int   ErrCntAssertions,
  input  logic Clk,
  input  logic Rst,
  input  logic Rx,
  input  logic Rx_FlagDetect,
  input  logic Rx_ValidFrame,
  input  logic Rx_AbortDetect,
  input  logic Rx_AbortSignal,
  input  logic Rx_Overflow,
  input  logic Rx_WrBuff
);

  initial begin
    ErrCntAssertions  =  0;
  end

    /*
    * 1.    Correct data in RX buffer according to RX input.
    *       The buffer should contain up to 128 bytes (this
    *       includes the 2 FCS bytes, but not the flags).
    * 2.    Attempting to read RX buffer after aborted frame,
    *       frame error or dropped frame should result in zeros.
    * 3.    Correct bits set in RX status/control register after
    *       receiving frame. Remember to check all bits, i.e. after
    *       an aborted the Rx_Overflow bit should be 0, unless an
    *       overflow also occured.
    * 4.    Correct TX output according to written TX buffer.
    * 5.    Start and end of frame pattern generation (Start and 
    *       end flag: 0111_1110).
    * 6.    Zero insertion and removal of transparent transmission.
    * 7.    idle pattern generation and checking (1111_1111 when not
    *       operating).
    * 8.    Abort pattern generation and checking (1111_110). Remember
    *       that the 0 must be sent first.
    * 9.    When aborting frame during transmission, Tx_AbortedTrans
    *       should be asserted.
    * 10.   Abort pattern detected during valid frame should generate
    *       Rx_AbortSignal.
    * 11.   CRC generation and checking.
    * 12.   When a whole RX frame has been received, check if end of frame
    *       is generated.
    * 13.   When receiving more than 128 bytes, Rx_Overflow should be asserted.
    * 14.   Rx_FrameSize should equal the number of bytes received in a frame
    *       (max 126 bytes = 128 bytes in buffer - 2 FCS byter).
    * 15.   Rx_Ready should indicate byte(s) in RX buffer is ready to  be read.
    * 16.   Non-byte aligned data or error in FCS checking should result
    *       in frame error.
    * 17.   Tx_Done should be asserted when the entire TX buffer has
    *       been read for transmission.
    * 18.   Tx_Full should be asserted after writing 126 or more bytes
    *       to the TX buffer (overflow).
    */

  /*******************************************
   *  Verify correct Rx_FlagDetect behavior  *
   *******************************************/

  sequence Rx_flag;
    $past(!Rx, 7) && $past(Rx, 6) && $past(Rx, 5) && $past(Rx, 4) && $past(Rx, 3) && $past(Rx, 2) && $past(Rx, 1) && !Rx; // Added by Morten
  endsequence

  // Check if flag sequence is detected
  property RX_FlagDetect;
    @(posedge Clk) Rx_flag |-> ##2 Rx_FlagDetect;
  endproperty

  RX_FlagDetect_Assert : assert property (RX_FlagDetect) begin
    $display("PASS: Flag detect");
  end else begin 
    $error("Flag sequence did not generate FlagDetect"); 
    ErrCntAssertions++; 
  end

  /********************************************
   *  Verify correct Rx_AbortSignal behavior  *
   ********************************************/

  //If abort is detected during valid frame. then abort signal should go high
  property RX_AbortSignal;
    @(posedge Clk) Rx_ValidFrame && Rx_AbortDetect |=> Rx_AbortSignal; // Added by Morten
  endproperty

  RX_AbortSignal_Assert : assert property (RX_AbortSignal) begin
    $display("PASS: Abort signal");
  end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
  end

endmodule
