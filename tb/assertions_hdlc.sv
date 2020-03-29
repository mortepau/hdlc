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
  output int                ErrCntAssertions,
  input  logic              Clk,
  input  logic              Rst,
  input  logic [2:0]        Address,
  input  logic              WriteEnable,
  input  logic              ReadEnable,
  input  logic [7:0]        DataIn,
  input  logic [7:0]        DataOut,
  input  logic              Rx,
  input  logic              RxEN,
  input  logic              Rx_Ready,
  input  logic              Rx_ValidFrame,
  input  logic              Rx_WrBuff,
  input  logic              Rx_EoF,
  input  logic              Rx_AbortSignal,
  input  logic              Rx_StartZeroDetect,
  input  logic              Rx_FrameError,
  input  logic              Rx_StartFCS,
  input  logic              Rx_StopFCS,
  input  logic [7:0]        Rx_Data,
  input  logic              Rx_NewByte,
  input  logic              Rx_FlagDetect,
  input  logic              Rx_AbortDetect,
  input  logic              RxD,
  input  logic              Rx_FCSerr,
  input  logic [7:0]        Rx_FrameSize,
  input  logic              Rx_Overflow,
  input  logic [7:0]        Rx_DataBuffOut,
  input  logic              Rx_FCSen,
  input  logic              Rx_RdBuff,
  input  logic              Rx_Drop,
  input  logic              Tx,
  input  logic              TxEN,
  input  logic              Tx_Done,
  input  logic              Tx_ValidFrame,
  input  logic              Tx_AbortedTrans,
  input  logic              Tx_WriteFCS,
  input  logic              Tx_InitZero,
  input  logic              Tx_StartFCS,
  input  logic              Tx_RdBuff,
  input  logic              Tx_NewByte,
  input  logic              Tx_FCSDone,
  input  logic [7:0]        Tx_Data,
  input  logic              Tx_Full,
  input  logic              Tx_DataAvail,
  input  logic [7:0]        Tx_FrameSize,
  input  logic [127:0][7:0] Tx_DataArray,
  input  logic [7:0]        Tx_DataOutBuff,
  input  logic              Tx_WrBuff,
  input  logic              Tx_Enable,
  input  logic [7:0]        Tx_DataInBuff,
  input  logic              Tx_AbortFrame
);

  initial begin
    ErrCntAssertions  =  0;
  end

    /*
    * 1I.    Correct data in RX buffer according to RX input.
    *       The buffer should contain up to 128 bytes (this
    *       includes the 2 FCS bytes, but not the flags).
    * 2I.    Attempting to read RX buffer after aborted frame,
    *       frame error or dropped frame should result in zeros.
    * 3.    Correct bits set in RX status/control register after
    *       receiving frame. Remember to check all bits, i.e. after
    *       an aborted the Rx_Overflow bit should be 0, unless an
    *       overflow also occured.
    * 4IT.    Correct TX output according to written TX buffer.
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
    * 11I.   CRC generation and checking.
    * 12.   When a whole RX frame has been received, check if end of frame
    *       is generated.
    * 13.   When receiving more than 128 bytes, Rx_Overflow should be asserted.
    * 14I.   Rx_FrameSize should equal the number of bytes received in a frame
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
   *                Sequences                *
   *******************************************/

  /***********************
   *         Rx          *
   ***********************/

  sequence Rx_idle;
    Rx [*8];
  endsequence;

  sequence Rx_flag;
    !Rx ##1 Rx [*6] ##1 !Rx; 
  endsequence

  sequence Rx_abort;
    !Rx ##1 Rx [*7];
  endsequence;

  sequence Rx_zeroInsert;
      $rose(Rx) ##1 Rx [*4] ##1 !Rx;
  endsequence

  /***********************
   *         Tx          *
   **********************/

  sequence Tx_idle;
    Tx [*8];
  endsequence

  sequence Tx_flag;
    !Tx ##1 Tx [*6] ##1 !Tx;
  endsequence

  sequence Tx_abort;
    !Tx ##1 Tx [*7];
  endsequence

  /*******************************************
   *                Properties               *
   *******************************************/

  // Check if flag sequence is detected
  property p_Rx_FlagDetect;
    @(posedge Clk) Rx_flag |-> ##2 Rx_FlagDetect;
  endproperty

  //If abort is detected during valid frame. then abort signal should go high
  property p_Rx_AbortSignal;
    @(posedge Clk) Rx_ValidFrame && Rx_AbortDetect |=> Rx_AbortSignal; // Added by Morten
  endproperty

  // 3. Correct bits set in RX status/control register after receiving frame.
  property p_Rx_Status;
    @(posedge Clk) disable iff(!Rst) $rose(Rx_EoF) |->
      if (Rx_FrameError)
        !Rx_Ready && !Rx_Overflow && !Rx_AbortSignal &&  Rx_FrameError
      else if (Rx_AbortSignal)
         Rx_Ready && !Rx_Overflow &&  Rx_AbortSignal && !Rx_FrameError
      else if (Rx_Overflow)
         Rx_Ready &&  Rx_Overflow && !Rx_AbortSignal && !Rx_FrameError
      else
         Rx_Ready && !Rx_Overflow && !Rx_AbortSignal && !Rx_FrameError
  endproperty

  // 5. Start and end of frame pattern generation.
  property p_Tx_FramePattern;
    @(posedge Clk) disable iff (!Rst) !$stable(Tx_ValidFrame) && $past(Tx_AbortFrame, 2) |-> Tx_flag;
  endproperty

  // 6. Zero insertion and removal of transparent transmission.
  /* property p_Tx_InsertZero; */
  /*   @(posedge Clk) disable iff (!Rst || !Rx_ValidFrame) Rx_zeroInsert |=> ##[0:2] Rx_NewByte ##0 (Rx_Data == 8'bxxx11111 || Rx_Data == 8'bxx11111x || Rx_Data == 8'bx11111xx || Rx_Data == 8'b11111xxx) */
  /* endproperty */

  property p_Rx_RemoveZero;
    @(posedge Clk) disable iff (!Rst || !Rx_ValidFrame) Rx_zeroInsert |=> ##[0:2] (Rx_Data[4:0] == 5'b11111 or Rx_Data[5:1] == 5'b11111 or Rx_Data[6:2] == 5'b11111 or Rx_Data[7:3] ==? 5'b11111)
  endproperty

  /********************************************
   *                Assertions                *
   ********************************************/

  Rx_FlagDetect_Assert : assert property (p_Rx_FlagDetect) begin
    $display("PASS: Flag detect");
  end else begin 
    $error("Flag sequence did not generate FlagDetect"); 
    ErrCntAssertions++; 
  end

  RX_AbortSignal_Assert : assert property (p_Rx_AbortSignal) begin
    $display("PASS: Abort signal");
  end else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe"); 
    ErrCntAssertions++; 
  end

  Rx_Status_Assert : assert property (p_Rx_Status) begin
    $display("PASS: Status/Control Register correct");
  end else begin
      $error("Status/Control Register not set correctly");
      ErrCntAssertions++;
  end

  Tx_FramePattern_Assert : assert property (p_Tx_FramePattern) begin
    $display("PASS: Start/End frame detected");
  end else begin
    $display("Start/End frame not detected");
    ErrCntAssertions++;
  end

  /* Tx_InsertZero_Assert : assert property (p_Tx_InsertZero) begin */
  /*   $display("PASS: Zero insertion successful"); */
  /* end else begin */
  /*   $error("Zero insertion not detected"); */
  /*   ErrCntAssertions++; */
  /* end */

  Rx_RemoveZero_Assert : assert property (p_Rx_RemoveZero) begin
    $display("PASS: Zero removal successful");
  end else begin
    $error("Zero removal not detected, Rx_Data=0x%h", Rx_Data);
    ErrCntAssertions++;
  end

endmodule
