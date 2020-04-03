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
	    ErrCntAssertions = 0;
	end

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
    endsequence

	sequence Rx_zero;
	    !Rx ##1 Rx [*5] ##1 !Rx;
	endsequence

	sequence Rx_DataZero;
        ( Rx_Data ==? 8'b111110xx) or
        ( Rx_Data ==? 8'bx111110x) or
        ( Rx_Data ==? 8'bxx111110) or
        ((Rx_Data ==? 8'bxxx11111) && ($past(Rx_Data, 8) ==? 8'b0xxxxxxx)) or
        ((Rx_Data ==? 8'bxxxx1111) && ($past(Rx_Data, 8) ==? 8'b10xxxxxx)) or
        ((Rx_Data ==? 8'bxxxxx111) && ($past(Rx_Data, 8) ==? 8'b110xxxxx)) or
        ((Rx_Data ==? 8'bxxxxxx11) && ($past(Rx_Data, 8) ==? 8'b1110xxxx)) or
        ((Rx_Data ==? 8'bxxxxxxx1) && ($past(Rx_Data, 8) ==? 8'b11110xxx));
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

    sequence Tx_zero;
        !Tx ##1 Tx [*5] ##1 !Tx;
    endsequence

    sequence Tx_DataZero;
        ( Tx_Data ==? 8'b111110xx) or
        ( Tx_Data ==? 8'bx111110x) or
        ( Tx_Data ==? 8'bxx111110) or
        ((Tx_Data ==? 8'bxxx11111) && ($past(Tx_Data, 8) ==? 8'b0xxxxxxx)) or
        ((Tx_Data ==? 8'bxxxx1111) && ($past(Tx_Data, 8) ==? 8'b10xxxxxx)) or
        ((Tx_Data ==? 8'bxxxxx111) && ($past(Tx_Data, 8) ==? 8'b110xxxxx)) or
        ((Tx_Data ==? 8'bxxxxxx11) && ($past(Tx_Data, 8) ==? 8'b1110xxxx)) or
        ((Tx_Data ==? 8'bxxxxxxx1) && ($past(Tx_Data, 8) ==? 8'b11110xxx));
    endsequence

	/*******************************************
	*                Properties               *
	*******************************************/

	// 3. Correct bits set in RX status/control register after receiving frame.
	property p_Rx_Status;
	    @(posedge Clk) disable iff(!Rst) $rose(Rx_EoF) |->
		    if (Rx_FrameError)
			    !Rx_Ready && !Rx_Overflow && !Rx_AbortSignal &&  Rx_FrameError
		    else if (Rx_AbortSignal && Rx_Overflow)
			     Rx_Ready &&  Rx_Overflow &&  Rx_AbortSignal &&  Rx_FrameError
		    else if (Rx_AbortSignal)
			     Rx_Ready && !Rx_Overflow &&  Rx_AbortSignal && !Rx_FrameError
		    else if (Rx_Overflow)
			     Rx_Ready &&  Rx_Overflow && !Rx_AbortSignal && !Rx_FrameError
		    else
			     Rx_Ready && !Rx_Overflow && !Rx_AbortSignal && !Rx_FrameError
    endproperty

	// 5. Start and end of frame pattern generation.
	// Not checked
	property p_Tx_FramePattern;
	    @(posedge Clk) disable iff (!Rst) !$stable(Tx_ValidFrame) && $past(Tx_AbortFrame, 2) |-> Tx_flag;
	endproperty

	property p_Rx_FramePattern;
	    @(posedge Clk) Rx_flag |-> ##2 Rx_FlagDetect;
	endproperty

	// 6. Zero insertion and removal of transparent transmission.
    // Not checked
	property p_Tx_InsertZero;
        @(posedge Clk) disable iff (!Rst) $rose(Tx_NewByte) ##0 Tx_DataZero |-> ##[13:20] Tx_zero;
	endproperty

	property p_Rx_RemoveZero;
	    @(posedge Clk) disable iff (!Rst) (Rx_zero and Rx_ValidFrame [*6]) |-> ##[9:17] Rx_NewByte ##1 Rx_DataZero;
	endproperty

	// 7. Idle pattern generation and checking
	// Not checked
	property p_Tx_IdlePattern;
	    @(posedge Clk) disable iff (!Rst) !Tx_ValidFrame && Tx_FrameSize == 8'b0 |-> Tx_idle;
	endproperty

	property p_Rx_IdlePattern;
	      @(posedge Clk) disable iff (!Rst) Rx_idle |=> !Rx_FlagDetect; 
	endproperty

	// 8. Abort pattern generation and checking.
	// Not checked
	property p_Tx_AbortPattern;
	    @(posedge Clk) disable iff (!Rst) $rose(Tx_AbortFrame) |-> ##3 Tx_abort;
	endproperty

	property p_Rx_AbortPattern;
	    @(posedge Clk) disable iff (!Rst) Rx_abort and (!Rx_ValidFrame [*7]) |-> ##2 $rose(Rx_AbortDetect);
	endproperty

	// 9. When aborting frame during transmission, Tx_AbortedTrans should be asserted
	// Not checked
	property p_Tx_AbortSignal;
	    @(posedge Clk) disable iff (!Rst) $rose(Tx_AbortFrame) && Tx_DataAvail |-> Tx_AbortedTrans;
	endproperty

	// 10. Abort pattern detected during valid frame should generate Rx_AbortSignal
	property p_Rx_AbortSignal;
	    @(posedge Clk) disable iff (!Rst) Rx_ValidFrame && Rx_AbortDetect |=> Rx_AbortSignal;
	endproperty

	// 12. When a whole RX frame has been received, check if end of frame is generated
	property p_Rx_EndOfFrame;
	    @(posedge Clk) disable iff (!Rst) $fell(Rx_ValidFrame) |=> $rose(Rx_EoF);
	endproperty

	// 13. When receiving more than 128 bytes, Rx_Overflow should be asserted
	property p_Rx_Overflow;
	    @(posedge Clk) disable iff (!Rst || !Rx_ValidFrame)  $rose(Rx_ValidFrame) ##0 ($rose(Rx_NewByte) [->129]) |=> $rose(Rx_Overflow)
	endproperty

    // 14. Rx_FrameSize should equal the number of bytes received in a frame.
	property p_Rx_FrameSize;
	    int bytes = 0;
	    @(posedge Clk) disable iff (!Rst) $rose(Rx_ValidFrame) ##0 ((##[7:9] $rose(Rx_NewByte), bytes++) [*1:128]) ##5 $rose(Rx_EoF) |=> Rx_FrameSize == (bytes - 2);
	endproperty

	// 15. Rx_Ready should indicate byte(s) in RX Buffer is ready to be read
	property p_Rx_Ready;
	    @(posedge Clk) disable iff (!Rst) $rose(Rx_Ready) |-> $rose(Rx_EoF) and !Rx_ValidFrame;
	endproperty

	// 16. Non-byte aligned data or errors in FCS checking should result in frame error
	// Not checked
	property p_Rx_FCSerr;
	    @(posedge Clk) disable iff (!Rst) $rose(Rx_FCSerr) && Rx_FCSen |=> $rose(Rx_FrameError);
	endproperty

    // 17. Tx_Done should be asserted when entire TX buffer has been read for transmission
	// Not checked
	property p_Tx_Done;
	    @(posedge Clk) disable iff (!Rst) $fell(Tx_DataAvail) |-> $past(Tx_Done, 1);
	endproperty

	// 18. Tx_Full should be asserted after writing 126 or more bytes to the TX buffer (overflow)
	// Not checked
	property p_Tx_Full;
        @(posedge Clk) disable iff (!Rst) $fell(Tx_Done) ##0 (($rose(Tx_WrBuff) [->1]) [*125:$]) ##0 !Tx_Done |-> Tx_Full;
	endproperty

	/********************************************
	*                Assertions                *
	********************************************/

	Rx_Status_Assert : assert property (p_Rx_Status) begin
	    $display("PASS: Status/Control Register correct");
	end else begin
		$error("Status/Control Register not set correctly");
		ErrCntAssertions++;
	end

	Tx_FramePattern_Assert : assert property (p_Tx_FramePattern) begin
	    $display("PASS: Flag detected on transmission side");
	end else begin
	    $display("FAIL: Flag not detected on transmission side");
	    ErrCntAssertions++;
	end

	Rx_FramePattern_Assert : assert property (p_Rx_FramePattern) begin
	    $display("PASS: Flag detected on receive side");
	end else begin 
	    $error("FAIL: Flag no detected on receive side"); 
	    ErrCntAssertions++; 
	end

	Tx_InsertZero_Assert : assert property (p_Tx_InsertZero) begin
	    $display("PASS: Zero insertion successful");
	end else begin
	    $error("FAIL: Zero insertion not detected");
	    ErrCntAssertions++;
	end

	Rx_RemoveZero_Assert : assert property (p_Rx_RemoveZero) begin
	    $display("PASS: Zero removal successful - Rx_Data=0b%b_%b", Rx_Data, $past(Rx_Data, 8));
	end else begin
	    $error("FAIL: Zero removal not detected, Rx_Data=0b%b_%b", Rx_Data, $past(Rx_Data, 8));
	    ErrCntAssertions++;
	end

	Tx_IdlePattern_Assert : assert property (p_Tx_IdlePattern) else begin
	    $error("FAIL: Idle pattern not detected on transmitting side");
	    ErrCntAssertions++;
	end

	Rx_IdlePattern_Assert : assert property (p_Rx_IdlePattern) else begin
	    $error("FAIL: Idle pattern not detected on receiving side");
	    ErrCntAssertions++;
	end

	Tx_AbortPattern_Assert : assert property (p_Tx_AbortPattern) begin
	    $display("PASS: Abort pattern generated");
	end else begin
	    $error("FAIL: Abort pattern not generated");
	    ErrCntAssertions++;
	end

	Rx_AbortPattern_Assert : assert property (p_Rx_AbortPattern) begin
	    $display("PASS: Abort pattern received");
	end else begin
	    $error("FAIL: Abort pattern not received");
	    ErrCntAssertions++;
	end

	Tx_AbortSignal_Assert : assert property (p_Tx_AbortSignal) begin
	    $display("PASS: Tx_AbortedTrans asserted");
	end else begin
	    $error("FAIL: Tx_AbortedTrans wasn't asserted");
	    ErrCntAssertions++;
	end

	Rx_AbortSignal_Assert : assert property (p_Rx_AbortSignal) begin
	    $display("PASS: Abort signal");
	end else begin 
	    $error("FAIL: AbortSignal did not go high after AbortDetect during validframe"); 
	    ErrCntAssertions++; 
	end

	Rx_EoF_Assert : assert property (p_Rx_EndOfFrame) begin
	    $display("PASS: Rx_EoF asserted");
	end else begin
	    $error("FAIL: Rx_EoF not asserted");
	    ErrCntAssertions++;
	end

	Rx_Overflow_Assert : assert property (p_Rx_Overflow) begin
	    $display("PASS: Rx_Overflow is high after receiving more than 128 bytes");
    end else begin
	    $error("FAIL: Rx_Overflow not asserted after receiving more than 128 bytes");
	    ErrCntAssertions++;
	end

	Rx_FrameSize_Assert : assert property (p_Rx_FrameSize) begin
	    $display("PASS: #frames received equals Rx_FrameSize");
	end else begin
	    $error("FAIL: #frames received does not equal Rx_FrameSize");
	    ErrCntAssertions++;
	end

	Rx_Ready_Assert : assert property (p_Rx_Ready) begin
	    $display("PASS: Rx_Ready asserted signals data to be read");
	end else begin
	    $error("FAIL: Rx_Ready asserted, but data isn't ready yet");
	    ErrCntAssertions++;
	end

	Rx_FCSerr_Assert : assert property (p_Rx_FCSerr) begin
	    $display("PASS: Frame error detected");
	end else begin
	    $error("FAIL: Frame error not detected");
	    ErrCntAssertions++;
	end

	Tx_Done_Assert : assert property (p_Tx_Done) begin
	    $display("PASS: Tx_Done asserted");
	end else begin
	    $error("FAIL: Tx_Done did not become asserted");
	    ErrCntAssertions++;
	end

	Tx_Full_Assert : assert property (p_Tx_Full) begin
	    $display("PASS: Tx_Full asserted");
	end else begin
	    $error("FAIL: Tx_Full did not become asserted");
	    ErrCntAssertions++;
	end

endmodule
