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

	sequence idle(signal);
	    signal [*8];
	endsequence;

	sequence flag(signal);
	    !signal ##1 signal [*6] ##1 !signal; 
	endsequence

	sequence abort(signal);
	    !signal ##1 signal [*7];
    endsequence

	sequence zero(signal);
	    !signal ##1 signal [*5] ##1 !signal;
	endsequence

	sequence Rx_DataZero;
        ( Rx_Data ==? 8'b11111xxx) or
        ( Rx_Data ==? 8'bx11111xx) or
        ( Rx_Data ==? 8'bxx11111x) or
        ( Rx_Data ==? 8'bxxx11111) or
        ((Rx_Data ==? 8'bxxxx1111) && ($past(Rx_Data, 8) ==? 8'b1xxxxxxx)) or
        ((Rx_Data ==? 8'bxxxxx111) && ($past(Rx_Data, 8) ==? 8'b11xxxxxx)) or
        ((Rx_Data ==? 8'bxxxxxx11) && ($past(Rx_Data, 8) ==? 8'b111xxxxx)) or
        ((Rx_Data ==? 8'bxxxxxxx1) && ($past(Rx_Data, 8) ==? 8'b1111xxxx));
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
			     Rx_Ready &&  Rx_Overflow &&  Rx_AbortSignal & !Rx_FrameError
		    else if (Rx_AbortSignal)
			     Rx_Ready && !Rx_Overflow &&  Rx_AbortSignal && !Rx_FrameError
		    else if (Rx_Overflow)
			     Rx_Ready &&  Rx_Overflow && !Rx_AbortSignal && !Rx_FrameError
		    else
			     Rx_Ready && !Rx_Overflow && !Rx_AbortSignal && !Rx_FrameError
    endproperty

	// 5. Start and end of frame pattern generation.
	property p_Tx_FramePattern;
	    @(posedge Clk) disable iff (!Rst) !$stable(Tx_ValidFrame) ##0 $past(!Tx_AbortFrame, 2) |-> ##[1:2] flag(Tx);
	endproperty

	property p_Rx_FramePattern;
	    @(posedge Clk) flag(Rx) |-> ##2 Rx_FlagDetect;
	endproperty

	// 6. Zero insertion and removal of transparent transmission.
	property p_Tx_InsertZero;
        @(posedge Clk) disable iff (!Rst || !Tx_ValidFrame) $rose(Tx_NewByte) ##0 Tx_DataZero |-> ##[13:22] zero(Tx);
	endproperty

	property p_Rx_RemoveZero;
	    @(posedge Clk) disable iff (!Rst) (zero(Rx) and Rx_ValidFrame [*6]) |-> ##[9:17] Rx_NewByte ##1 Rx_DataZero;
	endproperty

	// 7. Idle pattern generation and checking
	property p_Tx_IdlePattern;
	    @(posedge Clk) disable iff (!Rst) !Tx_ValidFrame && Tx_FrameSize == 8'b0 |-> idle(Tx);
	endproperty

	property p_Rx_IdlePattern;
	      @(posedge Clk) disable iff (!Rst) idle(Rx) |=> !Rx_FlagDetect; 
	endproperty

	// 8. Abort pattern generation and checking.
	property p_Tx_AbortPattern;
	    @(posedge Clk) disable iff (!Rst) $rose(Tx_AbortFrame) |-> ##4 abort(Tx);
	endproperty

	property p_Rx_AbortPattern;
	    @(posedge Clk) disable iff (!Rst) abort(Rx) and (!Rx_ValidFrame [*7]) |-> ##2 $rose(Rx_AbortDetect);
	endproperty

	// 9. When aborting frame during transmission, Tx_AbortedTrans should be asserted
	property p_Tx_AbortSignal;
	    @(posedge Clk) disable iff (!Rst) $rose(Tx_AbortFrame) && Tx_DataAvail ##1 $fell(Tx_AbortFrame) |=>  $rose(Tx_AbortedTrans);
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
	    @(posedge Clk) disable iff (!Rst) $rose(Rx_ValidFrame) ##0 ((##[7:9] $rose(Rx_NewByte), bytes++) [*1:128]) ##5 ($rose(Rx_EoF) and !Rx_FrameError) |=> Rx_FrameSize == (bytes - 2);
	endproperty

	// 15. Rx_Ready should indicate byte(s) in RX Buffer is ready to be read
	property p_Rx_Ready;
	    @(posedge Clk) disable iff (!Rst) $rose(Rx_Ready) |-> $rose(Rx_EoF) and !Rx_ValidFrame;
	endproperty

	// 16. Non-byte aligned data or errors in FCS checking should result in frame error
	property p_Rx_FCSerr;
	    @(posedge Clk) disable iff (!Rst) $rose(Rx_FCSerr) && Rx_FCSen |=> $rose(Rx_FrameError);
	endproperty

    // 17. Tx_Done should be asserted when entire TX buffer has been read for transmission
	property p_Tx_Done;
	    @(posedge Clk) disable iff (!Rst) $fell(Tx_DataAvail) |-> $past(Tx_Done, 1);
	endproperty

	// 18. Tx_Full should be asserted after writing 126 or more bytes to the TX buffer (overflow)
	property p_Tx_Full;
        @(posedge Clk) disable iff (!Rst) $fell(Tx_Done) ##0 (($rose(Tx_WrBuff) [->1]) [*125]) ##0 !Tx_Done |=> Tx_Full;
	endproperty

	/********************************************
	*                Assertions                *
	********************************************/

	Rx_Status_Assert : assert property (p_Rx_Status) begin
	    $display("PASS: Rx_SC correct");
	end else begin
		$error("FAIL: Rx_SC incorrect");
		ErrCntAssertions++;
	end

	Tx_FramePattern_Assert : assert property (p_Tx_FramePattern) begin
	    $display("PASS: Flag sent");
	end else begin
	    $error("FAIL: Flag not sent");
	    ErrCntAssertions++;
	end

	Rx_FramePattern_Assert : assert property (p_Rx_FramePattern) begin
	    $display("PASS: Flag received");
	end else begin 
	    $error("FAIL: Flag not received"); 
	    ErrCntAssertions++; 
	end

	Tx_InsertZero_Assert : assert property (p_Tx_InsertZero) begin
	    $display("PASS: Zero inserted");
	end else begin
	    $error("FAIL: Zero not inserted");
	    ErrCntAssertions++;
	end

	Rx_RemoveZero_Assert : assert property (p_Rx_RemoveZero) begin
        $display("PASS: Zero removed");
	end else begin
        $error("FAIL: Zero not removed");
	    ErrCntAssertions++;
	end

	Tx_IdlePattern_Assert : assert property (p_Tx_IdlePattern) else begin
	    $error("FAIL: Idle pattern not transmitted");
	    ErrCntAssertions++;
	end

	Rx_IdlePattern_Assert : assert property (p_Rx_IdlePattern) else begin
	    $error("FAIL: Idle pattern not received");
	    ErrCntAssertions++;
	end

	Tx_AbortPattern_Assert : assert property (p_Tx_AbortPattern) begin
	    $display("PASS: Abort transmitted");
	end else begin
	    $error("FAIL: Abort not transmitted");
	    ErrCntAssertions++;
	end

	Rx_AbortPattern_Assert : assert property (p_Rx_AbortPattern) begin
	    $display("PASS: Abort received");
	end else begin
	    $error("FAIL: Abort not received");
	    ErrCntAssertions++;
	end

	Tx_AbortSignal_Assert : assert property (p_Tx_AbortSignal) begin
	    $display("PASS: Tx_AbortedTrans asserted");
	end else begin
	    $error("FAIL: Tx_AbortedTrans not asserted");
	    ErrCntAssertions++;
	end

	Rx_AbortSignal_Assert : assert property (p_Rx_AbortSignal) begin
	    $display("PASS: Rx_AbortSignal asserted");
	end else begin 
	    $error("FAIL: Rx_AbortSignal not asserted"); 
	    ErrCntAssertions++; 
	end

	Rx_EoF_Assert : assert property (p_Rx_EndOfFrame) begin
	    $display("PASS: Rx_EoF asserted");
	end else begin
	    $error("FAIL: Rx_EoF not asserted");
	    ErrCntAssertions++;
	end

	Rx_Overflow_Assert : assert property (p_Rx_Overflow) begin
	    $display("PASS: Rx_Overflow asserted");
    end else begin
	    $error("FAIL: Rx_Overflow not asserted");
	    ErrCntAssertions++;
	end

	Rx_FrameSize_Assert : assert property (p_Rx_FrameSize) begin
	    $display("PASS: Rx_FrameSize correct");
	end else begin
	    $error("FAIL: Rx_FrameSize incorrect");
	    ErrCntAssertions++;
	end

	Rx_Ready_Assert : assert property (p_Rx_Ready) begin
	    $display("PASS: Data ready");
	end else begin
	    $error("FAIL: Data not ready");
	    ErrCntAssertions++;
	end

	Rx_FCSerr_Assert : assert property (p_Rx_FCSerr) begin
	    $display("PASS: Rx_FrameError asserted");
	end else begin
	    $error("FAIL: Rx_FrameError not asserted");
	    ErrCntAssertions++;
	end

	Tx_Done_Assert : assert property (p_Tx_Done) begin
	    $display("PASS: Tx_Done asserted");
	end else begin
	    $error("FAIL: Tx_Done not asserted");
	    ErrCntAssertions++;
	end

	Tx_Full_Assert : assert property (p_Tx_Full) begin
	    $display("PASS: Tx_Full asserted");
	end else begin
	    $error("FAIL: Tx_Full not asserted");
	    ErrCntAssertions++;
	end

endmodule
