//////////////////////////////////////////////////
// Title:	 testPr_hdlc
// Author: 
// Date:	
//////////////////////////////////////////////////

/* testPr_hdlc contains the simulation and immediate assertion code of the
	 testbench. 

	 For this exercise you will write immediate assertions for the Rx module which
	 should verify correct values in some of the Rx registers for:
	 - Normal behavior
	 - Buffer overflow 
	 - Aborts

	 HINT:
	 - A ReadAddress() task is provided, and addresses are documentet in the 
	   HDLC Module Design Description
*/

program testPr_hdlc(
    in_hdlc uin_hdlc
);
	
    int TbErrorCnt;

    /****************************************************************************
	 *                                                                          *
	 *                               Student code                               *
	 *                                                                          *
	 ****************************************************************************/
	
    logic [2:0] TXSC   = 3'b000,
	            TXBUFF = 3'b001, 
	            RXSC   = 3'b010, 
	            RXBUFF = 3'b011, 
	            RXLEN  = 3'b100; 
	logic [7:0] RXSC_READ_MASK = 8'b11011101;

    // VerifyNormalReceive should verify correct value in the Rx status/control register
    task VerifyNormalReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData, DataLen;
	    wait(uin_hdlc.Rx_Ready);

	    // Assert that only Rx_Ready is set
	    ReadAddress(RXSC, ReadData);
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h01) $display("PASS: VerifyNormalReceive:: Data ready");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyNormalReceive:: Expected Rx_SC = 0x01, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert content is valid
	    ReadAddress(RXLEN, DataLen);
	    for (int i = 0; i < DataLen; i++) begin
	        ReadAddress(RXBUFF, ReadData);
	        assert(ReadData == data[i]) else begin
	            TbErrorCnt++;
	            $display("FAIL: VerifyNormalReceive:: Expected ReadData[%0d] = 0x%h, Received ReadData[%0d] = 0x%h", i, data[i], i, ReadData);
	        end
	    end
	endtask

	// VerifyOverflowReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after overflow.
	task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData, DataLen;
	    wait(uin_hdlc.Rx_Ready);

	    // Assert that only Rx_Ready is set
	    ReadAddress(RXSC, ReadData);
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h11) 
            $display("PASS: VerifyOverflowReceive:: Data ready");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyOverflowReceive:: Expected Rx_SC = 0x11, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert content is valid
	    ReadAddress(RXLEN, DataLen);
	    for (int i = 0; i < DataLen; i++) begin
	        ReadAddress(RXBUFF, ReadData);
	        assert(ReadData == data[i]) else begin
	            TbErrorCnt++;
	            $display("FAIL: VerifyOverflowReceive:: Expected ReadData[%0d] = 0x%h, Received ReadData[%0d] = 0x%h", i, data[i], i, ReadData);
	        end
	    end
	    // Read a few times extra to assert the output is zero
	    ReadAddress(RXBUFF, ReadData);
	    assert(ReadData == 8'b0) 
            $display("PASS: VerifyOverflowReceive:: OverflowData = 0x00");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyOverflowReceive:: Expected ReadData = 0x00, Received ReadData = 0x%h", ReadData);
	    end
	    ReadAddress(RXBUFF, ReadData);
	    assert(ReadData == 8'b0)
            $display("PASS: VerifyOverflowReceive:: OverflowData = 0x00");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyOverflowReceive:: Expected ReadData = 0x00, Received ReadData = 0x%h", ReadData);
	    end
	    ReadAddress(RXBUFF, ReadData);
	    assert(ReadData == 8'b0)
            $display("PASS: VerifyOverflowReceive:: OverflowData = 0x00");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyOverflowReceive:: Expected ReadData = 0x00, Received ReadData = 0x%h", ReadData);
	    end
    endtask

	// VerifyAbortReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after abort.
	task VerifyAbortReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_AbortSignal is set
	    ReadAddress(RXSC, ReadData);
	    // Mask the Write-Only bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h08)
            $display("PASS: VerifyAbortReceive:: Abort received");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyAbortReceive:: Abort not received, Expected Rx_SC = 0x08, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is 0
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyAbortReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyAbortReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    end
	endtask

	// VerifyAbortReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after abort.
	// TODO: Check
	task VerifyDropReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_AbortSignal is set
	    ReadAddress(RXSC, ReadData);
	    // Mask the Write-Only bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h08)
            $display("PASS: VerifyAbortReceive:: Abort received");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyAbortReceive:: Abort not received, Expected Rx_SC = 0x08, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is 0
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyAbortReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyAbortReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    end
	endtask

	// VerifyAbortReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after abort.
	// TODO: Check
	task VerifyNonByteAlignedReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_AbortSignal is set
	    ReadAddress(RXSC, ReadData);
	    // Mask the Write-Only bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h08)
            $display("PASS: VerifyAbortReceive:: Abort received");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyAbortReceive:: Abort not received, Expected Rx_SC = 0x08, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is 0
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyAbortReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyAbortReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    end
	endtask

	// VerifyFrameErrorReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after frameError.
	// TODO: Check
	task VerifyFCSErrReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_FrameError is set
	    ReadAddress(RXSC, ReadData);
	    // Mask the Write-Only bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h04)
            $display("PASS: VerifyFrameErrorReceive:: FrameError received");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyFrameErrorReceive:: FrameError not received, Expected Rx_SC = 0x08, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is 0
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyFrameErrorReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyFrameErrorReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    end
	endtask

	// VerifyFrameErrorReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after frameError.
	// TODO: Check
	task VerifyFrameErrorReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_FrameError is set
	    ReadAddress(RXSC, ReadData);
	    // Mask the Write-Only bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == 'h04)
            $display("PASS: VerifyFrameErrorReceive:: FrameError received");
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyFrameErrorReceive:: FrameError not received, Expected Rx_SC = 0x08, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is 0
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyFrameErrorReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    else begin
	        TbErrorCnt++;
	        $display("FAIL: VerifyFrameErrorReceive:: Expected ReadData = 0x00 Received ReadData = 0x%h", ReadData);
	    end
	endtask


    task VerifyNormalTransmit;
        $display("VerifyNormalTransmit");
    endtask

    task VerifyAbortTransmit;
        $display("VerifyAbortTransmit");
    endtask

    task VerifyOverflowTransmit;
        $display("VerifyOverflowTransmit");
    endtask

	/****************************************************************************
	 *                                                                          *
	 *                             Simulation code                              *
	 *                                                                          *
	 ****************************************************************************/

    initial begin
	    $display("*************************************************************");
	    $display("%t - Starting Test Program", $time);
	    $display("*************************************************************");

	    Init();

	    //Receive: Size, Abort, FCSerr, NonByteAligned, Overflow, Drop, SkipRead
	    Receive( 10, 0, 0, 0, 0, 0, 0); //Normal
	    Receive( 40, 1, 0, 0, 0, 0, 0); //Abort
	    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
	    Receive( 45, 0, 0, 0, 0, 0, 0); //Normal
	    Receive(126, 0, 0, 0, 0, 0, 0); //Normal
	    Receive(122, 1, 0, 0, 0, 0, 0); //Abort
	    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
	    Receive( 25, 0, 0, 0, 0, 0, 0); //Normal
	    Receive( 47, 0, 0, 0, 0, 0, 0); //Normal

	    $display("*************************************************************");
	    $display("%t - Finishing Test Program", $time);
	    $display("*************************************************************");
	    $stop;
	end

	final begin
	    $display("*********************************");
	    $display("*                               *");
	    $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
	    $display("*                               *");
	    $display("*********************************");
	end

	// Covergroup
    covergroup hdlc_cg() @(posedge uin_hdlc.Clk);
	    Address: coverpoint uin_hdlc.Address {
	        bins Address[] = {[0:7]};
	    }
	    DataIn: coverpoint uin_hdlc.DataIn {
	        bins DataIn[] = {[0:255]};
	    }
	    DataOut: coverpoint uin_hdlc.DataOut {
	        bins DataOut[] = {[0:255]};
	    }
	    RxData: coverpoint uin_hdlc.Rx_Data {
	        bins RxData[] = {[0:255]};
	    }
	    RxFrameSize: coverpoint uin_hdlc.Rx_FrameSize {
	        bins RxFrameSize[] = {[0:255]};
	    }
	    RxDataBuffOut: coverpoint uin_hdlc.Rx_DataBuffOut {
	        bins RxDataBuffOut[] = {[0:255]};
	    }
	    RxValidFrame: coverpoint uin_hdlc.Rx_ValidFrame {
	        bins InvalidFrame = { 0 };
	        bins ValidFrame = { 1 };
	    }
	    RxAbortSignal: coverpoint uin_hdlc.Rx_AbortSignal {
	        bins Keep = { 0 };
	        bins Abort = { 1 };
	    }
	    RxReady: coverpoint uin_hdlc.Rx_Ready {
	        bins NotReady = { 0 };
	        bins Ready = { 1 };
	    }
	    RxEoF: coverpoint uin_hdlc.Rx_EoF {
	        bins NotEoF = { 0 };
	        bins EoF = { 1 };
	    }
	    RxOverflow: coverpoint uin_hdlc.Rx_Overflow {
	        bins NoOverflow = { 0 };
	        bins Overflow = { 1 };
	    }
	    RxFCSErr: coverpoint uin_hdlc.Rx_FCSerr {
	        bins NoError = { 0 };
	        bins Error = { 1 };
	    }
	    RxFrameError: coverpoint uin_hdlc.Rx_FrameError {
	        bins NoFrameError = { 0 };
	        bins FrameError = { 1 };
	    }
	    RxDrop: coverpoint uin_hdlc.Rx_Drop {
	        bins Keep = { 0 };
	        bins Drop = { 1 };
	    }
	endgroup

	// Instantiate the covergroup
	hdlc_cg inst_hdlc_cg = new();

	task Init();
	    uin_hdlc.Clk         =   1'b0;
	    uin_hdlc.Rst         =   1'b0;
	    uin_hdlc.Address     = 3'b000;
	    uin_hdlc.WriteEnable =   1'b0;
	    uin_hdlc.ReadEnable  =   1'b0;
	    uin_hdlc.DataIn      =     '0;
	    uin_hdlc.TxEN        =   1'b1;
	    uin_hdlc.Rx          =   1'b1;
	    uin_hdlc.RxEN        =   1'b1;

	    TbErrorCnt = 0;

	    #1000ns;
	    uin_hdlc.Rst         =   1'b1;
	endtask

	task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Address     = Address;
	        uin_hdlc.WriteEnable = 1'b1;
	        uin_hdlc.DataIn      = Data;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.WriteEnable = 1'b0;
	endtask

	task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Address    = Address;
	        uin_hdlc.ReadEnable = 1'b1;
	        #100ns;
	        Data                = uin_hdlc.DataOut;
	  @(posedge uin_hdlc.Clk);
	        uin_hdlc.ReadEnable = 1'b0;
	endtask

	task InsertFlagOrAbort(int flag);
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b0;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;
	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;
	    @(posedge uin_hdlc.Clk);
	        if(flag)
	            uin_hdlc.Rx = 1'b0;
	        else
	            uin_hdlc.Rx = 1'b1;
	endtask

	task MakeRxStimulus(logic [127:0][7:0] Data, int Size);
	    logic [4:0] PrevData;
	    PrevData = '0;
	    for (int i = 0; i < Size; i++) begin
	        for (int j = 0; j < 8; j++) begin
	            if(&PrevData) begin
	                @(posedge uin_hdlc.Clk);
	                    uin_hdlc.Rx = 1'b0;
	                    PrevData = PrevData >> 1;
	                    PrevData[4] = 1'b0;
	            end

	            @(posedge uin_hdlc.Clk);
	                uin_hdlc.Rx = Data[i][j];

	            PrevData = PrevData >> 1;
	            PrevData[4] = Data[i][j];
	        end
	    end
	endtask

    task MakeTxStimulus(logic [127:0][7:0] Data, int Size, logic [3:0][7:0] OverflowData, int OverflowSize);
        for (int i = 0; i < Size; i++) begin
            WriteAddress(TXBUFF, Data[i]);
        end         
        
        for (int i = 0; i < OverflowSize; i++) begin
            WriteAddress(TXBUFF, OverflowData[i]);
        end
    endtask

	task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead);
	    logic [127:0][7:0] ReceiveData;
	    logic       [15:0] FCSBytes;
	    logic   [2:0][7:0] OverflowData;
	    string msg;

	    if(Abort)
	        msg = "- Abort";
	    else if(FCSerr)
	        msg = "- FCS error";
	    else if(NonByteAligned)
	        msg = "- Non-byte aligned";
	    else if(Overflow)
	        msg = "- Overflow";
	    else if(Drop)
	        msg = "- Drop";
	    else if(SkipRead)
	        msg = "- Skip read";
	    else
	        msg = "- Normal";
	  
        $display("*************************************************************");
	    $display("%t - Starting task Receive %s", $time, msg);
	    $display("*************************************************************");

	    for (int i = 0; i < Size; i++) begin
	        ReceiveData[i] = $urandom;
	    end
	    ReceiveData[Size]   = '0;
	    ReceiveData[Size+1] = '0;

	    //Calculate FCS bits;
	    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
	    ReceiveData[Size]   = FCSBytes[7:0];
	    ReceiveData[Size+1] = FCSBytes[15:8];

	    //Enable FCS
	    if(!Overflow && !NonByteAligned) 
	        WriteAddress(RXSC, 8'h20);
	    else
	        WriteAddress(RXSC, 8'h00);

	    //Generate stimulus
	    InsertFlagOrAbort(1);
	  
	    MakeRxStimulus(ReceiveData, Size + 2);
	  
	    if(Overflow) begin
	        OverflowData[0] = 8'h44;
	        OverflowData[1] = 8'hBB;
	        OverflowData[2] = 8'hCC;
	        MakeRxStimulus(OverflowData, 3);
	    end

	    if(Abort) begin
	        InsertFlagOrAbort(0);
	    end else begin
	        InsertFlagOrAbort(1);
	    end

	    @(posedge uin_hdlc.Clk);
	        uin_hdlc.Rx = 1'b1;

	    repeat(8)
	        @(posedge uin_hdlc.Clk);

	    if(Abort)
	        VerifyAbortReceive(ReceiveData, Size);
	    else if(Overflow)
	        VerifyOverflowReceive(ReceiveData, Size);
	    else if(Drop)
	        VerifyDropReceive(ReceiveData, Size);
	    else if(FCSerr)
	        VerifyFCSErrReceive(ReceiveData, Size);
	    else if(NonByteAligned)
	        VerifyNonByteAlignedReceive(ReceiveData, Size);
	    else if(!SkipRead)
	        VerifyNormalReceive(ReceiveData, Size);

	    #5000ns;
	endtask

	task Transmit(int Size, int Abort, int Overflow);
	    logic [125:0][7:0] TransmitData;
	    logic       [15:0] FCSBytes;
	    logic   [2:0][7:0] OverflowData;
        logic [1224:0]     fData;
        int                NewSize;
	    string msg;

	    if(Abort)
	        msg = "- Abort";
	    else if(Overflow)
	        msg = "- Overflow";
	    else
	        msg = "- Normal";
	  
        $display("*************************************************************");
	    $display("%t - Starting task Transmit %s", $time, msg);
	    $display("*************************************************************");

	    for (int i = 0; i < Size; i++) begin
	        TransmitData[i] = $urandom;
	    end

	    //Calculate FCS bits;
	    GenerateFCSBytes(TransmitData, Size, FCSBytes);
	    TransmitData[Size]   = FCSBytes[15:8];
	    TransmitData[Size+1] = FCSBytes[7:0];
	  
	    if(Overflow) begin
	        OverflowData[0] = 8'h44;
	        OverflowData[1] = 8'hBB;
	        OverflowData[2] = 8'hCC;
            MakeTxStimulus(TransmitData, OverflowData, Size, 3);
        end else begin
            MakeTxStimulus(TransmitData, OverflowData, Size, 0);
        end

        if (Abort) begin
            WriteAddress(TXSC, 8'h04);
        end

        //Modify data so that it contains necessary zeros
        MakeTxOutput(TransmitData, Size, fData, NewSize);

        // Start transmission
        WriteAddress(TXSC, 8'h02);

	    repeat(8)
	        @(posedge uin_hdlc.Clk);

	    if(Abort)
	        VerifyAbortTransmit(TransmitData, Size);
	    else if(Overflow)
	        VerifyOverflowTransmit(TransmitData, Size, 3);
	    else
	        VerifyNormalTransmit(Transmit, Size);

        #5000ns;
    endtask

    task MakeTxOutput(logic [127:0][7:0] data, int size, output logic [128*8 + 200:0] fData, output int newSize);
        logic [4:0] checkZero;
        logic insertZero;

        checkZero = 4'b0;
        newSize = 0;

        // Insert zeros if necessary
        for (int i = 0; i < size; i++) begin
            for (int j = 0; j < 8; j++) begin
                insertZero = &checkZero;
                if (insertZero == 1'b1) begin
                    fData[newSize] = 1'b0;
                    newSize++;
                end
                fData[newSize] = data[i][j];
                newSize++;
                checkZero = checkZero >> 1;
                checkZero[4] = data[i][j];
            end
        end

        // Append FCS's
        fData[newSize+7:newSize] = data[size];
        newSize += 8;
        fData[newSize+7:newSize] = data[size+1];
        newSize += 8;
    endtask

	task GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
	    logic [23:0] CheckReg;
	    CheckReg[15:8]  = data[1];
	    CheckReg[7:0]   = data[0];
	    for(int i = 2; i < size+2; i++) begin
	        CheckReg[23:16] = data[i];
	        for(int j = 0; j < 8; j++) begin
	            if(CheckReg[0]) begin
	                CheckReg[0]    = CheckReg[0] ^ 1;
	                CheckReg[1]    = CheckReg[1] ^ 1;
	                CheckReg[13:2] = CheckReg[13:2];
	                CheckReg[14]   = CheckReg[14] ^ 1;
	                CheckReg[15]   = CheckReg[15];
	                CheckReg[16]   = CheckReg[16] ^1;
	            end
	            CheckReg = CheckReg >> 1;
	        end
	    end
	    FCSBytes = CheckReg;
	endtask

endprogram
