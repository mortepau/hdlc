//////////////////////////////////////////////////
// Title:	 testPr_hdlc
// Author: 
// Date:	
//////////////////////////////////////////////////

program testPr_hdlc(
    in_hdlc uin_hdlc
);
	
    int TbErrorCnt;

    // Addresses
    logic [2:0] TXSC   = 3'b000,
	            TXBUFF = 3'b001, 
	            RXSC   = 3'b010, 
	            RXBUFF = 3'b011, 
	            RXLEN  = 3'b100; 

    // Address bits
    logic [7:0] TXSC_FULL         = 8'b0001_0000,
                TXSC_ABORTEDTRANS = 8'b0000_1000,
                TXSC_ABORTFRAME   = 8'b0000_0100,
                TXSC_ENABLE       = 8'b0000_0010,
                TXSC_DONE         = 8'b0000_0001,
                RXSC_FCSEN        = 8'b0010_0000,
                RXSC_OVERFLOW     = 8'b0001_0000,
                RXSC_ABORTSIGNAL  = 8'b0000_1000,
                RXSC_FRAMEERROR   = 8'b0000_0100,
                RXSC_DROP         = 8'b0000_0010,
                RXSC_READY        = 8'b0000_0001;
                
    // Read masks
	logic [7:0] RXSC_READ_MASK = 8'b1101_1101,
                TXSC_READ_MASK = 8'b1111_1001;

    // VerifyNormalReceive should verify correct value in the Rx status/control register
    // and that the output is correct
    task VerifyNormalReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData, DataLen;

        // Wait for Rx_Ready to be asserted
	    wait(uin_hdlc.Rx_Ready);

	    // Assert that only Rx_Ready is set in RX_SC
	    ReadAddress(RXSC, ReadData);
        // Only check RO bits
	    ReadData = ReadData & RXSC_READ_MASK;
        assert (ReadData == RXSC_READY) begin
            $display("PASS: VerifyNormalReceive:: Rx_SC correct");
        end else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyNormalReceive:: Expected Rx_SC = 0x01, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert data length is correct
	    ReadAddress(RXLEN, DataLen);
        assert (DataLen == Size) begin
            $display("PASS: VerifyNormalReceive:: Rx_Len correct");
        end else begin
            TbErrorCnt++;
            $error("FAIL: VerifyNormalReceive:: Expected Rx_Len = %0d, Received Rx_Len = %0d", Size, DataLen);
        end

        // Check content
	    for (int i = 0; i < DataLen; i++) begin
	        ReadAddress(RXBUFF, ReadData);
            assert(ReadData == data[i]) begin
                $display("PASS: VerifyNormalReceive:: Rx_Buff correct");
            end else begin
	            TbErrorCnt++;
	            $error("FAIL: VerifyNormalReceive:: Expected Rx_Buff = 0x%h, Received Rx_Buff = 0x%h", data[i], ReadData);
	        end
	    end
	endtask

	// VerifyOverflowReceive should verify correct value in the Rx status/control
	// register, that the data is correct and that the Rx data buffer is 
    // zero after overflow.
	task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData, DataLen;

        // Wait for Rx_Ready to be asserted
	    wait(uin_hdlc.Rx_Ready);

	    // Assert that Rx_Ready and Rx_Overflow is set
	    ReadAddress(RXSC, ReadData);
        // Only check RO bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == (RXSC_OVERFLOW | RXSC_READY)) 
            $display("PASS: VerifyOverflowReceive:: Rx_SC correct");
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyOverflowReceive:: Expected Rx_SC = 0x11, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert data length is correct 
	    ReadAddress(RXLEN, DataLen);
        assert (DataLen == Size) begin
            $display("PASS: VerifyOverflowReceive:: Rx_Len correct");
        end else begin
            TbErrorCnt++;
            $error("FAIL: VerifyOverflowReceive:: Expected Rx_Len = %0d, Received Rx_Len = %0d", Size, DataLen);
        end

        // Check content
	    for (int i = 0; i < DataLen; i++) begin
	        ReadAddress(RXBUFF, ReadData);
            assert(ReadData == data[i]) begin
                $display("PASS: VerifyOverflowReceive:: Rx_Buff correct");
            end else begin
	            TbErrorCnt++;
	            $error("FAIL: VerifyOverflowReceive:: Expected Rx_Buff = 0x%h, Received Rx_Buff = 0x%h", data[i], ReadData);
	        end
	    end

	    // Read a few extra bytes and check that they are invalid
        for (int i = 0; i < 3; i++) begin
            ReadAddress(RXBUFF, ReadData);
            assert(ReadData == 8'b0) 
                $display("PASS: VerifyOverflowReceive:: Rx_Buff correct");
            else begin
                TbErrorCnt++;
                $error("FAIL: VerifyOverflowReceive:: Expected Rx_Buff = 0x00, Received Rx_Buff = 0x%h", ReadData);
            end
        end
    endtask

	// VerifyAbortReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after abort.
	task VerifyAbortReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_AbortSignal is set
	    ReadAddress(RXSC, ReadData);
        // Only check RO bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == RXSC_ABORTSIGNAL)
            $display("PASS: VerifyAbortReceive:: Rx_SC correct");
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyAbortReceive:: Expected Rx_SC = 0x08, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that data is invalid
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyAbortReceive:: Rx_Buff correct");
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyAbortReceive:: Expected Rx_Buff = 0x00, Received Rx_Buff = 0x%h", ReadData);
	    end
	endtask

	// VerifyDropReceive should verify that the Rx data buffer is zero
    // after dropping the frame.
	task VerifyDropReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

        // Drop the current frame
        WriteAddress(RXSC, RXSC_DROP);

        @(posedge uin_hdlc.Clk);

	    // Assert that Rx_Buff is invalid
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyDropReceive:: Rx_Buff correct", ReadData);
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyDropReceive:: Expected Rx_Buff = 0x00, Received Rx_Buff = 0x%h", ReadData);
	    end
	endtask

	// VerifyNonByteAlignedReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after Non-Byte-Alignment.
	task VerifyNonByteAlignedReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData;

	    // Assert that only Rx_FrameError is set
	    ReadAddress(RXSC, ReadData);
        // Only check RO bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == RXSC_FRAMEERROR)
            $display("PASS: VerifyNonByteAlignedReceive:: Rx_SX correct");
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyNonByteAlignedReceive:: Expected Rx_SC = 0x04, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is invalid
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyNonByteAlignedReceive:: Rx_Buff correct", ReadData);
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyNonByteAlignedReceive:: Expected Rx_Buff = 0x00, Received Rx_Buff = 0x%h", ReadData);
	    end
	endtask

	// VerifyFCSErrReceive should verify correct value in the Rx status/control
	// register, and that the Rx data buffer is zero after frameError.
	task VerifyFCSErrReceive(logic [127:0][7:0] data, int Size);
	    logic [7:0] ReadData, DataLen;

	    // Assert that only Rx_FrameError is set
	    ReadAddress(RXSC, ReadData);
	    // Only check RO bits
	    ReadData = ReadData & RXSC_READ_MASK;
	    assert (ReadData == RXSC_FRAMEERROR)
            $display("PASS: VerifyFCSErrReceive:: Rx_SC correct");
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyFCSErrReceive:: Expected Rx_SC = 0x04, Received Rx_SC = 0x%h", ReadData);
	    end

	    // Assert that Rx_Buff is invalid
	    ReadAddress(RXBUFF, ReadData);
	    assert (ReadData == 8'b0)
            $display("PASS: VerifyFCSErrReceive:: Rx_Buff correct", ReadData);
	    else begin
	        TbErrorCnt++;
	        $error("FAIL: VerifyFCSErrReceive:: Expected Rx_Buff = 0x00 Received Rx_Buff = 0x%h", ReadData);
	    end
	endtask

    // VerifyNonAbortTransmit should verify correct output stream from Tx
    // and that CRC is correct
    task VerifyNonAbortTransmit(logic [128*8+204:0] fData, int Size, int FCSSize);
        // Using +3 as this takes potential zero insertions into consideration
        // floor(16/5)=3
        logic [15+3:0] FCSBytes,
                       FCSBytes_calc;
        logic  [7:0] flag;
        
        flag = 8'b0111_1110;
        
        // Check flag
        for (int f = 0; f < 8; f++) begin
            if (f != 0) begin
                @(posedge uin_hdlc.Clk);
            end
            assert(uin_hdlc.Tx == flag[f]) else begin
                $error("FAIL: VerifyNonAbortTransmit:: Expected Tx_flag = 0b%b, Received Tx_flag = 0b%b", flag[f], uin_hdlc.Tx);
                TbErrorCnt++;
            end
        end

        // Check data
        for (int i = 0; i < Size; i++) begin
            @(posedge uin_hdlc.Clk);
                assert (fData[i] == uin_hdlc.Tx) else begin
                    $error("FAIL. VerifyNonAbortTransmit:: Expected Tx = 0b%b, Received Tx = 0b%b", fData[i], uin_hdlc.Tx);
                    TbErrorCnt++;
                end
        end

        // Check FCS bytes
        FCSBytes = '0;
        FCSBytes_calc = '0;
        for (int i = 0; i < FCSSize; i++) begin
            @(posedge uin_hdlc.Clk) begin
                FCSBytes[i] = uin_hdlc.Tx;
                FCSBytes_calc[i] = fData[Size + i];
            end
        end
        assert(FCSBytes == FCSBytes_calc) begin
            $display("PASS: VerifyNonAbortTransmit:: FCSBytes correct");    
        end else begin
            $error("FAIL: VerifyNonAbortTransmit:: Expected FCSBytes = 0x%5h, Received FCSBytes = 0x%5h", FCSBytes_calc, FCSBytes);
            TbErrorCnt++;
        end

        // Check flag
        for (int f = 0; f < 8; f++) begin
            @(posedge uin_hdlc.Clk);
                assert(uin_hdlc.Tx == flag[f]) else begin
                    $error("FAIL: VerifyNonAbortTransmit:: Expected Tx_flag = 0b%b, Received Tx_flag = 0b%b", flag[f], uin_hdlc.Tx);
                    TbErrorCnt++;
                end
        end
    endtask

    // VerifyAbortTransmit should verify correct output stream from Tx
    // and that the abort sequence is generated and idle after that
    task VerifyAbortTransmit(logic [128*8+204:0] fData, int Size);
        // Using +3 as this takes potential zero insertions into consideration
        // floor(16/5)=3
        logic [15+3:0] FCSBytes,
                       FCSBytes_calc;
        logic  [7:0] flag,
                     ReadData;
        
        flag = 8'b0111_1110;
        
        // Check flag
        for (int f = 0; f < 8; f++) begin
            if (f != 0) begin
                @(posedge uin_hdlc.Clk);
            end
            assert(uin_hdlc.Tx == flag[f]) else begin
                $error("FAIL: VerifyAbortTransmit:: Expected Tx_flag = 0b%b, Received Tx_flag = 0b%b", flag[f], uin_hdlc.Tx);
                TbErrorCnt++;
            end
        end

        // Check data
        for (int i = 0; i < Size / 2; i++) begin
            @(posedge uin_hdlc.Clk);
                assert (fData[i] == uin_hdlc.Tx) else begin
                    $error("FAIL: VerifyAbortTransmit:: Expected Tx = 0b%b, Received Tx = 0b%b", fData[i], uin_hdlc.Tx);
                    TbErrorCnt++;
                end
        end

        // Abort the frame
        WriteAddress(TXSC, TXSC_ABORTFRAME);

        // Wait 2 clock cycles
        @(posedge uin_hdlc.Clk);
        @(posedge uin_hdlc.Clk);

        // Check that Tx_AbortedTrans is asserted
        ReadAddress(TXSC, ReadData);
	    // Only check RO bits 
        ReadData = ReadData & TXSC_READ_MASK;
        assert (ReadData == (TXSC_ABORTEDTRANS | TXSC_DONE)) begin
            $display("PASS: VerifyAbortTransmit:: Tx_SC correct");
        end else begin
            $error("FAIL: VerifyAbortTransmit:: Expected Tx_SC = 0x09, Received Tx_SC = 0x%h", ReadData);
            TbErrorCnt++;
        end

        // Wait 2 clock cycles for Tx_AbortFrame to propagate
        @(posedge uin_hdlc.Clk);
        @(posedge uin_hdlc.Clk);

        // Check that Tx is set back to idle
        repeat(10) begin
            @(posedge uin_hdlc.Clk);
                assert (uin_hdlc.Tx == 1'b1) else begin
                    $error("FAIL: VerifyAbortTransmit:: Expected Tx = 0b1");
                    TbErrorCnt++;
                end
        end
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

	    // Receive: Size, Abort, FCSerr, NonByteAligned, Overflow, Drop, SkipRead
	    Receive(      10,     0,      0,              0,        0,    0,        0); // Normal
	    Receive(      40,     1,      0,              0,        0,    0,        0); // Abort
	    Receive(     126,     0,      0,              0,        1,    0,        0); // Overflow
	    Receive(      45,     0,      0,              0,        0,    0,        0); // Normal
	    Receive(     126,     0,      0,              0,        0,    0,        0); // Normal
	    Receive(     122,     1,      0,              0,        0,    0,        0); // Abort
	    Receive(     126,     0,      0,              0,        1,    0,        0); // Overflow
	    Receive(      25,     0,      0,              0,        0,    0,        0); // Normal
	    Receive(      47,     0,      0,              0,        0,    0,        0); // Normal
	    Receive(      58,     0,      1,              0,        0,    0,        0); // FCSerr
	    Receive(      90,     0,      0,              1,        0,    0,        0); // NonByteAligned
	    Receive(      74,     0,      0,              0,        0,    1,        0); // Drop
	    Receive(     101,     0,      0,              0,        0,    0,        1); // SkipRead

        //Transmit: Size, Abort, Overflow
        Transmit(     10,     0,        0); // Normal
        Transmit(    122,     1,        0); // Abort
        Transmit(    126,     0,        1); // Overflow
        Transmit(     40,     0,        0); // Normal
        Transmit(    126,     0,        0); // Normal
        Transmit(     40,     1,        0); // Abort
        Transmit(    126,     0,        1); // Overflow
        Transmit(    122,     0,        0); // Normal
        Transmit(     47,     0,        0); // Normal

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
            bins Tx_SC = {0};
            bins Tx_Buff = {1};
            bins Rx_SC = {2};
            bins Rx_Buff = {3};
            bins Rx_Len = {4};
            ignore_bins Invalid = {[5:7]};
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
	        bins RxFrameSize[] = {[0:126]};
            ignore_bins Invalid = {[127:255]};
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
        TxValidFrame: coverpoint uin_hdlc.Tx_ValidFrame {
            bins InvalidFrame = { 0 };
            bins ValidFrame = { 1 };
        }
        TxAbortedTrans: coverpoint uin_hdlc.Tx_AbortedTrans {
            bins Kept = { 0 };
            bins Aborted = { 1 };
        }
        TxData: coverpoint uin_hdlc.Tx_Data {
            bins TxData[] = {[0:255]};
        }
        TxFull: coverpoint uin_hdlc.Tx_Full {
            bins NotFull = { 0 };
            bins Full = { 1 };
        }
        TxFrameSize: coverpoint uin_hdlc.Tx_FrameSize {
            bins TxFrameSize[] = {[0:126]};
            ignore_bins Invalid = {[127:255]};
        }
        TxEnable: coverpoint uin_hdlc.Tx_Enable {
            bins Disabled = { 0 };
            bins Enabled = { 1 };
        }
        TxAbortFrame: coverpoint uin_hdlc.Tx_AbortFrame {
            bins Keep = { 0 };
            bins Abort = { 1 };
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

    task MakeTxStimulus(input logic [127:0][7:0] Data, input int Size, input logic [3:0][7:0] OverflowData, input int OverflowSize);
        // Write data that is actually inserted
        for (int i = 0; i < Size; i++) begin
            WriteAddress(TXBUFF, Data[i]);
        end         
        
        // Write overflow data
        for (int i = 0; i < OverflowSize; i++) begin
            WriteAddress(TXBUFF, OverflowData[i]);
        end
    endtask

    // Flatten the 2D array of data + FCS bytes and insert zeros when 5 consequent 1's 
    task ConvertToTxStream(input logic [127:0][7:0] Data, input int Size, output logic [128*8 + 200:0] fData, output int newSize, output int FCSSize);
        logic [4:0] prevData;

        prevData = '0;
        newSize = 0;
        FCSSize = 0;

        // Insert zeros if necessary
        fData = '0;
        for (int i = 0; i < Size + 2; i++) begin
            for (int j = 0; j < 8; j++) begin
                // If 5 1's in a row
                if (&prevData) begin
                    if (i <= Size) begin
                        fData[newSize] = 1'b0;
                        newSize++;
                    end else begin
                        fData[newSize + FCSSize] = 1'b0;
                        FCSSize++;
                    end

                    prevData = prevData >> 1;
                    prevData[4] = 1'b0;
                end

                if (i <= Size) begin
                    fData[newSize] = Data[i][j];
                    newSize++;
                end else begin
                    fData[newSize + FCSSize] = Data[i][j];
                    FCSSize++;
                end

                prevData = prevData >> 1;
                prevData[4] = Data[i][j];
            end
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

        if (FCSerr) begin
            FCSBytes[7:0]  = FCSBytes[7:0] ^ 8'b11111111;
            FCSBytes[15:8] = FCSBytes[15:8] ^ 8'b11111111;
        end

        ReceiveData[Size] = FCSBytes[7:0];
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

        if (NonByteAligned) begin
            @(posedge uin_hdlc.Clk);
                uin_hdlc.Rx = 1'b1;
            @(posedge uin_hdlc.Clk);
                uin_hdlc.Rx = 1'b0;
            @(posedge uin_hdlc.Clk);
                uin_hdlc.Rx = 1'b0;
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
	    logic [127:0][7:0] TransmitData;
	    logic   [2:0][7:0] OverflowData;
	    logic       [15:0] FCSBytes;
        logic     [1228:0] fData;
        int                NewSize;
        int                FCSSize;
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

        // Generate random data
	    for (int i = 0; i < Size; i++) begin
	        TransmitData[i] = $urandom;
	    end
        // Set FCS bytes to 0
        TransmitData[Size] = '0;
        TransmitData[Size + 1] = '0;


	    //Calculate FCS bits;
	    GenerateFCSBytes(TransmitData, Size, FCSBytes);
        // Insert the updated FCS bytes
	    TransmitData[Size] = FCSBytes[7:0];
	    TransmitData[Size+1]   = FCSBytes[15:8];
	  
        // Flatten data and insert zeros
        ConvertToTxStream(TransmitData, Size, fData, NewSize, FCSSize);

	    if(Overflow) begin
	        OverflowData[0] = 8'h44;
	        OverflowData[1] = 8'hBB;
	        OverflowData[2] = 8'hCC;
            MakeTxStimulus(TransmitData, Size, OverflowData, 3);
        end else begin
            MakeTxStimulus(TransmitData, Size, OverflowData, 0);
        end

        // Assert that Tx_Overflow is asserted
        if (Overflow) begin
            logic [7:0] ReadData;
            ReadAddress(TXSC, ReadData);
            assert (ReadData == 8'h10) begin
                $display("PASS: Tx_Overflow asserted"); 
            end else begin
                $error("FAIL: Tx_Overflow not asserted");
                TbErrorCnt++;
            end
        end

        // Start transmission
        WriteAddress(TXSC, 8'h02);

        // Wait for the beginning of the first flag
        @(negedge uin_hdlc.Tx);

	    if(Abort)
	        VerifyAbortTransmit(fData, NewSize);
	    else
	        VerifyNonAbortTransmit(fData, NewSize, FCSSize);

        #5000ns;

        @(posedge uin_hdlc.Clk);
        uin_hdlc.Rst = 1'b0;

        repeat(100)
            @(posedge uin_hdlc.Clk);
            
        uin_hdlc.Rst = 1'b1;
        @(posedge uin_hdlc.Clk);
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
