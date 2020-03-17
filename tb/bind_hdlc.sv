//////////////////////////////////////////////////
// Title:   bind_hdlc
// Author:  Karianne Krokan Kragseth
// Date:    20.10.2017
//////////////////////////////////////////////////

module bind_hdlc ();

  bind test_hdlc assertions_hdlc u_assertion_bind(
    .ErrCntAssertions   ( uin_hdlc.ErrCntAssertions   ),

    .Clk                ( uin_hdlc.Clk                ),
    .Rst                ( uin_hdlc.Rst                ),

    .Address            ( uin_hdlc.Address            ),
    .WriteEnable        ( uin_hdlc.WriteEnable        ),
    .ReadEnable         ( uin_hdlc.ReadEnable         ),
    .DataIn             ( uin_hdlc.DataIn             ),
    .DataOut            ( uin_hdlc.DataOut            ),

    .Rx                 ( uin_hdlc.Rx                 ),
    .RxEN               ( uin_hdlc.RxEN               ),
    .Rx_Ready           ( uin_hdlc.Rx_Ready           ),

    .Rx_ValidFrame      ( uin_hdlc.Rx_ValidFrame      ),
    .Rx_WrBuff          ( uin_hdlc.Rx_WrBuff          ),
    .Rx_AbortSignal     ( uin_hdlc.Rx_AbortSignal     ),
    .Rx_StartZeroDetect ( uin_hdlc.Rx_StartZeroDetect ),
    .Rx_FrameError      ( uin_hdlc.Rx_FrameError      ),
    .Rx_StartFCS        ( uin_hdlc.Rx_StartFCS        ),
    .Rx_StopFCS         ( uin_hdlc.Rx_StopFCS         ),
    .Rx_Data            ( uin_hdlc.Rx_Data            ),
    .Rx_NewByte         ( uin_hdlc.Rx_NewByte         ),
    .Rx_FlagDetect      ( uin_hdlc.Rx_FlagDetect      ),
    .Rx_AbortDetect     ( uin_hdlc.Rx_AbortDetect     ),
    .RxD                ( uin_hdlc.RxD                ),
    .Rx_FCSerr          ( uin_hdlc.Rx_FCSerr          ),
    .Rx_FrameSize       ( uin_hdlc.Rx_FrameSize       ),
    .Rx_Overflow        ( uin_hdlc.Rx_Overflow        ),
    .Rx_DataBuffOut     ( uin_hdlc.Rx_DataBuffOut     ),
    .Rx_FCSen           ( uin_hdlc.Rx_FCSen           ),
    .Rx_Drop            ( uin_hdlc.Rx_Drop            ),

    .Tx                 ( uin_hdlc.Tx                 ),
    .TxEN               ( uin_hdlc.TxEN               ),
    .Tx_Done            ( uin_hdlc.Tx_Done            ),

    .Tx_ValidFrame      ( uin_hdlc.Tx_ValidFrame      ),
    .Tx_AbortFrame      ( uin_hdlc.Tx_AbortFrame      ),
    .Tx_WriteFCS        ( uin_hdlc.Tx_WriteFCS        ),
    .Tx_InitZero        ( uin_hdlc.Tx_InitZero        ),
    .Tx_StartFCS        ( uin_hdlc.Tx_StartFCS        ),
    .Tx_RdBuff          ( uin_hdlc.Tx_RdBuff          ),
    .Tx_NewByte         ( uin_hdlc.Tx_NewByte         ),
    .Tx_FCSDone         ( uin_hdlc.Tx_FCSDone         ),
    .Tx_Data            ( uin_hdlc.Tx_Data            ),
    .Tx_Full            ( uin_hdlc.Tx_Full            ),
    .Tx_DataAvail       ( uin_hdlc.Tx_DataAvail       ),
    .Tx_FrameSize       ( uin_hdlc.Tx_FrameSize       ),
    .Tx_DataArray       ( uin_hdlc.Tx_DataArray       ),
    .Tx_DataOutBuff     ( uin_hdlc.Tx_DataOutBuff     ),
    .Tx_WrBuff          ( uin_hdlc.Tx_WrBuff          ),
    .Tx_Enable          ( uin_hdlc.Tx_Enable          ),
    .Tx_DataInBuff      ( uin_hdlc.Tx_DataInBuff      ),
    .Tx_AbortFrame      ( uin_hdlc.Tx_AbortFrame      )
  );

endmodule
