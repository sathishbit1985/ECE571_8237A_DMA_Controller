// DMA Top Module
module DMAControllerTop(SystemBusIF.DMA DMA, input logic nCS, inout wire [7:0] DB7_DB0 );

wire [7:0] CommandRegOut;
wire [3:0] MaskRegOut;
wire [5:0] ModeRegOut[4];
wire [15:0] TAROut[4];
wire [3:0] PendingReq;
wire [3:0] StatusOut;

//DMA Internal control signals in Interface
ControlIF DMAcif();
TimingControlLogic TCL(DMA, DMAcif, nCS, DB7_DB0, ModeRegOut, TAROut, StatusOut);
PriorityEncoder PEM(DMA, DMAcif, CommandRegOut[4], CommandRegOut[6], CommandRegOut[7], CommandRegOut[2], MaskRegOut, PendingReq);
Datapath DP(CommandRegOut, MaskRegOut, ModeRegOut, TAROut, StatusOut, DB7_DB0, PendingReq, DMAcif, DMA, DMA.Clock, DMA.Reset);
endmodule