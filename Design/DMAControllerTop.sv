//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Sathishkumar Thirumalaisamy
// Module Name: DMAControllerTop
// Project Name: DMA Controller
//////////////////////////////////////////////////////////////////////////////////

module DMAControllerTop(SystemBusIF.DMA sif, input logic nCS, inout wire [7:0] DB7_DB0 );

logic [7:0]  CommandReg;
logic [3:0]  MaskReg;
logic [5:0]  ModeReg[3:0];
logic [15:0] TARReg[3:0];
logic [3:0]  PendingReq;
logic [3:0]  StatusReg;

//DMA Internal control signals in Interface
ControlIF cif();

TimingControlLogic TCL(.*);
PriorityEncoder PEM(sif, cif, CommandReg[4], CommandReg[6], CommandReg[7], CommandReg[2], MaskReg, PendingReq);
Datapath DP(CommandReg, MaskReg, ModeReg, TARReg, StatusReg, DB7_DB0, PendingReq, cif, sif, sif.Clock, sif.Reset);
endmodule