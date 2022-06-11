//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Sathishkumar Thirumalaisamy
// Module Name: TimingControlLogic
// Project Name: DMA Controller
//////////////////////////////////////////////////////////////////////////////////

module TimingControlLogic (SystemBusIF.DMA sif, ControlIF.TCL cif, input logic nCS, input logic [7:0] DB7_DB0, input logic [5:0] ModeReg[3:0], input logic [15:0] TARReg[3:0], input logic [3:0] StatusReg );

import DmaRegisterAddressCode::*;

localparam CH0 = 2'b00;
localparam CH1 = 2'b01;
localparam CH2 = 2'b10;
localparam CH3 = 2'b11;
localparam DMAWrite = 2'b01;
localparam DMARead  = 2'b10;

logic ProgramMode;
logic en_AddrBuf, en_DataIOBuf;
logic aen, adstb;
logic IOW_out, IOR_out, MEMW_out, MEMR_out;
logic WriteTransfer, ReadTransfer;
logic UpAddrSTB;
logic CheckEOP, EOP;
logic RollOverCheck;			
logic TempAddrOut, TempAddrIncrDec;
logic [3:0] TempIncrDecLoad;

//////////////////////////// Register Read/Write Control Logic ///////////////////////////////////////////////
//ProgramMode Logic. If chip select & hold acknowledgement are low, DMA is in program mode
always_comb
begin
if(sif.Reset)				ProgramMode = 1'b0;
else if(~nCS && ~sif.Hlda)  ProgramMode = 1'b1; 
else    					ProgramMode = 1'b0;
end

//Write Control signals
//To load the address into Base,Current and Temp Address Register
assign cif.CARLoad[0]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH0_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.CARLoad[1]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH1_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.CARLoad[2]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH2_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.CARLoad[3]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH3_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.BARLoad     = cif.CARLoad;
assign cif.TARLoad     = cif.CARLoad | TempIncrDecLoad;

//To load the word count into Base,Current and Temp word count Register
assign cif.CWCLoad[0]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH0_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.CWCLoad[1]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH1_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.CWCLoad[2]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH2_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.CWCLoad[3]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CH3_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.BWCLoad     = cif.CWCLoad;
assign cif.TWCLoad 	   = cif.CWCLoad | TempIncrDecLoad;

//Mux select signal for Address & Word reg
assign cif.AddrMuxSel  = cif.CARLoad;
assign cif.WCMuxSel    = cif.CWCLoad;

//To load the Mode,Command and Mask Register
assign cif.ModeLoad[0]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == MODE_REGISTER && DB7_DB0[1:0] == CH0) ? 1'b1 : 1'b0;
assign cif.ModeLoad[1]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == MODE_REGISTER && DB7_DB0[1:0] == CH1) ? 1'b1 : 1'b0;
assign cif.ModeLoad[2]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == MODE_REGISTER && DB7_DB0[1:0] == CH2) ? 1'b1 : 1'b0;
assign cif.ModeLoad[3]  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == MODE_REGISTER && DB7_DB0[1:0] == CH3) ? 1'b1 : 1'b0;
assign cif.CommandLoad  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == COMMAND_REGISTER ) ? 1'b1 : 1'b0;
assign cif.MaskLoad = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == WRITE_ALL_MASK_REGISTER ) ? 1'b1 : 1'b0;

//Read Control signals
// Enable the current address for CPU readback
assign cif.CAREnable[0] = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH0_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.CAREnable[1] = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH1_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.CAREnable[2] = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH2_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;
assign cif.CAREnable[3] = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH3_CURRENT_ADDRESS ) ? 1'b1 : 1'b0;

// Enable the current word for CPU readback					      
assign cif.CWCEnable[0]  = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH0_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.CWCEnable[1]  = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH1_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.CWCEnable[2]  = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH2_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;
assign cif.CWCEnable[3]  = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == CH3_CURRENT_WORD_COUNT ) ? 1'b1 : 1'b0;

//Enable status reg for CPU readback
assign cif.StatusEnable	 = ( ProgramMode && ~sif.nIOR && sif.nIOW && sif.Address[3:0] == STATUS_REGISTER ) ? 1'b1 : 1'b0;

//Software commands
assign cif.MasterClear  = ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == MASTER_CLEAR ) ? 1'b1 : 1'b0;
assign cif.ClearMask	= ( ProgramMode && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CLEAR_MASK_REGISTER ) ? 1'b1 : 1'b0;

// byte pointer flip-flop generation logic
always_ff @(posedge sif.Clock)
begin
if ( (ProgramMode && ~nCS && sif.nIOR && ~sif.nIOW && sif.Address[3:0] == CLEAR_BPFF ) || cif.MasterClear ) cif.FF <= 1'b0;
else if (cif.CARLoad[0] || cif.CARLoad[1] || cif.CARLoad[2] || cif.CARLoad[3] || cif.CAREnable[0] || cif.CAREnable[1] || cif.CAREnable[2] || cif.CAREnable[3] ||
		 cif.CWCLoad[0] || cif.CWCLoad[1] || cif.CWCLoad[2] || cif.CWCLoad[3] || cif.CWCEnable[0] || cif.CWCEnable[1] || cif.CWCEnable[2] || cif.CWCEnable[3] ) cif.FF <= 1'b1;
end

//Buffer enable commands for address & data
assign cif.DataBufEnable   = ((~nCS && ~sif.nIOR && sif.nIOW) || en_DataIOBuf) ? 1'b1 : 1'b0;
assign cif.DataBufLoad     = (~nCS && sif.nIOR && ~sif.nIOW) ? 1'b1 : 1'b0;
assign cif.AddrBufEnbable  = en_AddrBuf ? 1'b1 : 1'b0;
//////////////////////////// End Register Read/Write Control Logic ///////////////////////////////////////////////


//////////////////////////////////////// DMA FSM & Control Logic  ////////////////////////////////////////////////
assign sif.nIOW  = sif.Hlda ? IOW_out  : 1'bz;
assign sif.nIOR  = sif.Hlda ? IOR_out  : 1'bz;
assign sif.nMEMW = sif.Hlda ? MEMW_out : 1'bz;
assign sif.nMEMR = sif.Hlda ? MEMR_out : 1'bz;

//logic to determine Write or Read transfer
always_comb
begin
{IOW_out,IOR_out,MEMW_out,MEMR_out} = '1;
if (WriteTransfer)
  begin
    if( (cif.ReqID == CH0 && ModeReg[0][1:0] == DMAWrite) || (cif.ReqID == CH1 && ModeReg[1][1:0] == DMAWrite) || (cif.ReqID == CH2 && ModeReg[2][1:0] == DMAWrite) || (cif.ReqID == CH3 && ModeReg[3][1:0] == DMAWrite))
	  IOR_out = '0;
	else if((cif.ReqID == CH0 && ModeReg[0][1:0] == DMARead) || (cif.ReqID == CH1 && ModeReg[1][1:0] == DMARead) || (cif.ReqID == CH2 && ModeReg[2][1:0] == DMARead) || (cif.ReqID == CH3 && ModeReg[3][1:0] == DMARead)) 
	  MEMR_out = '0;
  end
if (ReadTransfer)
  begin
    if( (cif.ReqID == CH0 && ModeReg[0][1:0] == DMAWrite) || (cif.ReqID == CH1 && ModeReg[1][1:0] == DMAWrite) || (cif.ReqID == CH2 && ModeReg[2][1:0] == DMAWrite) || (cif.ReqID == CH3 && ModeReg[3][1:0] == DMAWrite)) 
	  MEMW_out = '0;
	else if((cif.ReqID == CH0 && ModeReg[0][1:0] == DMARead) || (cif.ReqID == CH1 && ModeReg[1][1:0] == DMARead) || (cif.ReqID == CH2 && ModeReg[2][1:0] == DMARead) || (cif.ReqID == CH3 && ModeReg[3][1:0] == DMARead)) 
	  IOW_out = '0;
  end
end

//logic to determine if address upper byte has to be outputted in 8086 bus
//this logic will be triggered Address to change every 255 cycles
always_comb
begin
if(cif.ReqID == CH0 && ModeReg[0][3])        UpAddrSTB = ~|(TARReg[0][7:0]);
else if (cif.ReqID == CH1 && ModeReg[1][3])  UpAddrSTB = ~|(TARReg[1][7:0]);
else if (cif.ReqID == CH2 && ModeReg[2][3])  UpAddrSTB = ~|(TARReg[2][7:0]);
else if (cif.ReqID == CH3 && ModeReg[3][3])  UpAddrSTB = ~|(TARReg[3][7:0]);
else if (cif.ReqID == CH0 && ~ModeReg[0][3]) UpAddrSTB = &(TARReg[0][7:0]);
else if (cif.ReqID == CH1 && ~ModeReg[1][3]) UpAddrSTB = &(TARReg[1][7:0]);
else if (cif.ReqID == CH2 && ~ModeReg[2][3]) UpAddrSTB = &(TARReg[2][7:0]);
else if (cif.ReqID == CH3 && ~ModeReg[3][3]) UpAddrSTB = &(TARReg[3][7:0]);
else UpAddrSTB = '0;
end

//Control signal to check for word count register rollover from 0 to FFFFH
always_comb
begin
cif.RollOverCheck = '0;
if(RollOverCheck)
  begin
    if (cif.ReqID == CH0)      cif.RollOverCheck[0] = 1'b1;
    else if (cif.ReqID == CH1) cif.RollOverCheck[1] = 1'b1;
	else if (cif.ReqID == CH2) cif.RollOverCheck[2] = 1'b1;
	else 					   cif.RollOverCheck[3] = 1'b1;
  end
end

//Control signal to output the temporary address register to Address Buffer
always_comb
begin
cif.TAREnbale = '0;
if (TempAddrOut)
  begin
    if (cif.ReqID == CH0)      cif.TAREnbale[0] = 1'b1;
    else if (cif.ReqID == CH1) cif.TAREnbale[1] = 1'b1;
	else if (cif.ReqID == CH2) cif.TAREnbale[2] = 1'b1;
	else 					   cif.TAREnbale[3] = 1'b1;
  end
end

//Control signal to Increment/Decrement temporary address register
always_comb
begin
TempIncrDecLoad = '0;
if (TempAddrIncrDec)
  begin
    if (cif.ReqID == CH0)      TempIncrDecLoad[0] = 1'b1;
    else if (cif.ReqID == CH1) TempIncrDecLoad[1] = 1'b1;
	else if (cif.ReqID == CH2) TempIncrDecLoad[2] = 1'b1;
	else 					   TempIncrDecLoad[3] = 1'b1;
  end
end

//EOP generation logic
always_comb 
begin
EOP = 1'b1;
if(CheckEOP )
  begin
    if (cif.ReqID == CH0 && StatusReg[0]) EOP = 1'b0;    
    else if (cif.ReqID == CH1 && StatusReg[1]) EOP = 1'b0; 
    else if (cif.ReqID == CH2 && StatusReg[2]) EOP = 1'b0;  
    else if (cif.ReqID == CH3 && StatusReg[3]) EOP = 1'b0;
    else 	EOP = 1'b1;					
  end
end
assign sif.nEOP =  EOP ? 1'b1 : 1'b0;

// position for each state
 enum {
  	iSI   = 0,
  	iS0   = 1,
  	iS1   = 2,
  	iS2   = 3,
  	iS3   = 4,
  	iS4   = 5
  } StateIndex;
  
 // fsm states in onehot encoding
 enum logic [5:0] {
  	SI   = 6'b000001 << iSI, 
  	S0   = 6'b000001 << iS0, 
  	S1   = 6'b000001 << iS1, 
  	S2   = 6'b000001 << iS2, 
  	S3   = 6'b000001 << iS3, 
  	S4   = 6'b000001 << iS4 
  	} State, NextState;

//reset logic for FSM
always_ff @(posedge sif.Clock)
begin
  if(sif.Reset)
    begin
      State     <= SI;
      sif.AEN   <= 1'b0;
      sif.ADSTB <= 1'b0;
    end
  else 
    begin
      State     <= NextState;
      sif.AEN   <= aen;
      sif.ADSTB <= adstb;
    end	
end

//Next State Logic
always_comb
begin
NextState = State;
unique case(1'b1)
  State[iSI]:
    begin
      if(cif.ValidReqID )  NextState = S0;
      else                 NextState = SI;
    end
  State[iS0]:
    begin
      if(sif.Hlda)         NextState = S1;
      else if(!sif.Hlda)   NextState = S0;
      else if(!sif.nEOP)   NextState = SI;
    end
  State[iS1]:
    begin
      if(!sif.nEOP)        NextState = SI;
      else                 NextState = S2;
    end
  State[iS2]:
    begin
      if(!sif.nEOP)        NextState = SI;
      else                 NextState = S3;
    end
  State[iS3]:
    begin
      if(!sif.nEOP)        NextState = SI;
      else                 NextState = S4;
    end
  State[iS4]:
	begin
	  if(UpAddrSTB)		   NextState = S1;
	  else if (!sif.nEOP)  NextState = SI;
	  else 				   NextState = S2;
	end
  default: NextState = State;
endcase    
end

//Output Logic
always_comb
begin
{aen, adstb, sif.Hrq } = 3'b0;
{TempAddrOut, WriteTransfer, ReadTransfer } = 3'b0;
{en_AddrBuf, en_DataIOBuf, TempAddrIncrDec} = 3'b0;
{RollOverCheck, CheckEOP} = 2'b0; 

unique case(1'b1)
  State[iSI]: begin sif.Hrq = 1'b0; end
  State[iS0]: begin sif.Hrq = 1'b1; end
  State[iS1]: begin sif.Hrq = 1'b1; aen = 1'b1; adstb = 1'b1; end
  State[iS2]: begin sif.Hrq = 1'b1; aen = 1'b1; TempAddrOut = 1'b1; en_DataIOBuf = 1'b1; en_AddrBuf = 1'b1;  end
  State[iS3]: begin sif.Hrq = 1'b1; aen = 1'b1; TempAddrOut = 1'b1; en_AddrBuf = 1'b1; RollOverCheck = 1'b1; end
  State[iS4]: begin sif.Hrq = 1'b1; aen = 1'b1; TempAddrOut = 1'b1; en_AddrBuf = 1'b1; WriteTransfer = 1'b1; ReadTransfer = 1'b1; TempAddrIncrDec = 1'b1; CheckEOP = 1'b1; end
  default:
    begin
      {aen, adstb, sif.Hrq } = 3'b0;
      {TempAddrOut, WriteTransfer, ReadTransfer } = 3'b0;
      {en_AddrBuf, en_DataIOBuf, TempAddrIncrDec} = 3'b0;
      {RollOverCheck, CheckEOP} = 2'b0;
  	end
endcase
end
endmodule

