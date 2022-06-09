//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Kirk Chapman
// Module Name: DMA Datapath, Registers, Internal Bus Interface
// Project Name: DMA Controller 
////////////////////////////////////////////////////////////////////////////////////


module Datapath ( output logic [7:0] CommandRegOut,    //Output from Command Register to Priority Block
				  output wire  [7:0] Address,		   //Output from Temporary Address Regsister to external A7-A0 pins	
				  output logic [3:0] MaskRegOut,	   //Output from Mask Register to Priority Block  	 	
				  output logic [7:2] ModeRegOut[4],    //Output from Mode Registers to Control Block	
				  inout  wire  [7:0] DB, 			   //InOut  to CPU Databus, DB7-DB0
				  input  logic [3:0] PendingReq,       //Pending DMA Requests by Channel from Priority Block
				  ControlIF.Datapath Ctrl,			   //Control interface from Control block to Registers,
				  input  logic Clock, Reset);


/*************************************************************************************				  
*Register Abbreviations: 
*BAR = Base Address Register,       BWC = Base Word Count Register
*CAR = Current Address Register,    TAR = Temporary Address Register,
*CWC = Current Word Count Register, TWC = Temporary Word Count Register				  
*************************************************************************************/


logic [15:0] TWCOut[3:0], TAROut[3:0];  //Temporary Word Count and Temporary Address Registers output
logic [15:0] IncOut[3:0], DecOut[3:0];  //Incrementor and decrementor outputs

//Outputs from Multiplexors to Address and Count Registers.
logic [15:0] Mux2CAR[3:0], Mux2TAR[3:0], Mux2CWC[3:0], Mux2TWC[3:0]; 
bit LOW = 1'b0;
wire [7:0] IntAddress; //internal address lines: IntAddress[7:0] to buffer and out to pins
logic [3:0] TerminalCount;

	IntBus Bus(.*);	//Internal Data Bus				  

//Register Instantiations.
//Instance names will be Register.Command, Register.Mask, etc.
genvar i;
generate begin: Register //Couldnt add Register here as well as below
	//One of each Register
	CommandReg Command(Bus.CommandMod, CommandRegOut, Ctrl.CommandLoad, Ctrl.MasterClear);
	
	MaskReg    Mask   (Bus.MaskMod, MaskRegOut, Ctrl.ClearMask, Ctrl.WriteAllMask, Ctrl.MaskLoad, Ctrl.MasterClear);
	
	StatusReg  Status (Bus.StatusMod, PendingReq, TerminalCount,  Ctrl.StatusEnable, Ctrl.MasterClear);

	AddressBuff AddrBuffer(Address[7:0], IntAddress, Ctrl.AddrBufEnbable);
	
	DataIOBuff DataBuffer (Bus.DataBufMod, DB,  Ctrl.DataBufEnable, Ctrl.DataBufLoad);

for(i = 0; i < 4; i++) begin:i 
	//Create Bank of 4 Address Registers
	BaseAddressReg    BaseAddress    ( Bus.BARMod, Ctrl.BARLoad[i], Ctrl.FF);
	CurrentAddressReg CurrentAddress ( Bus.CARMod, Mux2CAR[i], Ctrl.CAREnable[i], Ctrl.CARLoad[i], Ctrl.FF, Ctrl.AddrMuxSel[i]);
	TempAddressReg	   TempAddress   ( Bus.TARMod, TAROut[i], IntAddress,  Mux2TAR[i], Ctrl.TAREnbale[i], Ctrl.TARLoad[i], Ctrl.FF, Ctrl.AddrMuxSel[i]);
	
	Mux2to1 CARMux( Mux2CAR[i], Bus.Data, TAROut[i], Ctrl.AddrMuxSel[i]); 
	Mux2to1 TARMux( Mux2TAR[i], Bus.Data, IncOut[i], Ctrl.AddrMuxSel[i]);
	IncDec Incrementor( IncOut[i], TAROut[i], ModeRegOut[i][5]); //ModeReg Bit 5 sets whether Address is Incremented/Decremented
	
	//Create Bank of 4 WordCount Registers
	BaseWordCountReg 	BaseWordCount    ( Bus.BWCMod, Ctrl.BWCLoad[i], Ctrl.FF);
	CurrentWordCountReg CurrentWordCount ( Bus.CWCMod, Mux2CWC[i], Ctrl.CWCEnable[i], Ctrl.CWCLoad[i], Ctrl.FF, Ctrl.WCMuxSel[i]);				
	TempWordCountReg	TempWordCount    ( Bus.TWCMod, TWCOut[i], TerminalCount[i], Mux2TWC[i], Ctrl.TWCEnable[i], Ctrl.TWCLoad[i], Ctrl.FF, Ctrl.WCMuxSel[i]);
			  
	Mux2to1 CWCMux( Mux2CWC[i], Bus.Data, TWCOut[i], Ctrl.WCMuxSel[i]);
	Mux2to1 TWCMux( Mux2TWC[i], Bus.Data, DecOut[i], Ctrl.WCMuxSel[i]);
	IncDec Decrementor( DecOut[i], TWCOut[i], LOW); 	//INCDEC tied low to be Decrementor
	
	//create Bank of 4 Mode Registers
	ModeReg Mode( Bus.ModeMod, ModeRegOut[i], Ctrl.ModeLoad[i]);
	end
end
endgenerate
		  
endmodule



/***************************			
*Current address  
*16 bits, Read and Write
***************************/
module CurrentAddressReg ( IntBus.CARMod Bus,				
				           input logic [15:0] CAIn,   //Current Address In
				           input logic Enable, Load, FF, SEL);

	logic [15:0] CAddress;

	assign Bus.Data = (Enable && FF) ? CAddress[15:8] : 
					  (Enable) ? CAddress[7:0] : 'z;

	always @(posedge Bus.Clock) 
		if (Bus.Reset) CAddress <= '0;
		else if (Load && SEL && FF) CAddress[15:8] <= CAIn[7:0];
		else if (Load && SEL)       CAddress[7:0]  <= CAIn[7:0];
		else if (Load) 			    CAddress 	   <= CAIn;
		else 						CAddress       <= CAddress;
				   
endmodule



/***************************			
*Current Word Count  
*16 bits, Read and Write
***************************/
module CurrentWordCountReg ( IntBus.CWCMod Bus,			
						     input  logic [15:0] CWCIn,  //Current Word Count In
						     input  logic Enable, Load, FF, SEL);

	logic [15:0] CWordCount;

	assign Bus.Data = (Enable && FF) ? CWordCount[15:8] : 
					  (Enable) ? CWordCount[7:0] : 'z;

	always @(posedge Bus.Clock)
		if (Bus.Reset) CWordCount <= '0;
		else if (Load && SEL && FF) CWordCount[15:8] <= CWCIn[7:0];
		else if (Load && SEL )		CWordCount[7:0]  <= CWCIn[7:0];
		else if (Load)		        CWordCount       <= CWCIn;
		else         		        CWordCount       <= CWordCount;			
		
endmodule



/***************************			
*Temporary Address  
*16 bits Read and Write
*Lower address bits out to Ports
*Output to Incrementor/Decrementor 
***************************/
module TempAddressReg( IntBus.TARMod Bus,       //Output to Internal Data Bus
					   output logic [15:0] TAROut, //Temporary Address Register Out to Inc/Dec
					   output logic [7:0]  LAddrOut, //Output to Address lines A[7:0]
					   input  logic [15:0] TARIn,  //Temporary Address Register In 
					   input  logic Enable, Load, FF, SEL);

	logic [15:0] TAddress;				  

	assign Bus.Data = (Enable && FF) ? TAddress[15:8] : 
					  (Enable) ? TAddress[7:0] : 'z;
					  
	assign TAROut   = (Enable) ? TAddress : 'z;
	assign LAddrOut = (Enable) ? TAddress[7:0] : 'z;



	always @(posedge Bus.Clock)
		if (Bus.Reset) TAddress <= '0;
		else if (Load && SEL && FF) TAddress[15:8] <= TARIn[7:0];
		else if (Load && SEL) 	    TAddress[7:0]  <= TARIn[7:0];
		else if (Load)				TAddress       <= TARIn;
		else 						TAddress	   <= TAddress;
			  
endmodule



/***************************			
*Temporary Word Count
*16 bits Read and Write
*Lower address bits out to Ports
*Output to Incrementor/Decrementor 
***************************/
module TempWordCountReg( IntBus.TWCMod Bus,   	  	  //Output to Internal Data Bus
						 output logic [15:0] TWCOut,  //Temporary Word Count Out To Decrementor  
						 output logic TerminalCount,  //Output to Status Register indicating if Terminal count has been reached
					     input  logic [15:0] TWCIn,   //Temporary Word Count in
					     input  logic Enable, Load, FF, SEL);
				  
	logic [15:0] TWordCount;

	assign Bus.Data = (Enable && FF) ? TWordCount[15:8] : 
					  (Enable) ? TWordCount[7:0] : 'z;
					  
	assign TWCOut = (Enable) ? TWordCount : 'z;
	assign TerminalCount = (TWordCount == 16'hFFFF);

	always @(posedge Bus.Clock)
		if (Bus.Reset) TWordCount <= '0;
		else if (Load && SEL && FF) TWordCount[15:8] <= TWCIn[7:0];	
		else if (Load && SEL)       TWordCount[7:0]  <= TWCIn[7:0];
		else if (Load)				TWordCount       <= TWCIn;
		else 						TWordCount		 <= TWordCount;
				  
endmodule


/**********************************************
*Base Address 
*16bits Write Only
*Used to Set Current Address in Auto Initialize
*Created for future Upgrades
***********************************************/
module BaseAddressReg ( IntBus.BARMod Bus,  		//Input from Internal Data Bus
				        input logic Load, FF);

	logic [15:0] BAddress;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset) BAddress <= '0;
		else if (Load && FF) BAddress[15:8] <= Bus.Data;
		else if (Load) 		 BAddress[7:0]  <= Bus.Data;
		else 				 BAddress       <= BAddress;
				   
endmodule



/**********************************************
*Base Word Count 
*16bits Write Only
*Used to Set Current Word Count in Auto Initialize
*Created for future Upgrades
***********************************************/
module BaseWordCountReg ( IntBus.BWCMod Bus, 		 //Input from Internal Data Bus
				          input logic Load, FF);

	logic [15:0] BWordCount;
	
	always_ff @(posedge Bus.Clock)
		if (Bus.Reset) BWordCount <= '0;
		else if (Load && FF) BWordCount[15:8] <= Bus.Data;
		else if (Load) 		 BWordCount[7:0]  <= Bus.Data;
		else 				 BWordCount       <= BWordCount;

endmodule


/**********************************************
*Command Register
*Contains settings for programing of Controller
*8 Bits, Write Only
*Output to Priority Block
***********************************************/
module CommandReg(IntBus.CommandMod Bus, 			//Input from Internal Data Bus
			      output logic [7:0] CmdOut,		//Output to Priority and Control Blocks
			      input  logic Load, MasterClear);  

	localparam DISABLE = 8'b0000_0100; //Bit pattern for controller disable

	logic [7:0] Command;

	assign CmdOut = Command;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset || MasterClear) Command <= DISABLE; //Disable DMA Controller on Reset
		else if (Load) Command <= Bus.Data;
	
endmodule				   
					
/**********************************************
*Mode Register
*Contains Mode Settings for a given Channel
*6 bits, Write Only
*Output to the Control Block 
***********************************************/
module ModeReg( IntBus.ModeMod Bus, 		 //Input from Internal Data Bus 
			    output logic [7:2] ModeOut,  //Output to Control Block
			    input logic  Load);

	logic [7:2] Mode;

	assign ModeOut = Mode;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset) Mode <= '0;
		else if (Load) Mode <= Bus.Data[7:2];
		else           Mode <= Mode;

endmodule

 
/**********************************************
*Mask Register
*4 Bits, Write and Set/Reset
*Sets bits to Mask(Disable) Channel DMA Requests
*Mask is set/reset by software commands, Can be written
*Mask[0] is channel 0, Mask[1] is Channel 1, etc.
*Output to Priority Block
***********************************************/
module MaskReg ( IntBus.MaskMod Bus,				//Input from internal Data Bus
				 output logic [3:0] MaskOut,		//Output to Priority Block
				 input  ClearMask,  WriteAllMask,		        //Signals to Clear/Set All bits 
				 input  logic Load, MasterClear);

	logic [3:0] Mask;

	assign MaskOut = Mask;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset || MasterClear || WriteAllMask)  Mask <= '1;	//Masks are Set on Reset or Master Clear
		else if (ClearMask) Mask <= '0;	//Clear Mask Command Clears all Masks
		else if (Load)      Mask <= Bus.Data;
		else                Mask <= Mask;
		
	
endmodule



/**********************************************
*Status Register 
*8 Bits, Read Only
*Status[7:4] indicate whether a DMA request is pending, from Priority Block
*Status[3:0] indicate whether a terminal  count has been reached for that channel. 
*The Status is Reset upon being Read by the CPU. 
***********************************************/
module StatusReg( IntBus.StatusMod Bus,					//Output to Internal Data Bus
				  input [3:0] PendingReq, TerminalCount, 	
				  input logic Enable, MasterClear);

	logic [7:0] Status;

	assign Bus.Data = (Enable) ? Status : 'z;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset || MasterClear || Enable) Status <= '0;
		else 									Status <= {PendingReq, TerminalCount};
	
endmodule

 
/**********************************************
				   BUFFERS, Etc
***********************************************/

/**********************************************
*Address Buffer 
*8 Bits
*Outputs lower 8 bits of Address to External Pins 
***********************************************/
module AddressBuff #( parameter SIZE = 8)
				    ( output logic [SIZE-1:0] AddressOut,
				      input  logic [SIZE-1:0] AddressIn, 
				      input  logic Enable);
					  
assign AddressOut = (Enable) ? AddressIn : 'z;
	
endmodule



/**********************************************
*Data Buffer 
*8 Bits
*In/Out 8 bits of Data to External Pins 
***********************************************/
module DataIOBuff #( parameter SIZE = 8)
				  ( IntBus.DataBufMod Bus, 
				   inout [SIZE-1:0] DB, 	   //To external DB[7:0]     
				   input Enable, Load); //Controls To Read or Write internal Bus from External DB[7:0].  
	
always_comb begin
	if (Load) Bus.Data = DB;
	end
	
assign DB = (Enable) ? Bus.Data : 'z; 
	
endmodule			


/**********************************************
*Multiplexer 
*Asymetrical Inputs. In2 is half size of In1
*Output is full size. In1 is padded to output.
*Allows for 8bit input from Data, as well as 
*16 bit input from incrementor, Temp Regs 
***********************************************/
module Mux2to1 #( parameter SIZE = 16) 
  				( output logic [SIZE-1:0] Out, 
				  input  logic [(SIZE>>1)-1:0] In1,
                  input  logic [SIZE-1:0] In2, 
                  input  logic Select);

    localparam HALF = SIZE >> 1;

	assign Out = (Select) ? { {HALF{1'b1}}, In1} : In2; //extend In1 to be SIZE bits to match output size

endmodule

/**********************************************
*Incrementor/Decrementor 
*Can be set to Increment or Decrement by setting 
*INCDEC input
***********************************************/
module IncDec #( parameter SIZE = 16)
			   ( output logic [SIZE-1:0] Out, 
				 input  logic [SIZE-1:0] In,  
				 input  logic INCDEC);        //If INCDEC = 1, input will be incremented, else Decremented.
				 
	always_comb begin 		   
		if (INCDEC) Out = In + 1;
		else   		Out = In - 1;
	end
			   
endmodule


/**********************************************
*Internal bus interface with modports for Registers
***********************************************/
interface IntBus (input logic Clock, input logic Reset);
	
	logic [7:0] Data;
	
	//Command Register
	modport CommandMod ( input Data,  input Clock, Reset);
	//Mode Register				 
	modport ModeMod( input Data,  input Clock, Reset);
	
	//Mask Register
	modport MaskMod( input Data,  input Clock, Reset);


	
	//Data buffer
	modport DataBufMod( inout Data);
	
	//Base Address Register 
	modport BARMod ( inout Data,  input Clock, Reset);
							  
	//Base Word Count Register 					   
	modport BWCMod ( inout Data,  input Clock, Reset);	
			


	//Current Word Count Registers						   
	modport CWCMod ( output Data, input Clock, Reset);
	
	//Current Address Register
	modport CARMod ( output Data, input Clock, Reset);
			
	//Temporary Address Registers		
	modport TARMod ( output Data, input Clock, Reset);

	//Temporary Word Count Registers
	modport TWCMod ( output Data, input Clock, Reset);	
	
	//Status Register				   
	modport StatusMod  ( output Data, input Clock, Reset);

endinterface