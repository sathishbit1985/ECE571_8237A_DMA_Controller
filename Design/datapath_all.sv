//DMA Datapath
module Datapath ( output logic [7:0] CommandRegOut, //Output from Command Register to Priority Block
				  output wire  [7:0] Address,		//Output from Temporary Address Regsister to external A7-A0 pins	
				  output logic [3:0] MaskRegOut,	//Output from Mask Register to Priority Block  	 	
				  output logic [7:2] ModeRegOut[3:0],  //Output from Mode Registers to Control Block	
				  inout  wire  [7:0] DB, 			//InOut  to CPU Databus, DB7-DB0
				  input  logic [3:0] PendingReq,    //Pending DMA Requests by Channel from Priority Block
				  ControlIF Ctrl,			   		//Control interface from Control block to Registers	
				  input  logic Clock, Reset);
				  
//Register Abbreviations: 
//BAR = Base Address Register,       BWC = Base Word Count Register
//CAR = Current Address Register,    TAR = Temporary Address Register,
//CWC = Current Word Count Register, TWC = Temporary Word Count Register				  

logic [15:0] TWCOut[3:0], TAROut[3:0];  //Temporary Word Count and Temporary Address Registers output
logic [15:0] IncOut[3:0], DecOut[3:0];  //Incrementor and decrementor outputs

//Outputs from Multiplexors to Address and Count Registers.
logic [15:0] Mux2CAR[3:0], Mux2TAR[3:0], Mux2CWC[3:0], Mux2TWC[3:0]; 
bit LOW = 1'b0;
wire [7:0] IntAddress; //internal address lines: IntAddress[7:0] to buffer and out to pins

	IntBus Bus(.*);	//Internal Data Bus			  

//Register Instantiations.
//Instance names will be Register[i].Command, Register[i].Mask, etc.
genvar i;
generate begin: Register //Couldnt add Register here as well as below
	//One of each Register
	CommandReg Command(Bus.CommandMod, CommandRegOut, Ctrl.CommandEnable, Ctrl.CommandLoad, Ctrl.MasterClear);
	
	MaskReg    Mask   (Bus.MaskMod, MaskRegOut, Ctrl.ClearMask, Ctrl.WriteAllMask, Ctrl.MaskLoad, Ctrl.MasterClear);
	
	StatusReg  Status (Bus.StatusMod, Ctrl.StatusEnable, Ctrl.MasterClear);

	AddressBuff AddrBuffer(Address[7:0], IntAddress, Ctrl.AddrBufEnbable);
	
	DataIOBuff DataBuffer (Bus.DataBufMod, DB,  Ctrl.DataBufEnable );

for(i = 0; i < 4; i++) begin
	//Create Bank of 4 Address Registers
	BaseAddressReg    BaseAddress    ( Bus.BARMod, 			  			  			   Ctrl.BARLoad[i], Ctrl.FF);
	CurrentAddressReg CurrentAddress ( Bus.CARMod,     		       		   Mux2CAR[i], Ctrl.CAREnable[i], Ctrl.CARLoad[i], Ctrl.FF, Ctrl.AddrMuxSel[i]);
	TempAddressReg	   TempAddress   ( Bus.TARMod, TAROut[i], IntAddress,  Mux2TAR[i], Ctrl.TAREnbale[i], Ctrl.TARLoad[i], Ctrl.FF, Ctrl.AddrMuxSel[i]);
	
	Mux2to1 CARMux( Mux2CAR[i], Bus.Data, TAROut[i], Ctrl.AddrMuxSel[i]); 
	Mux2to1 TARMux( Mux2TAR[i], Bus.Data, IncOut[i], Ctrl.AddrMuxSel[i]);
	IncDec Incrementor( IncOut[i], TAROut[i], ModeRegOut[i][5]); //ModeReg Bit 5 sets whether Address is Incremented/Decremented
	
	//Create Bank of 4 WordCount Registers
	BaseWordCountReg 	BaseWordCount    ( Bus.BWCMod, 						   Ctrl.BWCLoad[i], Ctrl.FF);
	CurrentWordCountReg CurrentWordCount ( Bus.CWCMod, 			   Mux2CWC[i], Ctrl.CWCEnable[i], Ctrl.CWCLoad[i], Ctrl.FF, Ctrl.WCMuxSel[i]);				
	TempWordCountReg	TempWordCount    ( Bus.TWCMod,  TWCOut[i], Mux2TWC[i], Ctrl.TWCEnable[i], Ctrl.TWCLoad[i], Ctrl.FF, Ctrl.WCMuxSel[i]);
			  
	Mux2to1 CWCMux( Mux2CWC[i], Bus.Data, TWCOut[i], Ctrl.WCMuxSel[i]);
	Mux2to1 TWCMux( Mux2TWC[i], Bus.Data, DecOut[i], Ctrl.WCMuxSel[i]);
	IncDec Decrementor( DecOut[i], TWCOut[i], LOW); 	//INCDEC tied low to be Decrementor
	
	//create Bank of 4 Mode Registers
	ModeReg Mode( Bus.ModeMod, ModeRegOut[i], Ctrl.ModeLoad[i]);
	end
end
endgenerate
		  
endmodule



			
//Current address *4, 16bits
//*********LIST BITS********
module CurrentAddressReg ( IntBus.CARMod Bus,				
				           input logic [15:0] CAIn,   //Current Address In
				           input logic Enable, Load, FF, SEL);

	logic [15:0] CAddress;

	assign Bus.Data = (Enable && FF) ? CAddress[15:8] : 
					  (Enable) ? CAddress[7:0] : 'z;

	always @(posedge Bus.Clock) 
		if (Bus.Reset) CAddress <= '0;
		else if (Load && SEL && FF) CAddress[15:8] <= CAIn[15:8];
		else if (Load && SEL)       CAddress[7:0]  <= CAIn[7:0];
		else if (Load) 			    CAddress 	   <= CAIn; 
				   
endmodule



//current word *4, 16bits, instantiate 4
//Read and Write
//*********LIST BITS********
module CurrentWordCountReg ( IntBus.CWCMod Bus,			
						     input  logic [15:0] CWCIn,  //Current Word Count In
						     input  logic Enable, Load, FF, SEL);

	logic [15:0] CWordCount;

	assign Bus.Data = (Enable && FF) ? CWordCount[15:8] : 
					  (Enable) ? CWordCount[7:0] : 'z;

	always @(posedge Bus.Clock)
		if (Bus.Reset) CWordCount <= '0;
		else if (Load && SEL && FF) CWordCount[15:8] <= CWCIn[15:8];
		else if (Load && SEL )		CWordCount[7:0]  <= CWCIn[7:0];
		else if (Load)		        CWordCount       <= CWCIn;	
		
endmodule



// Temp address *4, 16bits
//*********LIST BITS********
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
		else if (Load && SEL && FF) TAddress[15:8] <= TARIn[15:8];
		else if (Load && SEL) 	    TAddress[7:0]  <= TARIn[7:0];
		else if (Load)				TAddress       <= TARIn;
			  
endmodule



//Temp word *4, 16bits, 
//*********LIST BITS********
module TempWordCountReg( IntBus.TWCMod Bus,   	  	  //Output to Internal Data Bus
						 output logic [15:0] TWCOut,  //Temporary Word Count Out To Decrementor  
						 output logic TerminalCount,  //Output to Status Register indicating if Terminal count has been reached
					     input  logic [15:0] TWCIn,   //Temporary Word Count in
					     input  logic Enable, Load, FF, SEL);
				  
	logic [15:0] TWordCount;

	assign Bus.Data = (Enable && FF) ? TWordCount[15:8] : 
					  (Enable) ? TWordCount[7:0] : 'z;
					  
	assign TWCOut = (Enable) ? TWordCount : 'z;
	assign TerminalCount = (TWordCount != 16'hFFFF);

	always @(posedge Bus.Clock)
		if (Bus.Reset) TWordCount <= '0;
		else if (Load && SEL && FF) TWordCount[15:8] <= TWCIn[15:8];	
		else if (Load && SEL)       TWordCount[7:0]  <= TWCIn[7:0];
		else if (Load)				TWordCount       <= TWCIn;
				  
endmodule



//Base Address *4, 16bits
//*********LIST BITS********
module BaseAddressReg ( IntBus.BARMod Bus,  		//Input from Internal Data Bus
				        input logic Load, FF);

	logic [15:0] BAddress;


	always_ff @(posedge Bus.Clock)
		if (Bus.Reset) BAddress <= '0;
		else if (Load && FF) BAddress[15:8] <= Bus.Data;
		else if (Load) 		 BAddress[7:0]  <= Bus.Data;
				   
endmodule



//Base word count *4, 16bits,
//*********LIST BITS********
module BaseWordCountReg ( IntBus.BWCMod Bus, 		 //Input from Internal Data Bus
				          input logic Load, FF);

	logic [15:0] BWordCount;
	
	always_ff @(posedge Bus.Clock)
		if (Bus.Reset) BWordCount <= '0;
		else if (Load && FF) BWordCount[15:8] <= Bus.Data;
		else if (Load) 		 BWordCount[7:0]  <= Bus.Data;

endmodule



//Command Register
//*********LIST BITS********
module CommandReg(IntBus.CommandMod Bus, 					//Input from Internal Data Bus
			      output logic CmdOut,						//Output to Priority and Control Blocks
			      input  logic Enable, Load, MasterClear);  

	localparam DISABLE = 8'b0000_0100; //Bit pattern for controller disable

	logic [7:0] Command;

	assign CmdOut = (Enable) ? Command : 'z;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset || MasterClear) Command <= DISABLE; //Disable DMA Controller on Reset
		else if (Load) Command <= Bus.Data;
	
endmodule				   
					

//Mode is Write Only by CPU. The mode Can be read by the Control Block 
//through ModeOut.
//*********LIST BITS********
module ModeReg( IntBus.ModeMod Bus, 		 //Input from Internal Data Bus 
			    output logic [7:2] ModeOut,  //Output to Control Block
			    input logic  Load);

	logic [7:2] Mode;

	assign ModeOut = Mode;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset) Mode <= '0;
		else if (Load) Mode <= Bus.Data[7:2];

endmodule

 

//Mask is set/reset by software commands
//Mask[0] is channel 0, Mask[1] is Channel 1, etc.
//*********LIST BITS********
module MaskReg ( IntBus.MaskMod Bus,				//Input from internal Data Bus
				 output logic [3:0] MaskOut,		//Output to Priority Block
				 input  ClearMask, SetAllMask, 		//Signals to Clear/Set All bits 
				 input  logic Load, MasterClear);

	logic [3:0] Mask;

	assign MaskOut = Mask;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset || MasterClear || SetAllMask)  Mask <= '1;	//Masks are Set on Reset or Master Clear
		else if (ClearMask) Mask <= '0;	//Clear Mask Command Clears all Masks
		else if (Load)      Mask <= Bus.Data;
		
	
endmodule




//Status Register to be Read by the CPU. 
//The Upper 4 bits indicate whether a DMA request is pending.
//The Lower 4 bits indicate whether a terminal  count has been reached for that channel. 
//The Status is Reset upon begin Read by the CPU. 
//*********LIST BITS********
module StatusReg( IntBus.StatusMod Bus,					//Output to Internal Data Bus
				  input PendingReq, TerminalCount, 	
				  input logic Enable, MasterClear);

	logic [7:0] Status;

	assign Bus.Data = (Enable) ? Status : 'z;

	always_ff @(posedge Bus.Clock)
		if (Bus.Reset || MasterClear || Enable) Status <= '0;
		else 									Status <= {PendingReq, TerminalCount};
	
endmodule

 

/*********BUFFERS*************/
//Address, 4bits 
module AddressBuff #( parameter SIZE = 8)
				    ( output logic [SIZE-1:0] AddressOut,
				      input  logic [SIZE-1:0] AddressIn, 
				      input  logic Enable);
					  
assign AddressOut = (Enable) ? AddressIn : 'z;
	
endmodule



//Data, 16bits,
//
module DataIOBuff #( parameter SIZE = 8)
				  ( IntBus.DataBufMod Bus, 
				   inout [SIZE-1:0] DB, 	   //To external DB[7:0]     
				   input Enable, Load); //Controls To Read or Write internal Bus from External DB[7:0].  
	
//assign  DB = (Enable) ? Bus.Data : 'z;
//assign  Bus.Data = (Load) ? DB :'z;	

always_comb begin
	if (Load) Bus.Data = DB;
	end
	
assign DB = (Enable) ? Bus.Data : 'z; 
	
endmodule			



//Multiplexers
module Mux2to1 #( parameter SIZE = 16) 
  				( output logic [SIZE-1:0] Out, 
				  input  logic [SIZE>>1 -1:0] In1,
                  input  logic [SIZE-1:0] In2, 
                  input  logic Select);

	assign Out = (Select) ? In1 : In2;

endmodule


//Incrementor/Decrementor 
module IncDec #( parameter SIZE = 16)
			   ( output logic [SIZE-1:0] Out, 
				 input  logic [SIZE-1:0] In,  
				 input  logic INCDEC);        //If INCDEC = 1, input will be incremented, else Decremented.
				 
	always_comb begin 		   
		if (INCDEC) Out = In + 1;
		else   		Out = In - 1;
	end
			   
endmodule



//Internal bus interface with modports for Registers
interface IntBus (input logic Clock, input logic Reset);
	
	wire [7:0]  Data;
	
	///*****CHANGE TO WRITE MODPORT
	//Command Register
	modport CommandMod ( input Data,  input Clock, Reset);
	//Mode Register				 
	modport ModeMod( input Data,  input Clock, Reset);
	
	//Mask Register
	modport MaskMod( input Data,  input Clock, Reset);


	///*****CHANGE TO R/W MODPORT
	//Data buffer
	modport DataBufMod( inout Data);
	
	//Base Address Register 
	modport BARMod ( inout Data,  input Clock, Reset);
							  
	//Base Word Count Register 					   
	modport BWCMod ( inout Data,  input Clock, Reset);	
			

	///*****CHANGE TO READ MODPORT
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



//Datapath Control interface. Load and Enable for each Registers
//as well as Master Clear. FF controls Upper or Lower Byte select on 
//Some registers to be output to external Data Line DB7-DB0;
interface ControlIF;

	logic [3:0] ModeLoad;  	  					  //Mode Register 
	logic [3:0] BARLoad; 		 				  //Base Address Registers
	logic [3:0] CAREnable,   	 CARLoad;  		  //Current Address Registers
	logic [3:0] TAREnbale,   	 TARLoad;  		  //Temporary Address Registers 
	logic [3:0] BWCEnable, 		 BWCLoad; 		  //Base Word Count Registers 
	logic [3:0] CWCEnable,       CWCLoad; 		  //Current Word Count Registers
	logic [3:0] TWCEnable, 		 TWCLoad; 		  //Temporary Word Count Registers
	logic [3:0] AddrMuxSel, 	 WCMuxSel; 		  //Select lines to Address and Word Count Multiplexors
	logic 		CommandEnable, 	 CommandLoad;	  //Command Register
	logic 		MaskLoad; 	          		  //Mask Register
	logic 		StatusEnable;   				  //Status Register
	logic 		AddrBufEnbable;					  //Address Buffer
	logic 		DataBufEnable; 				  //Data Buffer Enable
	logic 		DataBufRead, DataBufWrite;	  //Data Buffer Read/Write	
	logic		ClearMask,    WriteAllMask;       //Clear and Set mask Registers
	logic 		MasterClear,     FF ;
	


  //Modport For Timing Control Logic Block
  modport TCL (
	output ModeLoad,   
	output BARLoad,  
	output CAREnable,   	CARLoad,  
	output TAREnbale,   	TARLoad,  
	output BWCEnable, 		BWCLoad, 
	output CWCEnable, 		CWCLoad, 
	output TWCEnable, 		TWCLoad, 
	output AddrMuxSel, 	    WCMuxSel,
	output CommandEnable, 	CommandLoad, 
	output MaskLoad, 	        
	output StatusEnable,   
	output AddrBufEnbable, 
	output DataBufEnable,
    output DataBufRead, DataBufWrite,	
	output ClearMask,    WriteAllMask,
	output MasterClear,     FF
	);


  //Modport for Datapath
  modport Datapath (  
	input ModeLoad,   
	input BARLoad,  
	input CAREnable,   	   CARLoad,  
	input TAREnbale,   	   TARLoad,  
	input BWCEnable, 	   BWCLoad, 
	input CWCEnable, 	   CWCLoad, 
	input TWCEnable, 	   TWCLoad, 
	input AddrMuxSel, 	   WCMuxSel,
	input CommandEnable,   CommandLoad, 
	input MaskLoad, 	      
	input StatusEnable,   
	input AddrBufEnbable,  
    input DataBufRead, DataBufWrite,
	input ClearMask,    WriteAllMask,
	input MasterClear,     FF 
	);
	
endinterface