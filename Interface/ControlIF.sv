//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Kirk Chapman
// Module Name: Control Interface: Control Signals to be sent from TCL To Datapath
// Project Name: DMA Controller 
////////////////////////////////////////////////////////////////////////////////////
interface ControlIF();

	logic [3:0] ModeLoad;  	  					  //Mode Register 
	logic [3:0] BAREnable,       BARLoad; 		  //Base Address Registers
	logic [3:0] CAREnable,   	 CARLoad;  		  //Current Address Registers
	logic [3:0] TAREnbale,   	 TARLoad;  		  //Temporary Address Registers 
	logic [3:0] BWCEnable, 		 BWCLoad; 		  //Base Word Count Registers 
	logic [3:0] CWCEnable,       CWCLoad; 		  //Current Word Count Registers
	logic [3:0] TWCEnable, 		 TWCLoad; 		  //Temporary Word Count Registers
	logic [3:0] AddrMuxSel, 	 WCMuxSel; 		  //Select lines to Address and Word Count Multiplexors
	logic 		CommandEnable, 	 CommandLoad;	  //Command Register
	logic 		MaskLoad; 	          		      //Mask Register
	logic 		StatusEnable;   				  //Status Register
	logic 		AddrBufEnbable;					  //Address Buffer
	logic 		DataBufEnable, DataBufLoad; 	  //Data Buffer Enable
	logic		ClearMask,    WriteAllMask;       //Clear and Set mask Registers
	logic 		MasterClear,     FF;
	logic [3:0] RollOverCheck;
	
	logic ValidReqID;
	logic [1:0] ReqID;
	


  //Modport For Timing Control Logic Block
  modport TCL (
	output ModeLoad,   
	output BAREnable,       BARLoad,  
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
	output DataBufEnable, DataBufLoad,
	output ClearMask,    WriteAllMask,
	output MasterClear,     FF,
	output RollOverCheck,
	
	input ValidReqID, ReqID
	);


  //Modport for Datapath
  modport Datapath (  
	input ModeLoad,   
	input BAREnable,       BARLoad,  
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
	input DataBufEnable, DataBufLoad,
	input ClearMask,    WriteAllMask,
	input MasterClear,     FF,
	input ReqID,
	input RollOverCheck
	);
	
  //Modprt for Priority Encoder	
  modport PE (
	output ValidReqID,
	output ReqID
	);
	
endinterface