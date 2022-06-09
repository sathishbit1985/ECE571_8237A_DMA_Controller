interface SystemBusIF(input logic Clock, Reset);
	
	wire  [7:0]  Data;
	logic [15:0] Address;
	
	logic nMEMR;
	logic nMEMW;
	wire  nIOR;
	wire  nIOW;
	
	logic Hlda;
	logic Hrq;
	logic [3:0] Dack;
	logic [3:0] Dreq;
	logic AEN;
	logic ADSTB;
	wire  nEOP;
	
	
	modport BFM8086 (
			input Clock,
			input Reset,
			input Hrq,
			input AEN,
			input ADSTB,
			
			output nMEMW,
			output nMEMR,
			output nIOR,
			output nIOW,
			output Address,
			output Hlda,
			
			inout  Data
			);
	
	modport DMA(
			input Clock,
			input Reset,
			input Hlda,
			input Dreq,
	
			output Dack,
			output nMEMR,
			output nMEMW,
			output AEN,
			output ADSTB,
			output Hrq,
			
			inout nIOR,
			inout nIOW,
			inout Address,
			inout Data,
			inout nEOP
			);
			
	modport IODevice(
			input Clock,
			input Reset,
			input Dack,
			input nIOR,
			input nIOW,
			
			inout Data,	
			output Dreq			
			); 
			
	modport PortDecoder (
			input Address,
			input nIOR,
			input nIOW
			);
	
	modport AddressLatch (
			input AEN,
			input ADSTB,
			
			output Address 
			);
	
	modport MemoryDevice(
	        input Clock,
			input nMEMR,
			input nMEMW,
			input Address,
			
			inout Data
			);
endinterface