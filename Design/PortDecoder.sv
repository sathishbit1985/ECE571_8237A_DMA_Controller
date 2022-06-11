//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Ramesh Chandar Aniruddh Punnai
// Module Name: Port Decoder
// Project Name: DMA Controller
//////////////////////////////////////////////////////////////////////////////////

module PortDecoder (SystemBusIF.PortDecoder PortDecoder, output logic nCS);
	localparam DMA_ID = 12'hFFF;
	
	assign nCS = ((PortDecoder.Address[15:4] == DMA_ID) && (~PortDecoder.nIOW||~PortDecoder.nIOR)) ? 1'b0 : 1'b1;
endmodule
