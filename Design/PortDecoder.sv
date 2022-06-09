module PortDecoder (SystemBusIF.PortDecoder PortDecoder, output logic nCS);
	localparam DMA_ID = 4'hF;
	
	assign nCS = ((PortDecoder.Address[7:4] == DMA_ID) && (~PortDecoder.nIOW||~PortDecoder.nIOR)) ? 1'b0 : 1'b1;
endmodule