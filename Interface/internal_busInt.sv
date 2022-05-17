//Internal bus interface
interface intBus (input logic CLK, input logic RESET);
	
	logic [15:0] Addr, WC; //address and word count
	logic [7:0] Data;
	logic [3:0] TC; // from Temp word count to status register
	logic [3:0] Req; // from request registers to status reigster
	
	
	
	modport read_buff( input Addr, WC,
					   input CLK, RESET);
	
	modport write_buff(output Addr, WC, 
					   input CLK, RESET);
					   
	modport temp_buff( inout Data,
					   input CLK, RESET);
					   
	modport status_reg( output Data, 
						input TC, Req,
						input CLK, RESET);
						
	modport cmd_reg( input Data,
					 input CLK, RESET);
					 
	modport req_reg ( output Req,
					  input Data, 
					  input CLK, RESET);
					  
	modport mode_reg( inout Data, 
					  input CLK, RESET);
					  
					   
	
endinterface