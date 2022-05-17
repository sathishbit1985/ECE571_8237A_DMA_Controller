interface systemBUS(input logic clock, reset);
	logic [7:0]DATA;
	logic [15:0]ADDR;
	logic nMEMR;
	logic nMEMW;
	logic nIOR;
	logic nIOW;
	logic Ready;
	logic HLDA;
	logic HRQ;
	logic AEN;
	logic ADSTB;
	logic DEN;
	logic nCS;
	
	modport processorThread (
			output HLDA,
			input HRQ,
			output MEMWn,
			output MEMRn,
			output IORn,
			output IOWn,
			output [15:0]ADDR,
			inout [7:0]DATA,
			input BUSEN
		);
	
	modport dmaThread(
		output MEMRn,
		output MEMWn,
		inout IORn,
		inout IOWn,
		input AEN,
		inout [7:4]A;
		output ADSTB,
		input HLDA,
		output HRQ,
		inout DB
	);
	
	task Write;
		input logic [7:0]DMAaddress;
		input logic [7:0]AddressReg;
		input logic [7:0]Data;
		input bit WR;
		
		enum {
		iT1=0;
		iT2=1;
		iT3=2;
		iT4=3;}stateposition;
		
		enum logic [3:0] {
			T1   = 4'b0001 << iT1, 
			T2   = 4'b0001 << iT2, 
			T3   = 4'b0001 << iT3, 
			T4   = 4'b0001 << iT4, 
  
		} State, next_state;
		
		always_ff @(posedge clock) begin
			if(reset)
				State <= T1;
			else
				State <= next_state;
		end
		
		
		always_comb begin
			ready=1;
			nMEMW=1;
			nCS=1;
			nIOW=1;
			nIOR=1;
			nMEMR=1;
			if(!WR) begin
				unique case (1'b1)
					state[iT1]: begin
						//ALE=1;
						ADDR = AddressReg;
						next_state=T2;
					end
					state[iT2]: begin
						//ALE = 0;
						nMEMW=0;
						next_state=T3;
					end
					state[iT3]: begin
						DataBus = Data;
						next_state = T4;
					end	
					state[iT4]: begin
						nMEMW=1;							
						next_state = T1;
					end
				endcase
			end
			else begin
				unique case (1'b1)
					state[iT1]: begin
						//ALE=1;
						ADDR = AddressReg;
						next_state=T2;
					end
					state[iT2]: begin
						//ALE = 0;
						nIOW=0;
						DATA = Data;
						next_state=T3;
					end
					state[iT3]: begin
						DataBus = Data;
						next_state = T4;
					end	
					state[iT4]: begin
						nIOW=1;
						next_state = T1;
					end
				endcase
				nCS = ~(DMAaddress==AddressReg);
			end
		end
	endtask
	
	task ReadMem;
		input logic [7:0]DMAaddress;
		input logic [7:0]AddressReg;
		logic DEN;
		input bit RD;
		
		enum {
		iT1=0;
		iT2=1;
		iT3=2;
		iT4=3;}stateposition;
		
		enum logic [3:0] {
			T1   = 4'b0001 << iT1, 
			T2   = 4'b0001 << iT2, 
			T3   = 4'b0001 << iT3, 
			T4   = 4'b0001 << iT4, 
  
		} State, next_state;
		
		always_ff @(posedge clock) begin
			if(reset)
				State <= T1;
			else
				State <= next_state;
		end		
		
		always_comb begin
			ready=1;
			nMEMW=1;
			nCS=1;
			nIOW=1;
			nIOR=1;
			nMEMR=1;
			if(!RD) begin
				unique case (1'b1)
					state[iT1]: begin
						//ALE=1;
						ADDR = AddressReg;
						next_state=T2;
					end
					state[iT2]: begin
						//ALE = 0;
						nMEMR=0;
						next_state=T3;
					end
					state[iT3]: begin
						//DEN=1 ??
						DataBus = Data;
						next_state = T4;
					end	
					state[iT4]: begin
						nMEMR=1;							
						next_state = T1;
					end
				endcase
			end
			else begin
				unique case (1'b1)
					state[iT1]: begin
						//ALE=1;
						ADDR = AddressReg;
						next_state=T2;
					end
					state[iT2]: begin
						//ALE = 0;
						nIOR=0;
						DATA = Data;
						next_state=T3;
					end
					state[iT3]: begin
						DataBus = Data;
						next_state = T4;
					end	
					state[iT4]: begin
						nIOR=1;
						next_state = T1;
					end
				endcase
				nCS = ~(DMAaddress==AddressReg);
			end
		end
	endtask
endinterface