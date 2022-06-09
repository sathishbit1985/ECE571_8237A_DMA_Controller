module BusFuncModel(SystemBusIF.BFM8086 BFMBus, inout logic[15:0] AD15_AD0, output logic ALE );
	
	logic M_nIO,Read,BUSWRITE,BUSREAD;
	logic [15:0] AddrReg;
	logic [7:0] DataReg;
	logic en_Data;
	
	
	logic nMEMR, nMEMW, nIOR, nIOW;
	
	//W_Tx -> IO write cycle, R_Tx -> IO read cycle
	enum {
		iIDLE = 0,
		iW_T1 = 1,
		iW_T2 = 2,
		iW_T3 = 3,
		iW_T4 = 4,
		iR_T1 = 5,
		iR_T2 = 6,
		iR_T3 = 7,
		iR_T4 = 8,
		iWAIT_FOR_DMA = 9
		}stateposition;
	
	enum logic [9:0] {
		IDLE = 10'b0000000001 << iIDLE,
		W_T1 = 10'b0000000001 << iW_T1,
		W_T2 = 10'b0000000001 << iW_T2,
		W_T3 = 10'b0000000001 << iW_T3,
		W_T4 = 10'b0000000001 << iW_T4,
		R_T1 = 10'b0000000001 << iR_T1,
		R_T2 = 10'b0000000001 << iR_T2,
		R_T3 = 10'b0000000001 << iR_T3,
		R_T4 = 10'b0000000001 << iR_T4,
		WAIT_FOR_DMA = 10'b0000000001 << iWAIT_FOR_DMA
		}state, next_state;
	
	logic en_AddrDataBuf = 0;
	assign AD15_AD0 = en_AddrDataBuf ? AddrReg : 'z;
	
	always_latch
	begin
  	if(en_Data) DataReg <= AD15_AD0[15:8];
	end

	//read & write control signals
	assign BFMBus.nMEMW = ~BFMBus.Hlda ? nMEMW : 'z;
	assign BFMBus.nMEMR = ~BFMBus.Hlda ? nMEMR : 'z;
	assign BFMBus.nIOW  = ~BFMBus.Hlda ? nIOW  : 'z;
	assign BFMBus.nIOR  = ~BFMBus.Hlda ? nIOR  : 'z;
	
	always_ff @(posedge BFMBus.Clock) begin
		if(BFMBus.Reset)
			state <= IDLE;
		else
			state <= next_state;
	end
	
	always_comb begin
		{nMEMW, nMEMR, nIOW, nIOR} = '1;
		BFMBus.Hlda = '0;
		ALE = '0;
		en_Data = '0;
		unique case(1'b1)
			state[iIDLE]: begin
				if(BFMBus.Hrq) begin
					next_state = WAIT_FOR_DMA;
				end
				else if(BUSWRITE) begin
					next_state = W_T1;	
				end
				else if(BUSREAD) begin
					next_state = R_T1;
				end
				else next_state = IDLE;
			end
			state[iW_T1]: begin 
				ALE = 1'b1;
				next_state = W_T2;
			end
			state[iW_T2]: begin
				next_state = W_T3;
			end
			state[iW_T3]: begin
				nIOW = 1'b0;	
				next_state   = W_T4;
			end
			state[iW_T4]: begin	
				next_state   = IDLE;
			end
			state[iR_T1]: begin
				ALE = 1'b1;		
				next_state=R_T2;
			end
			state[iR_T2]: begin		
				next_state=R_T3;
			end
			state[iR_T3]: begin
				nIOR = 1'b0;
				en_Data = '1;
				next_state=R_T4;
			end
			state[iR_T4]: begin
				next_state=IDLE;
			end
			state[iWAIT_FOR_DMA]: begin
				if(BFMBus.Hrq) begin	
					BFMBus.Hlda = 1'b1;
					next_state = WAIT_FOR_DMA;
				end
				else begin	
					BFMBus.Hlda = '0;
					next_state=IDLE;
				end
			end
		endcase
	end
	
	task WriteBUS(input logic [15:0]AddressValue, input logic Memory_nIO);
		BUSWRITE <= 1'b1;
		AddrReg[15:0] <= AddressValue[15:0];
		M_nIO <= Memory_nIO;
		en_AddrDataBuf <= 1'b1;
		@(posedge BFMBus.Clock) BUSWRITE <= 1'b0;
		@ (posedge BFMBus.Clock);
		wait(state == IDLE);
		en_AddrDataBuf <= 1'b0;
		repeat (2) @(posedge BFMBus.Clock);		
	endtask
	
	task ReadBUS(input logic [7:0]AddressValue, input logic Memory_nIO, output logic [7:0] DataRead);
		BUSREAD <= 1;
		AddrReg[15:0] <= AddressValue[7:0];
		Read <= Memory_nIO;
		en_AddrDataBuf <= 1'b1;
		@(posedge BFMBus.Clock) BUSREAD <= 1'b0;
		@(posedge BFMBus.Clock) en_AddrDataBuf <= 1'b0;
		@(posedge BFMBus.Clock);
		wait(state == IDLE);
		DataRead <= DataReg;
		repeat (2) @(posedge BFMBus.Clock);
	endtask
endmodule