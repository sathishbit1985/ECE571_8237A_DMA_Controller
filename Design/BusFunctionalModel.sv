//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Ramesh Chandar Aniruddh Punnai
// Module Name: BusFuncModel
// Project Name: DMA Controller
//////////////////////////////////////////////////////////////////////////////////

module BusFuncModel(SystemBusIF.BFM8086 BFMBus, inout logic[15:0] AD15_AD0, output logic ALE );
	
	logic M_nIO,Read,BUSWRITE,BUSREAD;
	logic [15:0] AddrReg, DataOut;
	logic [7:0] DataIn;
	logic ld_Data;
	logic AddrDataMuxSel;
	
	
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
	
	logic en_OutBuf;
	assign AD15_AD0 = en_OutBuf ? (AddrDataMuxSel ? AddrReg : DataOut) : 'z;
	
	always_ff @(posedge BFMBus.Clock )
	begin
  	  if(ld_Data) DataIn <= AD15_AD0[15:8];
	  else DataIn <= DataIn;
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
		BFMBus.Hlda = 1'b0;
		ALE = 1'b0;
		ld_Data = 1'b0;
		AddrDataMuxSel = 1'b0;
		en_OutBuf = 1'b0;
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
				a_checkUnknownSignals: assert(!$isunknown({BFMBus.Hrq}));
			end
			state[iW_T1]: begin 
				ALE = 1'b1;
				AddrDataMuxSel = 1'b1;
				en_OutBuf = 1'b1;
				next_state = W_T2;
			end
			state[iW_T2]: begin
				en_OutBuf = 1'b1;
				next_state = W_T3;
			end
			state[iW_T3]: begin
				en_OutBuf = 1'b1;
				nIOW = 1'b0;	
				next_state   = W_T4;
			end
			state[iW_T4]: begin
				en_OutBuf = 1'b1;
				next_state   = IDLE;
			end
			state[iR_T1]: begin
				ALE = 1'b1;
				AddrDataMuxSel = 1'b1;
				en_OutBuf = 1'b1;
				next_state=R_T2;
			end
			state[iR_T2]: begin		
				next_state=R_T3;
			end
			state[iR_T3]: begin
				nIOR = 1'b0;
				ld_Data = 1'b1;
				next_state=R_T4;
			end
			state[iR_T4]: begin
				ld_Data = 1'b1;
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
			default: next_state = state;
		endcase
	end
	
	task WriteBUS(input logic [15:0]AddressValue, input[15:0] DataValue, input logic Memory_nIO);
		BUSWRITE <= 1'b1;
		AddrReg <= AddressValue;
		DataOut <= DataValue;
		M_nIO <= Memory_nIO;
		@(posedge BFMBus.Clock) BUSWRITE <= 1'b0;
		@ (posedge BFMBus.Clock);
		wait(state == IDLE);
		repeat (2) @(posedge BFMBus.Clock);		
	endtask
	
	task ReadBUS(input logic [15:0]AddressValue, input logic Memory_nIO, output logic [7:0] DataRead);
		BUSREAD <= 1;
		AddrReg <= AddressValue;
		Read <= Memory_nIO;
		@(posedge BFMBus.Clock) BUSREAD <= 1'b0;
		@(posedge BFMBus.Clock);
		wait(state == R_T4);
		DataRead <= DataIn;
		repeat (2) @(posedge BFMBus.Clock);
	endtask
	
	//assertions

    //assertion to verify that the next state is either of IDLE, W_T1, R_T1 or WAIT_FOR_DMA state when current state is in IDLE on the posedge of the clock
	property  p_IdleState;
		@(posedge BFMBus.Clock) 
		!BFMBus.Reset && (state==IDLE)|=> ((state==WAIT_FOR_DMA)||(state==W_T1)||(state==R_T1)||(state==IDLE));
	endproperty
	a_IdleState: assert property(p_IdleState);
	/*begin
		$display("Assertion a_IdleState passed!");
	end*/

	//assertion to verify that the next state is WAIT_FOR_DMA state when current state is in IDLE and Hold request signal is asserted on the posedge of the clock
	property p_IdleToDMA;
		@(posedge BFMBus.Clock) 
		!BFMBus.Reset && BFMBus.Hrq && (state==IDLE)|=> (state==WAIT_FOR_DMA);
	endproperty
 	a_checkIdletowaitForDMA: assert property (p_IdleToDMA);
	/*begin
		$display("Assertion a_checkIdletowaitForDMA passed!");
	end*/

	//assertion to verify that the next state is W_T1 state when current state is in IDLE and BUSWRITE signal is asserted on the posedge of the clock
	property  p_IdleToWR1;
		@(posedge BFMBus.Clock) 
		!BFMBus.Reset && BUSWRITE && (state==IDLE)|=> (state==W_T1);
	endproperty
    a_checkIdletoWR1: assert property(p_IdleToWR1);
	/*begin
		$display("Assertion a_checkIdletoWR1 passed!");
	end*/

	//assertion to verify that the next state is R_T1 state when current state is in IDLE and BUSREAD signal is asserted on the posedge of the clock
	property  p_IdleToRD1;
		@(posedge BFMBus.Clock) 
		!BFMBus.Reset && BUSREAD && (state==IDLE)|=> (state==R_T1);
	endproperty
    a_checkIdletoRD1: assert property(p_IdleToRD1);
	/*begin
		$display("Assertion a_checkIdletoRD1 passed!");
	end*/	

	//assertion to verify that the next state remains in IDLE state when current state is in IDLE and neither of hold request, Bus read nor bus write signal is asserted on the posedge of the clock when the system is not in reset mode.
	property  p_Idle;
		@(posedge BFMBus.Clock) 
		!BFMBus.Reset && !BFMBus.Hrq && !BUSREAD && !BUSWRITE && (state==IDLE)|=> (state==IDLE);
	endproperty
    a_checkIdlestate: assert property(p_Idle);
	/*begin
		$display("Assertion a_checkIdlestate passed!");
	end*/	
          
    //assertion to verify that the next state remains in IDLE state when reset is sampled on the posedge of the clock
	property  p_checkReset;
		@(posedge BFMBus.Clock) 
		BFMBus.Reset |=> (state==IDLE);
	endproperty
	a_checkStateAtReset: assert property(p_checkReset);
	/*begin
		$display("Assertion a_checkStateAtReset passed!");
	end*/
endmodule
