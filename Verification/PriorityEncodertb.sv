
`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Name: Kaavya Thrilochan
// Module Name: Priority Encoder (Arbiter)
// ECE571 Final Project Spring 2022
// DMA Controller - Verification Team
//////////////////////////////////////////////////////////////////////
module PriorityEncoder_tb();
SystemBusIF.DMA sif;
ControlIF.PE cif;
logic  tbRotatingPriority, tbSenseDreq, tbSenseDack, Dma_Disable;
logic [3:0] tbMask;

logic [3:0] PendingReq;

/*************************************************************************************
* sif.Dreq = DREQ driving from test bench to DUT.
* tbRotatingPriority is driven high or low from testbench to DUT.
  0 - Fixed Priority, 1 - Rotating Priority.
* tbMask is used to mask the channel from testbench to the DUT input signal Mask.
* tbSenseDreq is driven high or low from testbench to DUT to check Dreq being sensed accordingly.
  0 - Dreq sense active high, 1 - Dreq sense active low.
* tbSenseDack is driven high or low from testbench to DUT to check Dack being sensed accordingly.
  0 - Dack sense active low, 1 - Dack sense active high.
* reqId, ExpDack, PendingReq and ValidRe is 4 bit which will indicate which all channels have requested and are
  still not yet completed DMA transfer. (Indirectly Dreq is outputed).
*************************************************************************************/

parameter TRUE = 1'b1;
parameter FALSE = 1'b0;
parameter CLOCK_CYCLE = 40;
parameter CLOCK_WIDTH = CLOCK_CYCLE/2;
parameter IDLE_CLOCKS = 2;
parameter FIXEDPRIORITY = 0;
parameter ROTATINGPRIORITY = 1;
parameter MAXARBITRATIONTIME = 10;

//intermediate variables
logic [3:0] Dreq, Dack;
int error = 0;

//sense check
assign Dreq = ((!tbSenseDreq) ? sif.Dreq : ~sif.Dreq) & ~tbMask;
assign Dack = (tbSenseDack) ? sif.Dack : ~sif.Dack;

PriorityEncoder DUT(sif, cif, tbRotatingPriority, tbSenseDreq, tbSenseDack, 
                        Dma_Disable, tbMask, PendingReq);
						
	
//create running clock.
initial
begin
sif.Clock = FALSE;
forever #CLOCK_WIDTH sif.Clock = ~sif.Clock;
end


//  Generate Reset signal
task Release_Reset();
	sif.Reset = TRUE;
	repeat (IDLE_CLOCKS) @(negedge sif.Clock);
	sif.Reset = FALSE;
endtask

task Directed_Traffic();

	repeat (IDLE_CLOCKS + 2) @(negedge sif.Clock);
				sif.Hlda = 1'b0; tbRotatingPriority = 1'b0; tbSenseDreq = 1'b0; tbSenseDack = 1'b0; tbMask = 4'b0100; sif.Dreq = 4'b1100; //masked one channel
				
	@(negedge sif.Clock);   
				sif.Hlda = 1'b1;
				
	@(negedge sif.Clock);   
				sif.Hlda = 1'b0; tbRotatingPriority = 1'b0; tbSenseDreq = 1'b0; tbSenseDack = 1'b0; tbMask = 4'b0000; sif.Dreq = 4'b1100; //unmasked the masked channel
		
	repeat (3) @(negedge sif.Clock);     
			sif.Hlda = 1'b1;
				
	repeat (2) @(negedge sif.Clock);   
				sif.Hlda = 1'b0; tbRotatingPriority = 1'b0; tbSenseDreq = 1'b0; tbSenseDack = 1'b0; tbMask = 4'b0000; sif.Dreq = 4'b0000; //no Dreq
	
	repeat (3) @(negedge sif.Clock);
				sif.Hlda = 1'b1;
				
	repeat (3) @(negedge sif.Clock);
				sif.Hlda = 1'b0; tbRotatingPriority = 1'b0; tbSenseDreq = 1'b0; tbSenseDack = 1'b1; tbMask = 4'b0000; sif.Dreq = 4'b0100; //sense Dack on High
		
	repeat (3) @(negedge sif.Clock);
				sif.Hlda = 1'b1;		
				
	repeat (5) @(negedge sif.Clock);
	
endtask

task Random_Traffic();
	repeat (IDLE_CLOCKS) @(negedge sif.Clock);
	sif.Hlda = 1'b0; tbRotatingPriority = 1'b0; tbSenseDreq = 1'b0; tbSenseDack = 1'b0; 
		
	repeat(5)begin //AR: increase iterations
	    repeat (IDLE_CLOCKS) @(negedge sif.Clock);
		tbMask = $urandom_range('d0, 'd15); sif.Dreq = $urandom_range('d0, 'd15); 
		repeat (IDLE_CLOCKS) @(negedge sif.Clock); 
	end
endtask

// -------------------------------------------------
// --------------- stimulus to DUT -----------------
// -------------------------------------------------
initial
begin
	Release_Reset();
	Directed_Traffic();	
	Random_Traffic();
	$finish;
end

// -----------Function to check Rotating Priority based on the input Dreq being asserted-----------------
function int RotatingPriority(input logic [3:0] refDreq); // 0011
static logic [1:0] leastpriority = 2'b11;
logic [1:0] funcReqId;
		unique case(leastpriority)
		 2'b00: begin
				unique case(refDreq)
				4'b??1? : funcReqId = 2'b01;
				4'b?10? : funcReqId = 2'b10;
				4'b100? : funcReqId = 2'b11;
				4'b0001 : funcReqId = 2'b00;
				endcase
				end
		 2'b01: begin
				unique case(refDreq)
				4'b?1?? : funcReqId = 2'b10;
				4'b10?? : funcReqId = 2'b11;
				4'b00?1 : funcReqId = 2'b00;
				4'b0010 : funcReqId = 2'b01;
				endcase
				end
		 2'b10: begin
				unique case(refDreq)
				4'b1??? : funcReqId = 2'b11;
				4'b0??1 : funcReqId = 2'b00;
				4'b0?10 : funcReqId = 2'b01;
				4'b0100 : funcReqId = 2'b10;
				endcase
				end
		 2'b11: begin
				unique case(refDreq)
				4'b???1 : funcReqId = 2'b00;
				4'b??10 : funcReqId = 2'b01;
				4'b?100 : funcReqId = 2'b10;
				4'b1000 : funcReqId = 2'b11;
				endcase
				end
 endcase
			return funcReqId;
endfunction
	
	
//---------------------------------------------
//--------------- Assertions ------------------
//---------------------------------------------

/* Never see a Dack for masked channel*/
property NoDackForMaskedChannel_p;
        @(posedge sif.Clock) disable iff(sif.Reset)
            (cif.ValidReqID & sif.Hlda) |=>  |(sif.Dack & ~tbMask);
endproperty
	NoDackForMaskedChannel_a : assert property (NoDackForMaskedChannel_p);


/*Atmost one Dack signal is asserted at a time */
property AtmostoneDack_p;
@(posedge sif.Clock) disable iff (sif.Reset || Dma_Disable)
	(!Dreq && sif.Hlda) throughout $onehot0(Dack);
endproperty
	AtmostoneDack_a: assert property (AtmostoneDack_p);


/* ValidDreq should be low when Dreq is not asserted or when Reset is High */
property ValidDreq_p;
@(posedge sif.Clock)
	(!Dreq || sif.Reset || ~sif.Hlda) throughout (!cif.ValidReqID);
endproperty
	ValidDreq_a: assert property (ValidDreq_p);


/* ValidDreq and Hlda should go high following Dreq being asserted and Hlda being low */
property ValidDreq_p1;
@(posedge sif.Clock)
	disable iff (Dma_Disable || sif.Reset)
	(Dreq && ~sif.Hlda) |-> ##[0:MAXARBITRATIONTIME] (cif.ValidReqID && sif.Hlda);
endproperty
	ValidDreq_a1: assert property (ValidDreq_p1);


/* ReqID_Dut is stable throughout tbHlda high */
property ReqIDStable_p;
@(posedge sif.Clock)
	sif.Hlda throughout $stable(cif.ReqID);
endproperty
	ReqIDStable_a: assert property (ReqIDStable_p);

/* Dack for Fixed Priority */
property DackFixed_p(id);
@(posedge sif.Clock)
	(sif.Dreq[id] && ~tbMask[id] && sif.Hlda && ~tbRotatingPriority) |-> Dack[id];
endproperty
	DackFixed_a0: assert property (@(posedge sif.Clock)DackFixed_p(0));
	DackFixed_a1: assert property (@(posedge sif.Clock)DackFixed_p(1));
	DackFixed_a2: assert property (@(posedge sif.Clock)DackFixed_p(2));
	DackFixed_a3: assert property (@(posedge sif.Clock)DackFixed_p(3));


/* Dack for Rotating Priority */	
always @(Dreq)begin // 0110
    if(Dack[RotatingPriority(Dreq)] == 'b1)begin
     $display("-----PASS-----");
    end else begin
       $display("-----FAIL-----");
    end
end
endmodule
