//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Vemuri Kousalya Gayatri
// Module Name: PriorityEncoder, testbench.
// Project Name: DMA Controller
//////////////////////////////////////////////////////////////////////////////////
`define DEBUG
`define TEST


/*************************************************************************************
* ValidDreq = DREQ from the I/O devices.
* RotatingPriority is bit [4] from Command register[7:0].
  0 - Fixed Priority, 1 - Rotating Priority.
* Mask tells us which all channel request should be ignored.
* SenseDreq is bit [6] from Command register tells us when we need to sense ipDREQ.
  0 - Dreq sense active high, 1 - Dreq sense active low.
* SenseDack is bit [7] from Command register tells us how we need to output the Dack.
  0 - Dack sense active low, 1 - Dack sense active high.
* PendingReq is 4 bit which will indicate which all channels have requested and are
  still not yet completed DMA transfer. (Indirectly Dreq is outputed).
*************************************************************************************/

module PriorityEncoder(
	SystemBusIF.DMA sif,
	ControlIF.PE cif,
	input logic RotatingPriority, SenseDreq, SenseDack, DMA_Disable,
    input logic [3:0] Mask,

    output logic [3:0] PendingReq
    );

    logic [1:0] leastPriority;
    logic [3:0] ValidDreq, tempDack;

    typedef enum logic [1:0] {ARBITER, WAITING, ACKNOWLEDGE} STATE;

    STATE PresentState, NextState;


    /* ValidDreq is an internal wire whose value is calculated.

    First to Sense our Dreq signal, we do XOR with SenseDreq,
    then the output is processed to get the channels which are
    not masked by doing an AND operation with complement of Mask. */

    assign ValidDreq = (sif.Dreq ^ {4{SenseDreq}}) & ~Mask;
    assign sif.Dack = tempDack ~^ {4{SenseDack}};


    // Sequential Logic.
    always_ff @(posedge sif.Clock)
    begin
        validControlSignals_a : assert (!$isunknown({sif.Reset,RotatingPriority,sif.Hlda,SenseDreq,SenseDack,DMA_Disable,Mask}));
        validDreq : assert (!$isunknown(ValidDreq));

        if(sif.Reset)
            begin
            PresentState <= ARBITER;
            leastPriority <= 2'b11;
            cif.ReqID <= '0;
            PendingReq <= '0;
            end
        else
            begin
            PresentState <= NextState;
            PendingReq <= ValidDreq;

            if(PresentState == WAITING && sif.Hlda && RotatingPriority)
                leastPriority <= cif.ReqID;

            if((PresentState == ARBITER) && (|(ValidDreq) & ~sif.Hlda & ~DMA_Disable))
                begin
                // Rotating priority
                if(RotatingPriority)
                    begin
                    unique case(leastPriority)
                    2'b00 : begin
                            if(ValidDreq[1])         cif.ReqID <= 2'b01;
                            else if(ValidDreq[2])    cif.ReqID <= 2'b10;
                            else if(ValidDreq[3])    cif.ReqID <= 2'b11;
                            else if(ValidDreq[0])    cif.ReqID <= 2'b00;
                            end
                    2'b01 : begin
                            if(ValidDreq[2])         cif.ReqID <= 2'b10;
                            else if(ValidDreq[3])    cif.ReqID <= 2'b11;
                            else if(ValidDreq[0])    cif.ReqID <= 2'b00;
                            else if(ValidDreq[1])    cif.ReqID <= 2'b01;
                            end
                    2'b10 : begin
                            if(ValidDreq[3])         cif.ReqID <= 2'b11;
                            else if(ValidDreq[0])    cif.ReqID <= 2'b00;
                            else if(ValidDreq[1])    cif.ReqID <= 2'b01;
                            else if(ValidDreq[2])    cif.ReqID <= 2'b10;
                            end
                    2'b11 : begin
                            if(ValidDreq[0])         cif.ReqID <= 2'b00;
                            else if(ValidDreq[1])    cif.ReqID <= 2'b01;
                            else if(ValidDreq[2])    cif.ReqID <= 2'b10;
                            else if(ValidDreq[3])    cif.ReqID <= 2'b11;
                            end
                    endcase
                    end
                // Fixed Priority.
                else
                    begin
                    if(ValidDreq[0])         cif.ReqID <= 2'b00;
                    else if(ValidDreq[1])    cif.ReqID <= 2'b01;
                    else if(ValidDreq[2])    cif.ReqID <= 2'b10;
                    else if(ValidDreq[3])    cif.ReqID <= 2'b11;
                    end
                end
            end

    end


    // NextState logic.
    always_comb
    begin
        NextState = PresentState;

        unique case(PresentState)
            ARBITER :   if(|(ValidDreq) & ~sif.Hlda & ~DMA_Disable & ~sif.Reset) NextState = WAITING;
            WAITING :   if(sif.Hlda)            NextState = ACKNOWLEDGE;
            ACKNOWLEDGE:if(~sif.Hlda)           NextState = ARBITER;
            default : NextState = PresentState;
        endcase
    end


    // Output logic.
    always_comb
    begin
        {tempDack, cif.ValidReqID} = '0;

        unique case(PresentState)
            ARBITER :   if(|(ValidDreq) & ~sif.Hlda & ~DMA_Disable & ~sif.Reset) cif.ValidReqID = 1'b1;
            WAITING :   begin
                        cif.ValidReqID = 1'b1;

                        if(sif.Hlda)
                            begin
                            unique case(cif.ReqID)
                                2'b00 : tempDack = 4'b0001;
                                2'b01 : tempDack = 4'b0010;
                                2'b10 : tempDack = 4'b0100;
                                2'b11 : tempDack = 4'b1000;
                            endcase
                            end
                        end

            ACKNOWLEDGE:begin
                        if(sif.Hlda)
                            begin
                            cif.ValidReqID = 1'b1;

                            unique case(cif.ReqID)
                                2'b00 : tempDack = 4'b0001;
                                2'b01 : tempDack = 4'b0010;
                                2'b10 : tempDack = 4'b0100;
                                2'b11 : tempDack = 4'b1000;
                            endcase
                            end
                        end
            default : {tempDack, cif.ValidReqID} = '0;
        endcase

    `ifdef DEBUG
        $monitor("Time=%t, Channel=%d, ValidReqID=%b, Hlda=%b, Dreq=%b, Dack=%b PendingReq=%b ", $time,cif.ReqID,cif.ValidReqID,sif.Hlda,ValidDreq,Dack,PendingReq);
    `endif

    end

endmodule



`ifdef TEST
module testbench();

    logic Clock, Reset, RotatingPriority, SenseDreq, SenseDack, DMA_Disable;
    logic [3:0] Mask;
    wire [3:0] PendingReq;

    SystemBusIF sif(Clock, Reset);
ControlIF cif();

    parameter TRUE = 1'b1;
    parameter FALSE = 1'b0;
    parameter CLOCK_CYCLE = 40;
    parameter CLOCK_WIDTH = CLOCK_CYCLE/2;
    parameter IDLE_CLOCKS = 2;
    parameter MAXTIME = 10;
    parameter MINTIME = 1;
    parameter CHECK = 4'b0001;


    PriorityEncoder DUT(sif.DMA, cif, RotatingPriority, SenseDreq, SenseDack, DMA_Disable, Mask, PendingReq);


    // Create running clock.
    initial
    begin
    Clock = FALSE;
    forever #CLOCK_WIDTH Clock = ~Clock;
    end

    // Generate Reset signal
    initial
    begin
    Reset = TRUE;
    repeat (IDLE_CLOCKS) @(negedge Clock);
    Reset = FALSE;
    end


    // Generate stimulus after waiting for reset.
    initial
    begin

    // As Reset is high for two clock cycles there won't be any ValidReqID asserted
    // For the third cycle DMA_Disable is high which will result in Encoder be in ARBITER state.
    sif.Dreq = 4'b1000; Mask = 4'b0000;
    SenseDack = 1;  SenseDreq = 0; sif.Hlda = 0; RotatingPriority = 0; DMA_Disable = 1;

    repeat (IDLE_CLOCKS + 1) @(negedge Clock);
    // Request on channel 3 & 1, Channel 0 is masked and rotating priority.
    // Grant should be given to channel 1, then leastPriority=1;
    sif.Dreq = 4'b1010; Mask = 4'b0001;
    SenseDack = 1;  SenseDreq = 0; sif.Hlda = 0; RotatingPriority = 1; DMA_Disable = 0;

    // Dma has control of the BUS, Dack = 0010. Request on channel 3 & 0.
    repeat (4) @(negedge Clock)   sif.Hlda = 1; sif.Dreq = 4'b1001;

    // Dma transfer is complete.
    // As channel 0 is masked the request will be ignored.
    repeat (5) @(negedge Clock)   sif.Hlda = 0;

    // Dma has control of the BUS.Request granted to channel 3.
    // Dack = 1000, then leastPriority=3;
    repeat (2) @(negedge Clock)  sif.Hlda = 1;

    // Dma transfer is complete. Request on channel 2 & 0.
    // As channel 0 is masked the request will be ignored.
    repeat (2) @(negedge Clock)  sif.Hlda = 0; sif.Dreq = 4'b0101;

    // Request on channel 3.
    @(negedge Clock) sif.Dreq = 4'b1101;

    // Dma has control of the BUS.Request granted to channel 2.
    // Dack = 0100, then leastPriority=2;
    repeat (4) @(negedge Clock)   sif.Hlda = 1;

    // Dma transfer is complete. Request one channel 3.
    repeat (5) @(negedge Clock)   sif.Hlda = 0;

    // Waiting for Hlda from the processor.
    repeat (2) @(negedge Clock);

    $finish;
    end


/******************Assertions to check Priority Encoder*****************/

    /* Dack should be correct W.R.T ReqID, throughtout the
    time when ValidReqID and Hlda is asserted.*/
    property ValidDack_p;
    @(posedge Clock) disable iff(Reset)
        (cif.ValidReqID & sif.Hlda) |-> sif.Dack === (CHECK << cif.ReqID);
    endproperty
    ValidDack_a : assert property (ValidDack_p);

    // Function to check Fixed Priority based on the input Dreq.
    function int FixedPriorityID(input bit [3:0] refDreq, refMask, input bit Sense);
        logic [3:0] dreq;
        dreq = (refDreq ^ {4{Sense}}) & ~refMask;
        unique case(dreq)
        4'b???1 : return 2'b00;
        4'b??10 : return 2'b01;
        4'b?100 : return 2'b10;
        4'b1000 : return 2'b11;
        default : return 2'b00;
        endcase
    endfunction

    /* When ValidReqID is asserted and RoatatingPriority is low,
    ReqID should be correct based on Dreq.*/
    property FixedPriorityReqID_p;
        @(posedge Clock) disable iff(Reset || RotatingPriority)
            $rose(cif.ValidReqID) |->  cif.ReqID === FixedPriorityID(sif.Dreq, Mask, SenseDreq);
    endproperty
    FixedPriorityReqID_a : assert property (FixedPriorityReqID_p);

    /* We should never see a Dack for masked channel.Consequent
    should be non zero, if zero then masked channel has a Dack.*/
    property NoDackForMaskedChannel_p;
        @(posedge Clock) disable iff(Reset)
            (cif.ValidReqID & sif.Hlda) |->  |(sif.Dack & ~Mask);
    endproperty
    NoDackForMaskedChannel_a : assert property (NoDackForMaskedChannel_p);

endmodule
`endif
