//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Vemuri Kousalya Gayatri
// Module Name: PriorityEncoder, testbench.
// Project Name: DMA Controller 
//////////////////////////////////////////////////////////////////////////////////
`define DEBUG
`define TEST


/*************************************************************************************
* ipDreq = DREQ from the I/O devices.
* RotatingPriority is bit [4] from Command register[7:0].
  0 - Fixed Priority, 1 - Rotating Priority.
* Mask tells us which all channel request should be ignored. 
* SenseDreq is bit [6] from Command register tells us when we need to sense ipDREQ.
  0 - Dreq sense active high, 1 - Dreq sense active low.
* SenseDack is bit [7] from Command register tells us how we need to output the Dack.
  0 - Dack sense active low, 1 - Dack sense active high.
*************************************************************************************/

module PriorityEncoder(
    input logic Clock, Reset,
    input logic [3:0] ipDreq,
    input logic Hlda, RotatingPriority,
    input logic SenseDreq, SenseDack,
    input logic [3:0] Mask,
    
    output logic [3:0] Dack,
    output logic [1:0] ReqID,
    output logic ValidReqID
    );
    
    logic [1:0] leastPriority;
    logic [3:0] Dreq, tempDack;
    
    typedef enum logic [1:0] {ARBITER, WAITING, ACKNOWLEDGE} STATE;
    
    STATE PresentState, NextState;
    
    
    /* Dreq is an internal wire whose value is calculated 
    to get the valid Dreq which we need to process.
    
    First to Sense our Dreq signal we do XOR with SenseDreq,
    then the output is processed to get the channels which are
    not masked by doing an AND operation with complement of Mask. */
    assign Dreq = (ipDreq ^ {4{SenseDreq}}) & ~Mask;
    assign Dack = tempDack ~^ {4{SenseDack}};
    
    
    
    // Sequential Logic.
    always_ff @(posedge Clock)
    begin
        if(Reset)
            begin
            PresentState <= ARBITER;
            leastPriority <= 2'b11;
            ReqID <= '0;
            end
        else
            begin
            PresentState <= NextState;
        
            if(PresentState == WAITING && Hlda && RotatingPriority)
                leastPriority <= ReqID;
        
            if((PresentState == ARBITER) && (|(Dreq) & ~Hlda))
                begin
                // Rotating priority
                if(RotatingPriority)
                    begin
                    unique case(leastPriority)
                    2'b00 : begin
                            if(Dreq[1])         ReqID <= 2'b01;
                            else if(Dreq[2])    ReqID <= 2'b10;
                            else if(Dreq[3])    ReqID <= 2'b11;
                            else if(Dreq[0])    ReqID <= 2'b00;
                            end
                    2'b01 : begin
                            if(Dreq[2])         ReqID <= 2'b10;
                            else if(Dreq[3])    ReqID <= 2'b11;
                            else if(Dreq[0])    ReqID <= 2'b00;
                            else if(Dreq[1])    ReqID <= 2'b01;
                            end
                    2'b10 : begin
                            if(Dreq[3])         ReqID <= 2'b11;
                            else if(Dreq[0])    ReqID <= 2'b00;
                            else if(Dreq[1])    ReqID <= 2'b01;
                            else if(Dreq[2])    ReqID <= 2'b10;
                            end
                    2'b11 : begin
                            if(Dreq[0])         ReqID <= 2'b00;
                            else if(Dreq[1])    ReqID <= 2'b01;
                            else if(Dreq[2])    ReqID <= 2'b10;
                            else if(Dreq[3])    ReqID <= 2'b11;
                            end
                    endcase
                    end
                // Fixed Priority.
                else
                    begin
                    if(Dreq[0])         ReqID <= 2'b00;
                    else if(Dreq[1])    ReqID <= 2'b01;
                    else if(Dreq[2])    ReqID <= 2'b10;
                    else if(Dreq[3])    ReqID <= 2'b11;
                    end
                end
            end
                    
    end
    
    
    // NextState logic.
    always_comb    
    begin
        NextState = PresentState;
        
        unique case(PresentState)
            ARBITER :   if(|(Dreq) & ~Hlda) NextState = WAITING;
            WAITING :   if(Hlda)            NextState = ACKNOWLEDGE;
            ACKNOWLEDGE:if(~Hlda)           NextState = ARBITER;
        endcase
    end
    
    
    // Output logic.
    always_comb
    begin
        {tempDack, ValidReqID} = '0; 
        
        unique case(PresentState)
            ARBITER :   if(|(Dreq) & ~Hlda) ValidReqID = 1'b1;
            WAITING :   begin
                        ValidReqID = 1'b1;
                        
                        if(Hlda)
                            begin
                            unique case(ReqID)
                                2'b00 : tempDack = 4'b0001;
                                2'b01 : tempDack = 4'b0010;
                                2'b10 : tempDack = 4'b0100;
                                2'b11 : tempDack = 4'b1000;
                            endcase
                            end
                        end
            
            ACKNOWLEDGE:begin
                        if(Hlda)
                            begin
                            ValidReqID = 1'b1;
                            
                            unique case(ReqID)
                                2'b00 : tempDack = 4'b0001;
                                2'b01 : tempDack = 4'b0010;
                                2'b10 : tempDack = 4'b0100;
                                2'b11 : tempDack = 4'b1000;
                            endcase
                            end
                        end
        endcase
        
        `ifdef DEBUG
            $display("Time=%t, Channel=%d, ValidReqID=%b, Hlda=%b, Dreq=%b, Dack=%b", $time,ReqID,ValidReqID,Hlda,Dreq,Dack);
        `endif
    end

endmodule



`ifdef TEST
module testbench();
    reg Clock, Reset, Hlda, RotatingPriority, SenseDreq, SenseDack;
    reg [3:0] Dreq, Mask;
    wire [1:0] ReqID;
    wire [3:0] Dack;
    wire ValidReqID;
    
    parameter TRUE = 1'b1;
    parameter FALSE = 1'b0;
    parameter CLOCK_CYCLE = 40;
    parameter CLOCK_WIDTH = CLOCK_CYCLE/2;
    parameter IDLE_CLOCKS = 2;
    
    PriorityEncoder DUT(Clock, Reset, Dreq, Hlda, RotatingPriority, SenseDreq, SenseDack, Mask,
        Dack, ReqID, ValidReqID);
    
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
    repeat (IDLE_CLOCKS + 1) @(negedge Clock);
      // Request on channel 3 & 1, Channel 0 is masked and rotating priority.
      // Grant should be given to channel 1, then leastPriority=1;
      Dreq = 4'b1010; Mask = 4'b0001;
      SenseDack = 1;  SenseDreq = 0; Hlda = 0; RotatingPriority = 1;
      
    // Dma has control of the BUS. Dack = 0010
    @(negedge Clock);   Hlda = 1;
     
    // Dma transfer is complete. Request on channel 3 & 0.
    // As channel 0 is masked the request will be ignored. 
    @(negedge Clock);   Hlda = 0; Dreq = 4'b1001;
    
    // Dma has control of the BUS.Request granted to channel 3.
    // Dack = 1000, then leastPriority=3;
    repeat (2) @(negedge Clock);  Hlda = 1;
    
    // Dma transfer is complete. Request on channel 2 & 0.
    // As channel 0 is masked the request will be ignored. 
    repeat (2) @(negedge Clock);  Hlda = 0; Dreq = 4'b0101;
    
    // Request on channel 3.
    @(negedge Clock); Dreq = 4'b1101;
    
    // Dma has control of the BUS.Request granted to channel 2.
    // Dack = 0100, then leastPriority=2;
    repeat (4) @(negedge Clock);   Hlda = 1;
    
    // Dma transfer is complete. Request one channel 3.
    repeat (5) @(negedge Clock);   Hlda = 0;
    
    // Waiting for Hlda from the processor.
    repeat (2) @(negedge Clock);
    
    $finish;
    end
    
endmodule
`endif