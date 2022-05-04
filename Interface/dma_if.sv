interface dma_if(input logic CLK, input logic RESET);

	logic [3:0] ADDR_U;		 // upper(A7-A4) address bits
	logic [3:0] ADDR_L;		// lower(A3-A0) address bits
	logic [7:0] DB;			        // data bus
	logic       n_CS; 		               // chip select
	logic       AEN;		               // address enable
	logic       ADSTB;		       // address strobe

	logic 	    n_MEMR;   	      // memory read
	logic 	    n_MEMW;	      // memory write
	logic 	    n_IOR;		      // IO read
	logic 	    n_IOW;		     // IO write
	logic 	    HLDA;		     // hold acknowledge from CPU, indicating that it has relinquished control of the bus
	logic 	    HRQ;		            // hold request to the CPU from DMA for bus control

	logic [3:0] DREQ;		   // asynchronous channel request lines by peripheral to obtain DMA service
	logic [3:0] DACK;		  // acknowledge lines to notify the peripheral of granted DMA cycle

	logic 	    n_EOP;		// End of Process
	logic       PIN5;                    // don't know whether we need this
	logic       READY;               // extend memory read and write pulses from 8237A for slow memories or IO peripheral

endinterface
