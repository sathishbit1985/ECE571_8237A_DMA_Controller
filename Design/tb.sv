module TestBenchTop();

parameter DMAADDRESS = 12'hFFF;

logic Clock =1 , Reset;
logic [7:0] DataRead;

typedef struct packed{
logic [11:0] Address;
logic [3:0]  RegCommandCode;
logic  [7:0]  Data;
logic Read;
} RegisterWR;

typedef struct packed{
logic [3:0] channel; 
logic [7:0] [3:0] Delay;
}Dmatransfer;
logic [3:0]Dmarequest;

Dmatransfer Dma;

import DmaRegisterAddressCode ::* ;

wire nCS, ALE;
wire [15:0] AD15_AD0;

ControlIF DMAcif();
SystemBusIF MainBus(Clock,Reset);
Memory M(MainBus);
IODevices IO (Dmarequest, MainBus);
BusFuncModel Bus (MainBus, AD15_AD0, ALE);
AddressLatch AL (MainBus, AD15_AD0, ALE );
PortDecoder P1 (MainBus, nCS);
DMAControllerTop DMATop(MainBus, nCS , AD15_AD0[15:8]);
SVARegister SVA (MainBus,DMAcif,Clock,Reset);

RegisterWR [31:0] DmaRegisterData = { '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH0_CURRENT_ADDRESS,8'hA5,1'b1},    '{ DMAADDRESS,CH0_CURRENT_ADDRESS,8'hA5,1'b1}, 
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH0_CURRENT_WORD_COUNT,8'h10,1'b1}, '{ DMAADDRESS,CH0_CURRENT_WORD_COUNT,8'h00,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH1_CURRENT_ADDRESS,8'hA5,1'b1},    '{ DMAADDRESS,CH1_CURRENT_ADDRESS,8'hA5,1'b1}, 
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH1_CURRENT_WORD_COUNT,8'h10,1'b1}, '{ DMAADDRESS,CH1_CURRENT_WORD_COUNT,8'h00,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH2_CURRENT_ADDRESS,8'h75,1'b1},    '{ DMAADDRESS,CH2_CURRENT_ADDRESS,8'hEA,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH2_CURRENT_WORD_COUNT,8'hFF,1'b1}, '{ DMAADDRESS,CH2_CURRENT_WORD_COUNT,8'h00,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH3_CURRENT_ADDRESS,8'h75,1'b1},    '{ DMAADDRESS,CH3_CURRENT_ADDRESS,8'hEA,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH3_CURRENT_WORD_COUNT,8'hFF,1'b1}, '{ DMAADDRESS,CH3_CURRENT_WORD_COUNT,8'h00,1'b1},
				                      '{ DMAADDRESS,MASTER_CLEAR,8'h69,1'b0},       '{ DMAADDRESS,COMMAND_REGISTER,8'h80,1'b0},       '{ DMAADDRESS,MODE_REGISTER,8'hA4,1'b0},      
									  '{ DMAADDRESS,MODE_REGISTER,8'hA9,1'b0},      '{ DMAADDRESS,MODE_REGISTER,8'h86,1'b0},          '{ DMAADDRESS,MODE_REGISTER,8'h8B,1'b0},
									  '{ DMAADDRESS,CLEAR_MASK_REGISTER,8'h05,1'b0},'{ DMAADDRESS,WRITE_ALL_MASK_REGISTER,8'h00,1'b0}};

initial
  forever #1 Clock = ~Clock;


initial
begin
	repeat(2) @(negedge Clock) Reset=1;
	@(negedge Clock) Reset=0;

	//Write all DMA Registers,
	foreach( DmaRegisterData[i])
		Bus.WriteBUS( {DmaRegisterData[i].Address ,DmaRegisterData[i].RegCommandCode}, {DmaRegisterData[i].Data, 8'h00 }, 1'b0);
	//Read DMA registers which are readable 
	foreach(DmaRegisterData[i])
    begin
		if( DmaRegisterData[i].RegCommandCode == CLEAR_BPFF)
			Bus.WriteBUS( {DmaRegisterData[i].Address ,DmaRegisterData[i].RegCommandCode}, {DmaRegisterData[i].Data, 8'h00 }, 1'b0);
		else if(DmaRegisterData[i].Read === 1)
		begin	
			Bus.ReadBUS({DmaRegisterData[i].Address ,DmaRegisterData[i].RegCommandCode},1'b0, DataRead);
			if(DmaRegisterData[i].RegCommandCode !==  CLEAR_BPFF)
				repeat(3) @(posedge Clock);
			if(DmaRegisterData[i].Data !== DataRead)
				$display("Data written= %h Data Read = %h", DmaRegisterData[i].Data , DataRead);	
		end
    end
	
	//DMA Transfer for Device 1. Address Decrement, Fixed Priority, IO to Memory
	$display("DMA Transfer for Device 1 started with Fixed Priority, Write Transfer, Address Decrement");
	@(negedge Clock)  Dma.channel = 4'b0001;
    Dma.Delay   = '0;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(!MainBus.nEOP);
	$display("DMA Transfer for Device 1 Done\n");
	repeat(2) @(negedge Clock);
	
	//DMA Transfer for Device 2. Address Decrement, Rotating Priority, Memory to IO
	$display("DMA Transfer for Device 2 started with Rotating Priority, Read Transfer, Address Decrement");
	Bus.WriteBUS({DMAADDRESS, 4'(COMMAND_REGISTER)}, {8'h90, 8'h00},1'b0);
	repeat(8) @(negedge Clock);
	@(negedge Clock)  Dma.channel = 4'b0010;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(MainBus.nEOP == 0);
	$display("DMA Transfer for Device 2 Done\n");
	repeat(2) @(negedge Clock);
	
	//DMA Transfer for Device 3. Address Increment, Fixed Priority, IO to Memory
	$display("DMA Transfer for Device 3 started with Fixed Priority, Write Transfer, Address Increment");
	Bus.WriteBUS({DMAADDRESS, 4'(COMMAND_REGISTER)}, {8'h80, 8'h00},1'b0);
	@(negedge Clock)  Dma.channel = 4'b0100;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(MainBus.nEOP == 0);
	$display("DMA Transfer for Device 3 Done\n");
	repeat(2) @(negedge Clock);
	
	//DMA Transfer for Device 4. Address Increment, Rotating Priority, Memory to IO
	$display("DMA Transfer for Device 4 started with Rotating Priority, Read Transfer, Address Increment");
	Bus.WriteBUS({DMAADDRESS, 4'(COMMAND_REGISTER)}, {8'h90, 8'h00},1'b0);
	@(negedge Clock)  Dma.channel = 4'b1000;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(MainBus.nEOP == 0);
	repeat(2) @(negedge Clock);
	$display("DMA Transfer for Device 4 Done\n");
	$finish; 
end


//Task to generate DMA request for 4 channels in parallel after specific delay
task Dmaaccess(input Dmatransfer Dma);
fork
  begin
    if(Dma.channel[0]== 1)
    begin
      repeat(Dma.Delay[0]) @(negedge Clock);
      Dmarequest[0] = 1;
      repeat(2) @(negedge Clock);
      Dmarequest[0] = 0;
    end  
    else
      Dmarequest[0] = 0;
  end
  begin
    if(Dma.channel[1]== 1)
    begin
      repeat(Dma.Delay[1]) @(negedge Clock);
      Dmarequest[1] = 1;
      repeat(2) @(negedge Clock);
      Dmarequest[1] = 0;
    end
    else
      Dmarequest[1] = 0;
    end
  begin
    if(Dma.channel[2] == 1)
    begin
      repeat(Dma.Delay[2]) @(negedge Clock);
      Dmarequest[2] = 1;
      repeat(2) @(negedge Clock);
      Dmarequest[2] = 0;
    end
    else
      Dmarequest[2] = 0;
  end
  begin
    if(Dma.channel[3] == 1)
    begin
      repeat(Dma.Delay[3]) @(negedge Clock);
      Dmarequest[3] = 1;
      repeat(2) @(negedge Clock); 
      Dmarequest[3] = 0;
    end
    else
      Dmarequest[3] = 0;
  end
join
endtask

endmodule
