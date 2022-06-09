module TestBenchTop();

parameter DMAADDRESS = 4'hF;
logic Clock =1 , Reset;
logic [7:0] DataRead;
typedef struct packed{
logic [3:0] Address;
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

SystemBusIF MainBus(Clock,Reset);
Memory M(MainBus);
IODevices IO (Dmarequest, MainBus);
BusFuncModel Bus (MainBus, AD15_AD0, ALE);
AddressLatch AL (MainBus, AD15_AD0, ALE );
PortDecoder P1 (MainBus, nCS);
DMAControllerTop DMATop(MainBus, nCS , AD15_AD0[15:8]);

RegisterWR [32:0] DmaRegisterData = { '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH0_CURRENT_ADDRESS,8'hA5,1'b1},    '{ DMAADDRESS,CH0_CURRENT_ADDRESS,8'hA5,1'b1}, 
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH0_CURRENT_WORD_COUNT,8'h10,1'b1}, '{ DMAADDRESS,CH0_CURRENT_WORD_COUNT,8'h00,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH1_CURRENT_ADDRESS,8'hA5,1'b1},    '{ DMAADDRESS,CH1_CURRENT_ADDRESS,8'hA5,1'b1}, 
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH1_CURRENT_WORD_COUNT,8'h10,1'b1}, '{ DMAADDRESS,CH1_CURRENT_WORD_COUNT,8'h00,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH2_CURRENT_ADDRESS,8'h75,1'b1},    '{ DMAADDRESS,CH2_CURRENT_ADDRESS,8'hEA,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH2_CURRENT_WORD_COUNT,8'hFF,1'b1}, '{ DMAADDRESS,CH2_CURRENT_WORD_COUNT,8'h00,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH3_CURRENT_ADDRESS,8'h75,1'b1},    '{ DMAADDRESS,CH3_CURRENT_ADDRESS,8'hEA,1'b1},
                                      '{ DMAADDRESS,CLEAR_BPFF,8'h00,1'b1},         '{ DMAADDRESS,CH3_CURRENT_WORD_COUNT,8'hFF,1'b1}, '{ DMAADDRESS,CH3_CURRENT_WORD_COUNT,8'h00,1'b1},
				                      '{ DMAADDRESS,MASTER_CLEAR,8'h69,1'b0},       '{ DMAADDRESS,COMMAND_REGISTER,8'h80,1'b0}, 
                                      '{ DMAADDRESS,MODE_REGISTER,8'hA4,1'b0},      '{ DMAADDRESS,MODE_REGISTER,8'hA9,1'b0},          '{ DMAADDRESS,MODE_REGISTER,8'h86,1'b0},
                                      '{ DMAADDRESS,MODE_REGISTER,8'h8B,1'b0},      '{ DMAADDRESS,CLEAR_MASK_REGISTER,8'h05,1'b0},	  '{ DMAADDRESS,WRITE_ALL_MASK_REGISTER,8'h00,1'b0},
									  '{ DMAADDRESS,WRITE_SINGLE_MASK_REGISTER,8'h00,1'b0}};

initial
  forever #1 Clock = ~Clock;


initial
begin
	repeat(2) @(negedge Clock) Reset=1;
	@(negedge Clock) Reset=0;

	//Write all DMA Registers
	foreach( DmaRegisterData[i])
		Bus.WriteBUS({DmaRegisterData[i].Data, DmaRegisterData[i].Address ,DmaRegisterData[i].RegCommandCode},1'b0);
	//Read DMA registers which are readable 
	foreach(DmaRegisterData[i])
    begin
		if( DmaRegisterData[i].RegCommandCode == CLEAR_BPFF)
			Bus.WriteBUS({DmaRegisterData[i].Data, DmaRegisterData[i].Address ,DmaRegisterData[i].RegCommandCode},1'b0);
		else if(DmaRegisterData[i].Read === 1)
		begin	
			Bus.ReadBUS({DmaRegisterData[i].Address ,DmaRegisterData[i].RegCommandCode},1'b0, DataRead);
			if(DmaRegisterData[i].RegCommandCode !==  CLEAR_BPFF)
				repeat(4) @(negedge Clock);
			if(DmaRegisterData[i].Data !== DataRead)
				$display("Data written= %h Data Read = %h", DmaRegisterData[i].Data , DataRead);	
		end
    end
	@(negedge Clock)  Dma.channel = 4'b0001;
    Dma.Delay   = '0;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(!MainBus.nEOP);
	repeat(4) @(negedge Clock);
	
	Bus.WriteBUS({8'h90, DMAADDRESS, 4'(COMMAND_REGISTER)},1'b0);
	repeat(8) @(negedge Clock);
	@(negedge Clock)  Dma.channel = 4'b0010;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(MainBus.nEOP == 0);
	repeat(4) @(negedge Clock);
	Bus.WriteBUS({8'h80,DMAADDRESS, 4'(COMMAND_REGISTER)},1'b0);
	@(negedge Clock)  Dma.channel = 4'b0100;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(MainBus.nEOP == 0);
	repeat(4) @(negedge Clock);
	
	Bus.WriteBUS({8'h90,DMAADDRESS, 4'(COMMAND_REGISTER)},1'b0);
	@(negedge Clock)  Dma.channel = 4'b1000;
	@(negedge Clock)  Dmaaccess(Dma);
	@(negedge Clock);
	wait(MainBus.nEOP == 0);
	repeat(4) @(negedge Clock); 
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
