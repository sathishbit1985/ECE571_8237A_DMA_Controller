//test bench to verify the IO and Memory transfers
//test bench is only instantiated with IO,Memory and Interface modules. DMA module and Bus Functional Module is not instantiated in the testbench code.
module test;

logic [7:0] IOData,MemoryData;
int n=0;
logic Reset;
logic Clock=1;
logic nIOR_Drive, nIOW_Drive;

typedef struct packed{
logic [3:0] channel; 
logic [7:0] [3:0] Delay;
}Dmatransfer;
logic [3:0]Dmarequest;
Dmatransfer Dma;

SystemBusIF MainBus(Clock,Reset);

Memory MEM (MainBus);
IODevices IOD (Dmarequest,MainBus);

initial
  forever #1 Clock =~Clock;

assign MainBus.nIOR = nIOR_Drive;
assign MainBus.nIOW = nIOW_Drive;

initial
begin
  MainBus.Dack  = '0;
  nIOW_Drive  = 1;
  nIOR_Drive  = 1;
  MainBus.nMEMW = 1;
  MainBus.nMEMR = 1;
  @(negedge Clock)  Dma.channel = 4'b0001;
                    Dma.Delay   = '0;
  @(negedge Clock)  Dmaaccess(Dma);
  @(negedge Clock)  IOtoMemoryTransfer();
  @(negedge Clock)  MemorytoIOTransfer();
  $finish;
end  
  
initial
begin
  $dumpfile("dump.vcd"); $dumpvars;
end

//task to trigger IO to Memory Dma transfer(nIOR = 0  and nMEMW =0)
task IOtoMemoryTransfer();
begin
  @(negedge Clock) MainBus.Dack    = Dma.channel;                  //used Dma.channel variable to active the Dack for the same channel 
  @(negedge Clock) MainBus.Address = 0;
  @(negedge Clock) nIOR_Drive    = 0;
                   MainBus.nMEMW   = 0;
  repeat(255) @(negedge Clock) MainBus.Address=MainBus.Address+1;  //to transfer 255 bytes of data from IO to Memory
  @(negedge Clock) nIOR_Drive    = 1;
                   MainBus.nMEMW   = 1;
                   MainBus.Dack    = '0;
end
endtask

//task to trigger Memory to IO Dma transfer(nIOW =0 and nMEMR=0)            
task MemorytoIOTransfer();
begin
  @(negedge Clock) MainBus.Dack    = Dma.channel;                //used Dma.channel variable to active the Dack for the same channel 
  @(negedge Clock) MainBus.Address = 0;
  @(negedge Clock) nIOW_Drive    = 0;
                   MainBus.nMEMR   = 0;
  repeat(255) @(negedge Clock) MainBus.Address=MainBus.Address+1; //to transfer 255 bytes of data from Memory to IO
  @(negedge Clock) nIOW_Drive    = 0;
                   MainBus.nMEMR   = 0;
                   MainBus.Dack    = '0;
end
endtask

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
