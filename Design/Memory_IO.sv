module Memory(SystemBusIF.MemoryDevice pin);

logic [7:0] Mem[16'hFFFF:0];
int i=0;

initial
begin
for(i=0;i<16'hFFFF;i++)
Mem[i]=0;
end

  assign pin.Data = ~pin.nMEMR ? Mem[pin.Address] : 'z;

  always@(posedge pin.Clock)
begin
  if(~pin.nMEMW)
    Mem[pin.Address] <= pin.Data;
end

endmodule




module IO(input logic Dmatransfer, input logic Clock, Reset, Dack, nIOR, nIOW, inout [7:0] Data, output logic Dreq);

logic[15:0] IOMemoryAddress=0;
int i=0;
logic [7:0] IOMemory[16'hFFFF:0];

initial
begin
for(i=0;i<16'hFFFF;i++)
IOMemory[i]=0;
end

always_comb
begin
if(Dmatransfer)
Dreq = 1;
if(Dack)
Dreq = 0;
end 

assign Data = (Dack && ~nIOR) ? (~IOMemoryAddress[7:0]) : 'z;

always@(posedge Clock)
begin
if(Reset)
  IOMemoryAddress <= '0;
else if(Dack && ~nIOW)
  begin
   IOMemory[IOMemoryAddress] <= Data;
   IOMemoryAddress <= IOMemoryAddress + 1;
  end
else if(Dack && ~nIOR)
  IOMemoryAddress <= IOMemoryAddress + 1;
else
  IOMemoryAddress <= IOMemoryAddress; 
end
endmodule




//IODevices Module will respond only to DMA Transfers and does not support Processor requests.
module IODevices(input logic [3:0]Dmatransfer,SystemBusIF.IODevice pin);

genvar i;
generate 
for(i=0;i<4;i++)
  IO M1 (Dmatransfer[i],pin.Clock, pin.Reset, pin.Dack[i], pin.nIOR, pin.nIOW, pin.Data, pin.Dreq[i]);
endgenerate

endmodule

