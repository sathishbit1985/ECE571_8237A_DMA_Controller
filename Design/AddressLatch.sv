//////////////////////////////////////////////////////////////////////////////////
// Designer Name: Ramesh Chandar Aniruddh Punnai
// Module Name: AddressLatch
// Project Name: DMA Controller
//////////////////////////////////////////////////////////////////////////////////

module AddressLatch (SystemBusIF.AddressLatch alif, input logic [15:0] AD15_AD0, input logic ALE);

  logic STB;
  logic [15:0] DLatchOut;
  	
  //2 to 1 mux for selecting strobe line for address latch
  assign STB = alif.AEN ? alif.ADSTB : ALE;
  
  //AD7-0 latch with tristate output buffer
  always_latch
  begin
  	if(ALE) DLatchOut[7:0] <= AD15_AD0[7:0];
  end
  assign alif.Address[7:0] = ~alif.AEN ? DLatchOut[7:0] :'z ;
  
  //AD15-8 latch with tristate output buffer
  always_latch
  begin
  	if(STB) DLatchOut[15:8] <= AD15_AD0[15:8];
  end
  assign alif.Address[15:8] = DLatchOut[15:8];
  
endmodule
