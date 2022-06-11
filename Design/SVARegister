module SVARegister(SystemBusIF Bus, ControlIF ctrl,input Clock,Reset);


//If DACK[i] signal is asserted,the current address register of the channel 'i' should Increment after 3 cycles if bit number 3 of mode register is 0
genvar i;
generate
for(i=0;i<4;i++)
begin
AddressInc_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7]))&& (!DMATop.DP.Register.i[i].Mode.Mode[3])) |=> ##2 (DMATop.DP.Register.i[i].CurrentAddress.CAddress == $past(DMATop.DP.Register.i[i].CurrentAddress.CAddress ) + 1));
end
endgenerate

//If DACK[i] signal is asserted,the current address register of the channel 'i' should decrement after 3 cycles if bit number 3 of mode register is 1
generate
for(i=0;i<4;i++)
begin
AddressDec_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) &&(DMATop.DP.Register.i[i].Mode.Mode[3])) |=> ##2 (DMATop.DP.Register.i[i].CurrentAddress.CAddress == $past(DMATop.DP.Register.i[i].CurrentAddress.CAddress ) - 1));
end
endgenerate


//If DACK[i] signal is asserted and the value in the word count register of the channel i goes from 0 to FFFFH ,the bit number 'i' of the status register should be to 1
generate
for(i=0;i<4;i++)
begin
Statusregister_a : assert property(@(posedge Clock)
$past(!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7]) |->  (DMATop.DP.Register.Status.Status[i]== 1) );
end
endgenerate

//When reset or master clear instruction is asserted , the command register and status register should be cleared
property ResetMasterClear_p;
@(posedge Clock)
(ctrl.MasterClear || Reset) |=> ##4 (DMATop.DP.Register.Command.Command == 8'h04 &&  DMATop.DP.Register.Status.Status == 8'h00);
endproperty

ResetMasterClear_a : assert property(ResetMasterClear_p);

//If controller disable(bit number 2 of Command Register) is 1, the control signals HRQ,HLDA,DACK[i] should not be asserted
property ControllerDisable_p;
@(posedge Clock)
(DMATop.DP.Register.Command.Command[2]) |-> (Bus.Hrq == 0 && Bus.Hlda == 0 && (Bus.Dack ^ {4{DMATop.DP.Register.Command.Command[7]}}) == 4'b1111);
endproperty

ControllerDisable_a : assert property(ControllerDisable_p);

//If DACK[i] is asserted and if its write transfer(bit number 3 and 2 of mode register is 0,1 respectively) , MEMW and IOR signals should be asserted in next cycle and remain asserted till DMA transfer is done
generate
for(i=0;i<4;i++)
begin
WriteTransfer_a : assert property(@(posedge Clock)
($rose(!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (DMATop.DP.Register.i[i].Mode.Mode ==? 6'bxxxx01))  |=> ##[0:3] (Bus.nIOR==0 && Bus.nMEMW==0 ) );
end
endgenerate

//If DACK[i] is asserted and if its read transfer(bit number 3 and 2 of mode register is 1,0 respectively) , MEMR and IOW signals should be asserted in next cycle and remain asserted till D//MA transfer is  done.
generate
for(i=0;i<4;i++)
begin
ReadTransfer_a : assert property(@(posedge Clock)
($rose(!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (DMATop.DP.Register.i[i].Mode.Mode ==? 6'bxxxx10))  |=> ##[0:3] (Bus.nIOW == 0 && Bus.nMEMR == 0) );
end
endgenerate

//If DACK[i] is asserted ,word count is greater than 0 and 8 lower address bits(A7-A0) for channel 'i' is FFH(Address increments) , the ADSTB signal should be asserted in next cycle.
generate
for(i=0;i<4;i++)
begin
StrobeCurrentAddressInc_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (!DMATop.DP.Register.Command.Command[5]) && (DMATop.DP.Register.i[i].CurrentAddress.CAddress[7:0] == 8'hFF) && DMATop.DP.Register.i[i].CurrentWordCount.CWordCount > 0 )  |=> $rose(Bus.ADSTB));
end
endgenerate

//If DACK[i] is asserted ,word count is greater than 0 and 8 lower address bits(A7-A0) for channel 'i' is 00H(Address decrements) , the ADSTB signal should be asserted in next cycle.
generate
for(i=0;i<4;i++)
begin
StrobeCurrentAddressDec_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (!DMATop.DP.Register.Command.Command[5]) && (DMATop.DP.Register.i[i].CurrentAddress.CAddress[7:0] == 8'h00) && DMATop.DP.Register.i[i].CurrentWordCount.CWordCount > 0 )  |=> $rose(Bus.ADSTB));
end
endgenerate

//If DACK[i] is asserted ,word count is greater than 0 and 8 lower address bits(A7-A0) for channel 'i' is FFH(Address increments) , the ADSTB signal should be asserted in next cycle.
generate
for(i=0;i<4;i++)
begin
StrobeTempAddressInc_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (!DMATop.DP.Register.Command.Command[5]) && (DMATop.DP.Register.i[i].TempAddress.TAddress[7:0] == 8'hFF) && (DMATop.DP.Register.i[i].TempWordCount.TWordCount > 0 )  |-> ##[0:5]$rose(Bus.ADSTB)));
end
endgenerate

//If DACK[i] is asserted ,word count is greater than 0 and 8 lower address bits(A7-A0) for channel 'i' is 00H(Address decrements) , the ADSTB signal should be asserted in next cycle.
generate
for(i=0;i<4;i++)
begin
StrobeTempAddressDec_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && (DMATop.DP.Register.Command.Command[5]) && (DMATop.DP.Register.i[i].TempAddress.TAddress[7:0] == 8'h00) && DMATop.DP.Register.i[i].TempWordCount.TWordCount > 0 )  |-> ##[0:5] $rose(Bus.ADSTB));
end
endgenerate


//If DACK[i] and address data strobe signal is asserted , then higher 8 bits of address bus should be updated with higher bits of current address register.
generate
for(i=0;i<4;i++)
begin
StrobehigherAddressBus_a : assert property(@(posedge Clock)
((!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) && $rose(Bus.ADSTB)) |-> (Bus.Address[15:8] == DMATop.DP.Register.i[i].CurrentAddress.CAddress[15:8]) );
end
endgenerate


//If DACK[i] is asserted and the value in the word count register of the channel 'i' goes from 0 to FFFFH ,the control signals HRQ,DACK and HLDA should be deasserted in the next cycle.
generate
for(i=0;i<4;i++)
begin
DMATransferend_a : assert property(@(posedge Clock)
$rose(!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) |=>   (DMATop.DP.Register.i[i].CurrentWordCount.CWordCount == 16'hFFFF) [->1] ##1 (!Bus.Hrq && !Bus.Hlda && (Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])));
end
endgenerate



//If DACK[i] signal is asserted,the current word count register of the channel 'i' should Decrement after every 3 cycles
generate
for(i=0;i<4;i++)
begin
WordCountDec_a : assert property(@(posedge Clock)
(!(Bus.Dack[i] ^ DMATop.DP.Register.Command.Command[7])) |=> ##2 (DMATop.DP.Register.i[i].CurrentWordCount.CWordCount== $past(DMATop.DP.Register.i[i].CurrentWordCount.CWordCount ) -1));
end
endgenerate

endmodule


