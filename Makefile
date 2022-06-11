# Makefile
RTL= RegisterPackage.sv SystemBusIF.sv ControlIF.sv BusFunctionalModel.sv AddressLatch.sv PortDecoder.sv DataPath.sv PriorityEncoder.sv TimingControlLogic.sv DMAControllerTop.sv Memory_IO.sv SVARegister.sv tb.sv

work= work #library name  

VSIMBATCH= -c -do "run -all; exit"

lib: 
	vlib $(work)

compile:
	vlog  $(RTL)
	
sim:
	vsim $(VSIMBATCH) work.TestBenchTop

		
clean:
	clear

all: clean lib compile sim



