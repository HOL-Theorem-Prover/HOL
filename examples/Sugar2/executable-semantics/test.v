// BUF from Chapter 4 of FoCs User's Manual (www.haifa.il.ibm.com/projects/verification/focs/)

//---------------------------------- Sender ----------------------------------
// Send the sequence 0, 1, 2, ... , 99

module Sender (BtoS_ACK, StoB_REQ, DI);

input         BtoS_ACK;
output        StoB_REQ;
output [31:0] DI;

// Can't assign to output wires, so need to connect them to registers
reg           StoB_REQ_reg;      // Drives StoB_REQ
reg    [31:0] DI_reg;            // Drives DI (with 0, 1, 2, ... , 99)

assign StoB_REQ = StoB_REQ_reg;  // Drive wire StoB_REQ
assign DI       = DI_reg;        // Drive wire DI (actually a 32-bit bus)

initial
 begin
  DI_reg = 0;
  #10
  while (DI_reg < 100)
   begin
    StoB_REQ_reg = 1;            // Assert request
     @(posedge BtoS_ACK)         // Wait for ack to be asserted
     #10                         // Wait 10 time units
     StoB_REQ_reg = 0;           // Deassert request
     #10                         // Wait 10 time units
     @(negedge BtoS_ACK)         // Wait for ack to be de-asserted
     #10                         // Wait 10 time units before incrementing data
     DI_reg = DI_reg + 1;        // Increment data to be sent next iteration
    end
  #10 $finish;
 end

endmodule

//---------------------------------- BUF -------------------------------------
// Receive data from Sender and then send it to Receiver

module BUF (clk,StoB_REQ, RtoB_ACK, DI, BtoS_ACK, BtoR_REQ, DO);

input         clk;
input         StoB_REQ;
input         RtoB_ACK;
input  [31:0] DI;
output        BtoS_ACK;
output        BtoR_REQ;
output [31:0] DO;

// Can't assign to output wires, so need to connect them to registers
reg           BtoS_ACK_reg;      // Drives BtoS_ACK
reg           BtoR_REQ_reg;      // Drives BtoR_REQ
reg    [31:0] DO_reg;            // Drives DO

// BUF internal state registers
reg           free;              // Flag to say if BUF is free to receive new data
reg    [31:0] data;              // Data last read from Sender

assign BtoS_ACK = BtoS_ACK_reg;  // Drive wire BtoS_ACK
assign BtoR_REQ = BtoR_REQ_reg;  // Drive wire BtoR_REQ
assign DO       = DO_reg;        // Drive wire DO (actually a 32-bit bus)

initial 
 begin 
  BtoS_ACK_reg = 0;              // Initially BtoS_ACK not asserted
  BtoR_REQ_reg = 0;              // Initially BtoR_REQ not asserted
  free = 1;                      // Initially free is true
 end  

always @(posedge clk)
 if (StoB_REQ && free)           // Wait for StoB_REQ to be asserted and BUF free
  begin 
   free = 0;                     // Set BUF to be not free
   data = DI;                    // Read data
   #10 BtoS_ACK_reg = 1;         // Tell Sender data is aquired
   #10 DO_reg = data;            // Put dat on DO
   #10 BtoR_REQ_reg = 1;         // Assert BtoR_REQ
   @(posedge RtoB_ACK)           // Wait for Receiver to acknowledge receipt of data
   #10 BtoR_REQ_reg = 0;         // Deassert BtoR_REQ
   #10 BtoS_ACK_reg = 0;         // Deassert BtoS_ACK
   free = 1;                     // Set BUF to be free
  end
 else 
  #10 begin end

endmodule



//---------------------------------- Receiver --------------------
// Receive data from BUF

module Receiver (BtoR_REQ, DO, RtoB_ACK);

input         BtoR_REQ;
input  [31:0] DO;
output        RtoB_ACK;

// Can't assign to output wire RtoB_ACK, so need to connect it to a register
reg           RtoB_ACK_reg;      // Drives BtoR_REQ

// Receiver internal state registers
reg    [31:0] data;              // Data last read from BUF

assign RtoB_ACK = RtoB_ACK_reg;  // Drive wire RtoB_ACK

initial RtoB_ACK_reg = 0;        // Initially RtoB_ACK not asserted

always
 @(posedge BtoR_REQ)             // Wait for BtoR_REQ to be asserted
 begin
  #10 data = DO;                 // Copy data from DO
  #10 RtoB_ACK_reg = 1;          // Assert RtoB_ACK to say data aquired
  #10 RtoB_ACK_reg = 0;          // Deassert RtoB_ACK
 end

endmodule

//---------------------------------- Test ------------------------------------
// Top level module linking Sender, BUF and Receiver

module test ();

wire         StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK;
wire  [31:0] DI, DO;
reg          clk;

Sender   M1(BtoS_ACK, StoB_REQ, DI);
BUF      M2(clk,StoB_REQ, RtoB_ACK, DI, BtoS_ACK, BtoR_REQ, DO);
Receiver M3(BtoR_REQ, DO, RtoB_ACK);

// Make clock tick
initial
 forever 
  begin
   #10 clk = 0;
   #10 clk = 1;
  end


// Xtreme kludge to generate output that can be munged
// into SimRun example in test (have eliminated strings)

initial
 begin
 $monitor 
   ("Time = %0d, clk = %0d, StoB_REQ = %0d, BtoS_ACK = %0d, DI = %0d, BtoR_REQ = %0d, RtoB_ACK = %0d, DO = %0d",
    $time, clk, StoB_REQ, BtoS_ACK, DI, BtoR_REQ, RtoB_ACK, DO);
 end

//initial
// begin
// $monitor 
//  ("((if %0d=1 then {\"StoB_REQ\"} else {}) UNION\
//(if %0d=1 then {\"BtoS_ACK\"} else {}) UNION\
//(if %0d=1 then {\"BtoR_REQ\"} else {}) UNION\
//(if %0d=1 then {\"RtoB_ACK\"} else {}));",
//   StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK);
// end

endmodule



//initial
// $monitor 
//  ("val At_%0d = ``(StoB_REQ = %0d) /\\ (BtoS_ACK = %0d) /\\ (BtoR_REQ = %0d) /\\ (RtoB_ACK = %0d)``;",
//   $time, StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK);



//initial
// begin
// $monitor 
//   ("Time = %0d, clk = %0d, StoB_REQ = %0d, BtoS_ACK = %0d, DI = %0d, BtoR_REQ = %0d, RtoB_ACK = %0d, DO = %0d",
//    $time, clk, StoB_REQ, BtoS_ACK, DI, BtoR_REQ, RtoB_ACK, DO);
// end



