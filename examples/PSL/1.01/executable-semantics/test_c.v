// BUF from Chapter 4 of FoCs User's Manual (www.haifa.il.ibm.com/projects/verification/focs/)

//---------------------------------- Sender ----------------------------------
// Send the sequence 0, 1, 2, ... , 99

module Sender (BtoS_ACK, StoB_REQ, DI);

input         BtoS_ACK;
output        StoB_REQ;
output [31:0] DI;
reg           StoB_REQ;
reg    [31:0] DI;

initial
 begin
  DI = 0;
  #10
  while (DI < 100)
   begin
    StoB_REQ = 1;                // Assert request
     @(posedge BtoS_ACK)         // Wait for ack to be asserted
     #10                         // Wait 10 time units
     StoB_REQ = 0;               // Deassert request
     #10                         // Wait 10 time units
     @(negedge BtoS_ACK)         // Wait for ack to be de-asserted
     #10                         // Wait 10 time units before incrementing data
     DI = DI + 1;                // Increment data to be sent next iteration
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
reg           BtoS_ACK;
reg           BtoR_REQ;
reg    [31:0] DO;

// BUF internal state registers
reg           free;              // Flag to say if BUF is free to receive new data
reg    [31:0] data;              // Data last read from Sender

initial 
 begin 
  BtoS_ACK = 0;                  // Initially BtoS_ACK not asserted
  BtoR_REQ = 0;                  // Initially BtoR_REQ not asserted
  free = 1;                      // Initially free is true
 end  

always @(posedge clk)
 if (StoB_REQ && free)           // Wait for StoB_REQ to be asserted and BUF free
  begin 
   free = 0;                     // Set BUF to be not free
   data = DI;                    // Read data
   #10 BtoS_ACK = 1;             // Tell Sender data is aquired
   #10 DO = data;                // Put dat on DO
   #10 BtoR_REQ = 1;             // Assert BtoR_REQ
   @(posedge RtoB_ACK)           // Wait for Receiver to acknowledge receipt of data
   #10 BtoR_REQ = 0;             // Deassert BtoR_REQ
   #10 BtoS_ACK = 0;             // Deassert BtoS_ACK
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
reg           RtoB_ACK;

// Receiver internal state registers
reg    [31:0] data;              // Data last read from BUF

initial RtoB_ACK = 0;            // Initially RtoB_ACK not asserted

always
 @(posedge BtoR_REQ)             // Wait for BtoR_REQ to be asserted
 begin
  #10 data = DO;                 // Copy data from DO
  #10 RtoB_ACK = 1;              // Assert RtoB_ACK to say data aquired
  #10 @(negedge BtoR_REQ)        // Wait for BtoR_REQ to be deasserted
  #10 RtoB_ACK = 0;              // Deassert RtoB_ACK
 end

endmodule

// ------------------------------- Checker ------------------------------------
// The following regular expression as a Verilog state machine
// sere2regexp
//   (S_REPEAT S_TRUE ;;
//    S_BOOL (B_AND (B_NOT (B_PROP StoB_REQ),B_PROP BtoS_ACK)) ;;
//    S_BOOL (B_PROP StoB_REQ))

module Checker (StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK, state);

input StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK;
output [2:0] state;
reg    [2:0] state;

initial state = 0;

always @ (StoB_REQ or BtoS_ACK or BtoR_REQ or RtoB_ACK)
begin
  case (state)
    0:
      if (StoB_REQ) state = 1;
      else
        if (BtoS_ACK) state = 2;
        else state = 1;
    
    1:
      if (StoB_REQ) state = 1;
      else
        if (BtoS_ACK) state = 2;
        else state = 1;
    
    2:
      if (StoB_REQ) state = 3;
      else
        if (BtoS_ACK) state = 2;
        else state = 1;
    
    3: begin $display ("Checker: property violated!"); $finish; end
    
    default: begin $display ("Checker: unknown state"); $finish; end
  endcase
end

endmodule

//---------------------------------- Test ------------------------------------
// Top level module linking Sender, BUF and Receiver

module test ();

wire         StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK;
wire  [31:0] DI, DO;
wire   [2:0] state;
reg          clk;


Sender   M1(BtoS_ACK, StoB_REQ, DI);
BUF      M2(clk,StoB_REQ, RtoB_ACK, DI, BtoS_ACK, BtoR_REQ, DO);
Receiver M3(BtoR_REQ, DO, RtoB_ACK);
Checker  M4(StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK, state);

initial $monitor("State: %0d", state);

// Make clock tick
initial
  forever 
  begin
    #10 clk = 0;
    #10 clk = 1;
  end

// Xtreme kludge to generate output that can be munged
// into SimRun example in test (have eliminated strings)

//initial
// begin
// $monitor 
//   ("Time = %0d, clk = %0d, StoB_REQ = %0d, BtoS_ACK = %0d, DI = %0d, BtoR_REQ = %0d, RtoB_ACK = %0d, DO = %0d",
//    $time, clk, StoB_REQ, BtoS_ACK, DI, BtoR_REQ, RtoB_ACK, DO);
// end

// initial
//  begin
//  $monitor 
//   ("((if %0d=1 then {\"StoB_REQ\"} else {}) UNION\
// (if %0d=1 then {\"BtoS_ACK\"} else {}) UNION\
// (if %0d=1 then {\"BtoR_REQ\"} else {}) UNION\
// (if %0d=1 then {\"RtoB_ACK\"} else {}));",
//    StoB_REQ, BtoS_ACK, BtoR_REQ, RtoB_ACK);
//  end

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



