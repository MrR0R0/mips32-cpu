//===============================================================================
//
//			M.M. Roshani - 402101855
//
//			Implemented Instructions are:
//			R format:  add(u), sub(u), and, or, xor, nor, slt, sltu;
//			I format:  beq, bne, lw, sw, addi(u), slti, sltiu, andi, ori, xori, lui.
//
//===============================================================================

`timescale 1ns/1ns

   `define ADD  4'h0
   `define SUB  4'h1
   `define SLT  4'h2
   `define SLTU 4'h3
   `define AND  4'h4
   `define OR   4'h5
   `define NOR  4'h6
   `define XOR  4'h7
   `define LUI  4'h8

module single_cycle_mips 
(
	input clk,
	input reset
);
 
	initial begin
		$display("Single Cycle MIPS Implemention");
		$display("M.M.Roshani - 402101855");
	end

	reg [31:0] PC;          // Keep PC as it is, its name is used in higher level test bench

   wire [31:0] instr;
   wire [5:0] op   = instr[31:26];
   wire [5:0] func = instr[5:0];

   wire [31:0] RD1, RD2, AluResult, MemReadData;

   wire AluZero;

   // Control Signals

   wire PCSrc = op == 6'b000100 ? AluZero :// beq
                op == 6'b000101 ? !AluZero :// bne
                1'b0; //otherwise

   reg SZEn, ALUSrc, RegDst, MemtoReg, RegWrite, MemWrite;


   reg [3:0] AluOP;

	
	// CONTROLLER COMES HERE

   always @(*) begin
      SZEn = 1'b0; //if 1: sign extend, if 0: zero extend
      AluOP = 4'h0;
      ALUSrc = 1'b0;
      RegDst = 1'b0;
      MemtoReg = 1'b0;
      RegWrite = 1'b0;
      MemWrite = 1'b0;

      case(op)
         // I formats

         //lw
         6'b100011: begin
            SZEn = 1'b1;
            RegWrite = 1'b1;
            MemtoReg = 1'b1;
            AluOP = `ADD;
            ALUSrc = 1'b1;
            // $display("we detected lw");
         end

         //sw
         6'b101011: begin
            AluOP = `ADD;
            MemWrite = 1'b1;
            SZEn = 1'b1;
            ALUSrc = 1'b1;
            // $display("we detected sw");
         end

         //beq
         6'b000100: begin
            SZEn = 1'b1;
            ALUSrc = 1'b0;
            AluOP = `XOR;
            // $display("we detected beq");
         end

         //bne
         6'b000101: begin
            SZEn = 1'b1;
            ALUSrc = 1'b0;
            AluOP = `XOR;
            // $display("we detected bne");
         end

         //slti
         6'b001010: begin
            AluOP = `SLT;
            SZEn = 1'b1;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected slti");
         end

         //sltiu
         6'b001011: begin
            AluOP = `SLTU;
            SZEn = 1'b1;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected sltiu");
         end

         //andi
         6'b001100: begin
            AluOP = `AND;
            SZEn = 1'b0;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected andi");
         end

         //ori
         6'b001101: begin
            AluOP = `OR;
            SZEn = 1'b0;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected ori");
         end

         //xori
         6'b001110: begin
            AluOP = `XOR;
            SZEn = 1'b0;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected xori");
         end

         //lui
         6'b001111: begin
            AluOP = `LUI;
            SZEn = 1'b0;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected lui");
         end

         //addi - addiu
         6'b001000, 6'b001001: begin
            AluOP = `ADD;
            SZEn = 1'b1;
            RegWrite = 1'b1;
            RegDst = 1'b0;
            ALUSrc = 1'b1;
            // $display("we detected addi(u)");

         end


         // R-formats


         6'b000000: begin
            RegWrite = 1'b1;
            RegDst = 1'b1;
            ALUSrc = 1'b0;
            case(func)
               //add - addu
               6'b100000, 6'b100001: begin
                  AluOP = `ADD;
                  // $display("we detected add(u)");
               end

               // sub(u)
               6'b100010, 6'b100011: begin
                  AluOP = `SUB;
                  // $display("we detected sub(u)");
               end
               
               // and
               6'b100100: begin
                  AluOP = `AND;
                  // $display("we detected and");
               end
               
               // or
               6'b100101: begin
                  AluOP = `OR;
                  // $display("we detected or");
               end

               // xor
               6'b100110: begin
                  AluOP = `XOR;
                  // $display("we detected xor");
               end

               // nor
               6'b100111: begin
                  AluOP = `NOR;
                  // $display("we detected nor");
               end

               // slt
               6'b101010: begin
                  AluOP = `SLT;
                  // $display("we detected slt");
               end

               // sltu
               6'b101011: begin
                  AluOP = `SLTU;
                  // $display("we detected sltu");
               end
            endcase
            
         end

      endcase

   end

	// DATA PATH STARTS HERE

   wire [31:0] PCplus4 = PC + 4'h4;

   wire [31:0] WD = MemtoReg ? MemReadData : AluResult;

   wire [4:0] WR = RegDst ? instr[15:11] : instr[20:16];

   wire [31:0] Imm32 = SZEn ? {{16{instr[15]}},instr[15:0]} : {16'h0, instr[15:0]};
                    // ZSEn: 1 sign extend, 0 zero extend

   wire [31:0] PCbranch = PCplus4 + (Imm32 << 2);


   always @(posedge clk)
      if(reset)
         PC <= 32'h0;
      else
         PC <= PCSrc ? PCbranch : PCplus4;

//==========================================================//
//	instantiated modules
//==========================================================//

// Register File

   reg_file rf
   (
      .write ( RegWrite ),
      .RR1   ( instr[25:21] ),
      .RR2   ( instr[20:16] ),
      .*
	);

   my_alu alu
   (
      .Op( AluOP ),
      .A ( RD1 ),
      .B ( ALUSrc ? Imm32 : RD2),
      .X ( AluResult ),
      .Z ( AluZero )
   );
   
//	Instruction Memory
	async_mem imem			// keep the exact instance name
	(
		.clk		   (1'b0),
		.write		(1'b0),		// no write for instruction memory
		.address	   ( PC ),		   // address instruction memory with pc
		.write_data	(32'bx),
		.read_data	( instr )
	);
	
// Data Memory
	async_mem dmem			// keep the exact instance name
	(
		.clk		   ( clk ),
		.write		( MemWrite ),
		.address	   ( AluResult ),
		.write_data	( RD2 ),
		.read_data	( MemReadData )
	);

endmodule


//===============================================================================

module my_alu(
   input  [3:0] Op,
   input  [31:0] A,
   input  [31:0] B,
   output [31:0] X,
   output        Z
   );

   wire sub = Op != `ADD;
   wire [31:0] bb = sub ? ~B : B;
   wire [32:0] sum = A + bb + sub;
   wire sltu = ! sum[32];

   wire v = sub ?
            ( A[31] != B[31] && A[31] != sum[31] )
          : ( A[31] == B[31] && A[31] != sum[31] );

   wire slt = v ^ sum[31];

   reg [31:0] x;

   always @( * ) begin
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x = A & B;
         `OR  : x = A | B;
         `NOR : x = ~(A | B);
         `XOR : x = A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         default : x = 32'hxxxxxxxx;
      endcase
      $display ("[$display] A=0x%0h", A);
      $display ("[$display] B=0x%0h", B);
      $display ("[$display] res=0x%0h", x);
   end

   assign X = x;
   assign Z = x == 32'h00000000;

endmodule

//===============================================================================






// A note to myself:
// Don't leave any wire as don't care =/