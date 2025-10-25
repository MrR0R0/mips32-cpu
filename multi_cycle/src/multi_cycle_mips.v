`timescale 1ns/100ps

   `define ADD  4'b0000
   `define SUB  4'b0001
   `define SLT  4'b0010
   `define SLTU 4'b0011
   `define AND  4'b0100
   `define XOR  4'b0101
   `define OR   4'b0110
   `define NOR  4'b0111
   `define LUI  4'b1000
   `define SLL 4'b1001
   `define SRL 4'b1010
   `define DIVU 4'b1011

`default_nettype none

module multi_cycle_mips(

   input wire clk,
   input wire reset,

   // Memory Ports
   output wire  [31:0] mem_addr,
   input  wire  [31:0] mem_read_data,
   output wire  [31:0] mem_write_data,
   output wire         mem_read,
   output wire         mem_write
);

   // Data Path Registers
   // MRE: Mem Read Enable
   // MWE: Mem Write Enable
   reg MRE, MWE;
   // IR: Instruction Register
   // MDR: Mem. Data Reg
   // MAR: Memory Address Register
   reg [31:0] A, B, PC, IR, MDR, MAR, hiReg, loReg; 

   // Data Path Control Lines, don't forget, regs are not always register !!
   // These are combinational logic 
   reg setMRE, clrMRE, setMWE, clrMWE, multStart;

   // Awrt, Bwrt: Write-enable for registers A and B
   // RFwrt: Register File Write (enables writing to the MIPS register file)
   // IRwrt: Instruction Register Write (loads a new instruction into IR)
   reg Awrt, Bwrt, RFwrt, PCwrt, IRwrt, MDRwrt, MARwrt;


   // Mux & ALU Control Line
   reg [3:0] aluOp;
   reg [2:0] aluSelB;
   reg [1:0] aluSelA;
   reg SgnExt, MemtoReg;
   reg [1:0] RegDst; //  00: IR[20:16], 01: IR[15:11], 10: 5'b11111
   reg [1:0] PCsrc; // 00: aluResult, 01: jump_PC_Address, 10: A
   reg [1:0] MARscr; // 00: PC (instruction), 01: aluResult (Data), 10: jumpAddress, 11: A
   reg [1:0] toRegSrc;



   // Wiring
   wire aluZero, multReady;
   wire [31:0] shift_amount =  IR[10:6];
   wire [31:0] aluResult, RD1, RD2, loWire, hiWire;
   wire [67:0] multResult;

   wire [4:0] RR1 = IR[25:21];
   wire [4:0] RR2 = IR[20:16];

   wire [31:0] WD = MemtoReg ? MDR : aluResult;
   wire [4:0] WR  = RegDst == 2'b10 ? 5'b11111  :
                    RegDst == 2'b01 ? IR[15:11] :
                    IR[20:16];

   wire [31:0] jump_PC_Address = {PC[31:28], IR[25:0], 2'b00};

   // Memory Ports Bindings
   assign mem_addr = MAR;
   assign mem_read = MRE;
   assign mem_write = MWE;
   assign mem_write_data = B;

   // Clocked Registers
   always @( posedge clk ) begin
      if( reset )
         PC <= #0.1 32'h00000000;
      else if( PCwrt )
         PC <= #0.1  PCsrc == 2'b00 ? aluResult :
                     PCsrc == 2'b01 ? jump_PC_Address :
                     PCsrc == 2'b10 ? A :
                     32'h00000000;

      if( Awrt ) A <= #0.1 RD1;
      if( Bwrt ) B <= #0.1 RD2;

      if( MARwrt ) MAR <= #0.1 MARscr == 2'b00 ? PC :
                               MARscr == 2'b01 ? aluResult :
                               MARscr == 2'b10 ? jump_PC_Address :
                               A;

      if( IRwrt ) IR <= #0.1 mem_read_data;
      if( MDRwrt ) MDR <= #0.1 mem_read_data;

      if( reset | clrMRE ) MRE <= #0.1 1'b0;
      else if( setMRE) MRE <= #0.1 1'b1;

      if( reset | clrMWE ) MWE <= #0.1 1'b0;
      else if( setMWE) MWE <= #0.1 1'b1;
   end

   // Register File
   reg_file rf(
      .write( RFwrt ),
      .*
   );

   // Sign/Zero Extension
   wire [31:0] SZout = SgnExt ? {{16{IR[15]}}, IR[15:0]} : {16'h0000, IR[15:0]};

   // ALU-A Mux
   wire [31:0] aluA = aluSelA == 2'b00 ? PC :
                      aluSelA == 2'b01 ? A  :
                      shift_amount;

   // ALU-B Mux
   reg [31:0] aluB;
   always @(*)
   case (aluSelB)
      3'b000: aluB = B;
      3'b001: aluB = 32'h4;
      3'b010: aluB = SZout;
      3'b011: aluB = SZout << 2;
      3'b100: aluB = hiReg;
      3'b101: aluB = loReg;
      3'b110: aluB = 32'h0000_0000;
      default : aluB = 32'hxxxxxxxx;
   endcase

   my_alu alu(
      .Op( aluOp ),
      .A( aluA ),
      .B( aluB ),
      .X( aluResult ),
      .Z( aluZero ),
      .hiReg (hiWire),
      .loReg (loWire)
   );

   // multiplier unit
   booth_signed_mult #(.n(33)) multiplier (
      .clk(clk),
      .start(multStart),
      .A({1'b0, aluA}),
      .B({1'b0, aluB}),
      .Product(multResult),
      .ready(multReady)
    );


   // Controller Starts Here

   // Controller State Registers
   reg [4:0] state, nxt_state;

   // State Names & Numbers
   localparam
      RESET = 0, FETCH1 = 1, FETCH2 = 2, FETCH3 = 3, DECODE = 4,
      EX_ALU_R = 7, EX_ALU_I = 8,
      EX_LW_1 = 11, EX_LW_2 = 12, EX_LW_3 = 13, EX_LW_4 = 14, EX_LW_5 = 15,
      EX_SW_1 = 21, EX_SW_2 = 22, EX_SW_3 = 23,
      EX_BRA_1 = 25, EX_BRA_2 = 26, EX_mult = 27;

   // State Clocked Register 
   always @(posedge clk)
      if(reset)
         state <= #0.1 RESET;
      else
         state <= #0.1 nxt_state;

   task PrepareFetch;
      begin
         MARscr = 2'b00;
         setMRE = 1;
         MARwrt = 1;
         nxt_state = FETCH1;
      end
   endtask

   // State Machine Body Starts Here
   always @( * ) begin
      SgnExt = 0; MARscr = 2'b00;
      MemtoReg = 0; RegDst = 2'b00;
      aluSelA = 2'b00; aluSelB = 3'b000; aluOp = `ADD;

      PCwrt = 0; PCsrc = 2'b00;
      Awrt = 0; Bwrt = 0;
      RFwrt = 0; IRwrt = 0;
      MDRwrt = 0; MARwrt = 0;
      setMRE = 0; clrMRE = 0;
      setMWE = 0; clrMWE = 0;

      case(state)
         RESET: begin
            PrepareFetch;
         end

         FETCH1: begin
            nxt_state = FETCH2;
         end

         FETCH2: begin
            nxt_state = FETCH3;
         end

         FETCH3: begin
            IRwrt = 1;
            PCwrt = 1;
            PCsrc = 2'b00;
            clrMRE = 1;
            aluSelA = 2'b00;
            aluSelB = 3'b001;
            aluOp = `ADD;
            nxt_state = DECODE;
         end

         DECODE: begin
            Awrt = 1;
            Bwrt = 1;
            case( IR[31:26] )
               6'b000_000:  begin       // R-format
                  case( IR[5:3] )
                     3'b000: nxt_state = EX_ALU_R; //sll - srl - sllv - srlv
                     3'b001: nxt_state = EX_ALU_R; // jr, jalr
                     3'b010: nxt_state = EX_ALU_R; //mfhi - mflo
                     3'b011: nxt_state = EX_ALU_R; // multu - divu
                     3'b100: nxt_state = EX_ALU_R; // add(u) - sub(u) and - or - xor - nor
                     3'b101: nxt_state = EX_ALU_R; // slt(u)
                     3'b110: ;
                     3'b111: ;
                  endcase
               end

               6'b001_000,             // addi
               6'b001_001,             // addiu
               6'b001_010,             // slti
               6'b001_011,             // sltiu
               6'b001_100,             // andi
               6'b001_101,             // ori
               6'b001_111,             // lui
               6'b001_110:             // xori
                  nxt_state = EX_ALU_I;

               6'b100_011: //lw
                  nxt_state = EX_LW_1;

               6'b101_011: begin //sw
                  nxt_state = EX_SW_1;
               end

               6'b000_100,  // beq
               6'b000_101:  // bne
                  nxt_state = EX_BRA_1;
               
               6'b000_010: begin // j (jump)
                  PCwrt = 1;
                  MARwrt = 1;
                  PCsrc = 2'b01;
                  MARscr = 2'b10;
                  setMRE = 1;
                  nxt_state = FETCH1;
               end

               6'b000_011: begin // jal
                  PCwrt = 1;
                  MARwrt = 1;
                  PCsrc = 2'b01;
                  MARscr = 2'b10;
                  setMRE = 1;
                  
                  MemtoReg = 0;
                  aluSelA = 2'b00; aluSelB = 3'b110;
                  RFwrt = 1;
                  aluOp = `ADD;
                  RegDst = 2'b10;
                  nxt_state = FETCH1;
               end


            endcase
         end

         EX_ALU_R: begin
            MemtoReg = 0; RegDst = 2'b01;
            aluSelA = 2'b01; aluSelB = 3'b000;
            RFwrt = 1;

            case(IR[5:0])
               //add - addu
               6'b100000, 6'b100001: begin
                  aluOp = `ADD;
                  PrepareFetch;
               end

               // sub(u)
               6'b100010, 6'b100011: begin
                  aluOp = `SUB;
                  PrepareFetch;
               end
               
               // and
               6'b100100: begin
                  aluOp = `AND;
                  PrepareFetch;
               end
               
               // or
               6'b100101: begin
                  aluOp = `OR;
                  PrepareFetch;
               end

               // xor
               6'b100110: begin
                  aluOp = `XOR;
                  PrepareFetch;
               end

               // nor
               6'b100111: begin
                  aluOp = `NOR;
                  PrepareFetch;
               end

               // slt
               6'b101010: begin
                  aluOp = `SLT;
                  PrepareFetch;
               end

               // sltu
               6'b101011: begin
                  aluOp = `SLTU;
                  PrepareFetch;
               end

               // mfhi
               6'b010000: begin
                  aluOp = `ADD;
                  aluSelB = 3'b100;
                  PrepareFetch;
               end
               
               // mflo
               6'b010010: begin
                  aluOp = `ADD;
                  aluSelB = 3'b101;
                  PrepareFetch;
               end

               // jr
               6'b001000: begin
                  RFwrt = 0;
                  PCwrt = 1;
                  MARwrt = 1;
                  PCsrc = 2'b10;
                  MARscr = 2'b11;

                  setMRE = 1;
                  nxt_state = FETCH1;
               end

               // jalr
               6'b001001: begin
                  RFwrt = 0;
                  PCwrt = 1;
                  MARwrt = 1;
                  PCsrc = 2'b10;
                  MARscr = 2'b11;

                  MemtoReg = 0;
                  aluSelA = 2'b00; aluSelB = 3'b110;
                  RFwrt = 1;
                  aluOp = `ADD;
                  RegDst = 2'b10;
                  setMRE = 1;
                  nxt_state = FETCH1;
               end

               // multu
               6'b011001: begin
                  RFwrt = 0;
                  multStart = 1;
                  nxt_state = EX_mult;

               end

               // divu
               6'b011_011: begin
                  aluOp = `DIVU;
                  hiReg = hiWire;
                  loReg = loWire;
                  PrepareFetch;
               end

               // sll
               6'b000_000: begin
                  aluOp = `SLL;
                  aluSelA = 2'b10; // this is the shift amount
                  PrepareFetch;
               end

               // srl
               6'b000_010: begin
                  aluOp = `SRL;
                  aluSelA = 2'b10; // this is the shift amount
                  PrepareFetch;
               end

               // sllv
               6'b000_100: begin
                  aluOp = `SLL;
                  PrepareFetch;
               end

               // srl
               6'b000_110: begin
                  aluOp = `SRL;
                  PrepareFetch;
               end



            endcase

         end

         EX_ALU_I: begin
            MemtoReg = 0;
            aluSelA = 2'b01;
            aluSelB = 3'b010;
            RegDst = 2'b00;
            RFwrt = 1;

            case(IR[31:26])
               6'b001_000, 6'b001_001: begin // addi(u)
                  aluOp = `ADD;
                  SgnExt = 1;
               end
               6'b001_010: begin // slti
                  aluOp = `SLT;
                  SgnExt = 1;
               end
               6'b001_011: begin // sltiu
                  aluOp = `SLTU;
                  SgnExt = 1;
               end
               6'b001_100: begin // andi
                  aluOp = `AND;
                  SgnExt = 0;
               end
               6'b001_101: begin // ori
                  aluOp = `OR;
                  SgnExt = 0;
               end
               6'b001_110: begin // xori
                  aluOp = `XOR;
                  SgnExt = 0;
               end
               6'b001_111: begin  // lui
                  aluOp = `LUI;
                  SgnExt = 0;
               end
            endcase

            PrepareFetch;
         end

         EX_LW_1: begin
            aluOp = `ADD;
            aluSelA = 2'b01;
            aluSelB = 3'b010;
            SgnExt = 1;
            MARwrt = 1;
            MARscr = 2'b01;
            setMRE = 1;
            nxt_state = EX_LW_2;
         end

         EX_LW_2: begin
            nxt_state = EX_LW_3;
         end

         EX_LW_3: begin
            nxt_state = EX_LW_4;
         end

         EX_LW_4: begin
            MDRwrt = 1;
            nxt_state = EX_LW_5;
         end

         EX_LW_5: begin
            RegDst = 2'b00;
            MemtoReg = 1;
            RFwrt = 1;
            PrepareFetch;
         end


         EX_SW_1: begin
            MARwrt = 1;
            MARscr = 2'b01;
            aluSelA = 2'b01;
            aluSelB = 3'b010;
            aluOp = `ADD;
            setMWE = 1;
            nxt_state = EX_SW_2;
         end

         EX_SW_2: begin
            clrMWE = 1;
            nxt_state = EX_SW_3;
         end

         EX_SW_3: begin
            PrepareFetch;
         end

         EX_BRA_1: begin
            aluOp = `XOR;
            aluSelA = 2'b01; aluSelB = 3'b000;
            case(IR[31:26])
               6'b000_100:  //beq
               begin
                  if(aluZero)
                     nxt_state = EX_BRA_2;
                  else
                     PrepareFetch;
               end

               6'b000_101:  //bne
               begin
                  if(aluZero)
                     PrepareFetch;
                  else
                     nxt_state = EX_BRA_2;
               end
            endcase
         end

         EX_BRA_2: begin
            aluOp = `ADD;
            PCwrt = 1;
            PCsrc = 2'b00;
            SgnExt = 1;
            aluSelA = 2'b00; aluSelB = 3'b011;
            MARscr = 2'b01;
            setMRE = 1;
            MARwrt = 1;
            nxt_state = FETCH1;
         end

         EX_mult: begin
            multStart = 0;
            if(multReady) begin
                  {hiReg, loReg} = multResult;
                  PrepareFetch;
            end
            else begin
               nxt_state = EX_mult;
            end
         end

      endcase

   end

endmodule

//==============================================================================

module my_alu(
   input wire  [3:0] Op,
   input wire  [31:0] A,
   input wire  [31:0] B,
   output wire [31:0] X,
   output wire        Z,
   output wire [31:0] hiReg,
   output wire [31:0] loReg
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
   reg [31:0] quo;
   reg [31:0] rem;

   always @( * ) begin
      case( Op )
         `ADD : x = sum;
         `SUB : x = sum;
         `SLT : x = slt;
         `SLTU: x = sltu;
         `AND : x =   A & B;
         `OR  : x =   A | B;
         `NOR : x = ~(A | B);
         `XOR : x =   A ^ B;
         `LUI : x = {B[15:0], 16'h0};
         `SLL : x = B << A;
         `SRL : x = B >> A;
         `DIVU : begin
            quo = $unsigned(A) / $unsigned(B);
            rem = $unsigned(A) % $unsigned(B);
         end
         default : x = 32'h0;
      endcase
   end

   assign #2 X = x;
   assign #2 Z = x == 32'h00000000;
   assign loReg = quo;
   assign hiReg = rem;

endmodule

//==============================================================================

module reg_file(
   input  wire clk,
   input  wire write,
   input  wire [4:0] WR,
   input  wire [31:0] WD,
   input  wire [4:0] RR1,
   input  wire [4:0] RR2,
   output wire [31:0] RD1,
   output wire [31:0] RD2
);

   reg [31:0] rf_data [0:31];

   assign #2 RD1 = rf_data[ RR1 ];
   assign #2 RD2 = rf_data[ RR2 ];   

   always @( posedge clk ) begin
      if ( write )
         rf_data[ WR ] <= WD;

      rf_data[0] <= 32'h00000000;
   end

endmodule

//=============================================================================


module booth_signed_mult
#(
 parameter n,
 parameter final_n = 2*((n+1)/2)
)
(
//-----------------------Port directions and deceleration
   input wire clk,
   input wire start,
   input wire [n-1:0] A,
   input wire [n-1:0] B,
   output reg [2*final_n-1:0] Product,
   output wire ready
   );
//------------------------------------------------------

//----------------------------------- register deceleration
reg [$clog2(final_n)-1:0] counter;
reg [final_n-1:0] Multiplicand;
reg last_shifted_bit;
reg [final_n:0] neg_multiplicand;
//-------------------------------------------------------

//-------------------------------------- combinational logic
assign ready = counter == final_n>>1;
//---------------------------------------------------------

//--------------------------------------- sequential Logic
always @ (posedge clk) begin

   if(start) begin
      last_shifted_bit = 0;
      counter <= 4'h0;
      Multiplicand <= n == final_n ? A : {A[n-1], A};
      neg_multiplicand <= n == final_n ? ~{ A[n-1], A} + 1'b1 : ~{ {2{A[n-1]}} , A} + 1'b1;
      Product <= n == final_n ? {{n{1'b0}}, B} : {{final_n{1'b0}}, B[n - 1], B};
   end
   
   else if(!ready) begin
      case ({Product[1:0], last_shifted_bit})
         3'b000, 3'b111:
            // Just sign-extending
            Product <= { {2{Product[2*final_n-1]}},  Product[2*final_n-1:2] };

         3'b001, 3'b010:
            // Multiplicand + the first n bits
            Product <= { { {2{Multiplicand[final_n-1]}}, Multiplicand} + { {2{Product[2*final_n-1]}}, Product[2*final_n-1:final_n]},
                        Product[final_n-1:2]}; //n+2 -bit + n-2 -bit

         3'b110, 3'b101:
            // neg_multiplicand + the first n bits
            Product <= { {neg_multiplicand[final_n], neg_multiplicand} + { {2{Product[2*final_n-1]}}, Product[2*final_n-1:final_n]},
                        Product[final_n-1:2]}; //n+2 -bit + n-2 -bit

         3'b011:
            // 2 * Multiplicand + the first 8 bits
            Product <= { {Multiplicand[final_n-1], Multiplicand, 1'b0} + { {2{Product[2*final_n-1]}}, Product[2*final_n-1:final_n]},
                        Product[final_n-1:2]}; //n+2 -bit + n-2 -bit
         
         3'b100:
            // 2 * neg_multiplicand + the first 8 bits
            Product <= { {neg_multiplicand, 1'b0} + { {2{Product[2*final_n-1]}}, Product[2*final_n-1:final_n]},
                        Product[final_n-1:2]}; //n+2 -bit + n-2 -bit

      endcase
      last_shifted_bit <= Product[1];

      counter <= counter + 1;
   end
end

endmodule