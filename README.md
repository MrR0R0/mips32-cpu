# Single-Cycle & Multi-Cycle MIPS32 CPU

**Author:** M.M. Roshani   
**Course:** Computer Architecture   
**Instructor:** Mohammad-Reza Movahedin   

## Overview
This repository contains an educational implementation of a **MIPS32 CPU** in Verilog/SystemVerilog. Both **single-cycle** and **multi-cycle** designs are included.

### Implemented Instructions
- **R-format:** `add(u)`, `sub(u)`, `and`, `or`, `xor`, `nor`, `slt`, `sltu`  
- **I-format:** `beq`, `bne`, `lw`, `sw`, `addi(u)`, `slti`, `sltiu`, `andi`, `ori`, `xori`, `lui`  
- **Additional:** `sll`, `srl`, `multu`, `divu` in multi-cycle design  

### Features
- Single-cycle and multi-cycle CPU datapaths  
- Parameterized ALU supporting all required operations  
- Register file with 32 registers (`x0` hardwired to 0)  
- Instruction and data memory modules (`async_mem`)  
- Multi-cycle controller with fetch/decode/execute states  
- Booth multiplier for multi-cycle multiply instructions  
- Testbenches for simulation
