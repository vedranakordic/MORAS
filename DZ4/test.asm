// function fibonacci 4
(fib.fibonacci)
@SP
M=M+1
A=M-1
M=0
@SP
M=M+1
A=M-1
M=0
@SP
M=M+1
A=M-1
M=0
@SP
M=M+1
A=M-1
M=0
// push constant 0
@0
D=A
@SP
M=M+1
A=M-1
M=D
// pop local 0
@0
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push constant 1
@1
D=A
@SP
M=M+1
A=M-1
M=D
// pop local 1
@1
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push constant 2
@2
D=A
@SP
M=M+1
A=M-1
M=D
// pop local 3
@3
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push constant 0
@0
D=A
@SP
M=M+1
A=M-1
M=D
// eq
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB0
D;JEQ
@LAB1
D=0;JMP
(LAB0)
D=-1
(LAB1)
@SP
A=M-1
M=D
// if-goto IF_TRUE0
@fib.fibonacci$IF_TRUE0
0;JMP
// goto IF_FALSE0
@fib.fibonacci$IF_FALSE0
0;JMP
// label IF_TRUE0
(fib.fibonacci$IF_TRUE0)
// push local 0
@0
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// return
@LCL
D=M
@R15
M=D
@5
D=A
@R15
A=M-D
D=M
@R14
M=D
@SP
AM=M-1
D=M
@ARG
A=M
M=D
@ARG
D=M+1
@SP
M=D
@R15
AM=M-1
D=M
@THAT
M=D
@R15
AM=M-1
D=M
@THIS
M=D
@R15
AM=M-1
D=M
@ARG
M=D
@R15
AM=M-1
D=M
@LCL
M=D
@R14
A=M
0;JMP
// label IF_FALSE0
(fib.fibonacci$IF_FALSE0)
// label WHILE_EXP0
(fib.fibonacci$WHILE_EXP0)
// push local 3
@3
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// gt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB2
D;JGT
@LAB3
D=0;JMP
(LAB2)
D=-1
(LAB3)
@SP
A=M-1
M=D
// not
@SP
A=M-1
M=!M
// not
@SP
A=M-1
M=!M
// if-goto WHILE_END0
@fib.fibonacci$WHILE_END0
0;JMP
// push local 0
@0
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push local 1
@1
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// add
@SP
AM=M-1
D=M
A=A-1
M=M+D
// pop local 2
@2
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push local 1
@1
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// pop local 0
@0
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push local 2
@2
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// pop local 1
@1
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push local 3
@3
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push constant 1
@1
D=A
@SP
M=M+1
A=M-1
M=D
// add
@SP
AM=M-1
D=M
A=A-1
M=M+D
// pop local 3
@3
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// goto WHILE_EXP0
@fib.fibonacci$WHILE_EXP0
0;JMP
// label WHILE_END0
(fib.fibonacci$WHILE_END0)
// push local 1
@1
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// return
@LCL
D=M
@R15
M=D
@5
D=A
@R15
A=M-D
D=M
@R14
M=D
@SP
AM=M-1
D=M
@ARG
A=M
M=D
@ARG
D=M+1
@SP
M=D
@R15
AM=M-1
D=M
@THAT
M=D
@R15
AM=M-1
D=M
@THIS
M=D
@R15
AM=M-1
D=M
@ARG
M=D
@R15
AM=M-1
D=M
@LCL
M=D
@R14
A=M
0;JMP
// function mid 1
(mid.mid)
@SP
M=M+1
A=M-1
M=0
// push argument 2
@2
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// pop local 0
@0
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB4
D;JLT
@LAB5
D=0;JMP
(LAB4)
D=-1
(LAB5)
@SP
A=M-1
M=D
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 2
@2
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB6
D;JLT
@LAB7
D=0;JMP
(LAB6)
D=-1
(LAB7)
@SP
A=M-1
M=D
// and
@SP
AM=M-1
D=M
A=A-1
M=M&D
// push argument 2
@2
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB8
D;JLT
@LAB9
D=0;JMP
(LAB8)
D=-1
(LAB9)
@SP
A=M-1
M=D
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB10
D;JLT
@LAB11
D=0;JMP
(LAB10)
D=-1
(LAB11)
@SP
A=M-1
M=D
// and
@SP
AM=M-1
D=M
A=A-1
M=M&D
// or
@SP
AM=M-1
D=M
A=A-1
M=M|D
// if-goto IF_TRUE0
@mid.mid$IF_TRUE0
0;JMP
// goto IF_FALSE0
@mid.mid$IF_FALSE0
0;JMP
// label IF_TRUE0
(mid.mid$IF_TRUE0)
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// pop local 0
@0
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// label IF_FALSE0
(mid.mid$IF_FALSE0)
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB12
D;JLT
@LAB13
D=0;JMP
(LAB12)
D=-1
(LAB13)
@SP
A=M-1
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 2
@2
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB14
D;JLT
@LAB15
D=0;JMP
(LAB14)
D=-1
(LAB15)
@SP
A=M-1
M=D
// and
@SP
AM=M-1
D=M
A=A-1
M=M&D
// push argument 2
@2
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB16
D;JLT
@LAB17
D=0;JMP
(LAB16)
D=-1
(LAB17)
@SP
A=M-1
M=D
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// push argument 1
@1
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// lt
@SP
AM=M-1
D=M
A=A-1
D=M-D
@LAB18
D;JLT
@LAB19
D=0;JMP
(LAB18)
D=-1
(LAB19)
@SP
A=M-1
M=D
// and
@SP
AM=M-1
D=M
A=A-1
M=M&D
// or
@SP
AM=M-1
D=M
A=A-1
M=M|D
// if-goto IF_TRUE1
@mid.mid$IF_TRUE1
0;JMP
// goto IF_FALSE1
@mid.mid$IF_FALSE1
0;JMP
// label IF_TRUE1
(mid.mid$IF_TRUE1)
// push argument 0
@0
D=A
@ARG
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// pop local 0
@0
D=A
@LCL
D=M+D
@R15
M=D
@SP
AM=M-1
D=M
@R15
A=M
M=D
// label IF_FALSE1
(mid.mid$IF_FALSE1)
// push local 0
@0
D=A
@LCL
A=D+M
D=M
@SP
M=M+1
A=M-1
M=D
// return
@LCL
D=M
@R15
M=D
@5
D=A
@R15
A=M-D
D=M
@R14
M=D
@SP
AM=M-1
D=M
@ARG
A=M
M=D
@ARG
D=M+1
@SP
M=D
@R15
AM=M-1
D=M
@THAT
M=D
@R15
AM=M-1
D=M
@THIS
M=D
@R15
AM=M-1
D=M
@ARG
M=D
@R15
AM=M-1
D=M
@LCL
M=D
@R14
A=M
0;JMP
