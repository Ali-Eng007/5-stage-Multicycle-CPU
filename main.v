`timescale 1ns/1ps
module tb_computer();

  reg clk, reset;
  wire [15:0] data_out_instruction, data_in, data_out, address_data;
  wire MemRead, MemWrite;
  wire [3:0] state;	
  wire [15:0] ALUresult, address_inst; 
  wire [1:0] ALUop;	
  reg [15:0] out;
  wire [15:0] rr;

    
	  
	    // Clock generation
  initial begin
    clk = 0;
    forever #10 clk = ~clk; // Toggle the clock every 7 time units
  end

  initial begin
	  
	clk = 1;
    reset = 1;
	#1ns
	reset = 0;
	#1ns
	reset = 1;
	
$monitor("At time %t, address_inst = %h, data_out_instruction = %h, data_in = %h, data_out = %h, address_data = %h, MemRead = %b, MemWrite = %b, state = %h, ALUresult = %h, ALUop = %b",
             $time, address_inst, data_out_instruction, data_in, data_out, address_data, MemRead, MemWrite, state, ALUresult, ALUop);
    #8000ns $finish;
  end

  computer dut (
  
    .clk(clk),
    .address_inst(address_inst),
    .data_out_instruction(data_out_instruction),
    .data_in(data_in),
    .data_out(data_out),
    .address_data(address_data),
    .MemRead(MemRead),
    .MemWrite(MemWrite),
	.reset(reset),
	.state(state),
	.ALUresult(ALUresult),
	.ALUop(ALUop)
  );
  
endmodule 









 module instructionMemory #(
    parameter WIDTH = 16
) (
    output reg [15:0] data,        
    input clk,                     
    input [WIDTH-1:0] address     
);

    reg [7:0] mem [0: 32'hEFFF];  

    initial begin 
        $readmemh("instruction.txt", mem, 0, 32'hEFFF);
    end

    always @(address) begin
        data = {mem[address + 1], mem[address]};
    end

endmodule


//register file 
module reg_file (
	
	input clk,
	input regW, 
  input [2:0] regDst,
  input [2:0] regSrcA, regSrcB,
  input [15:0] BusW, 
  output reg [15:0] BusA, BusB
);
	
  reg [15:0] regArray [0:7] ;
  initial begin
    regArray[0] = 16'h0000;
    regArray[1] = 16'h50;
    regArray[2] = 2;
    regArray[3] = 78;
    regArray[4] = 16'h0011;
    regArray[5] = 80;
    regArray[6] = 16'h50;
    regArray[7] = 16'h1011;


    end
  
  
	always @(*) begin //The output is taken asynchronously										  
      BusA = regArray[regSrcA];
      BusB = regArray[regSrcB];	
	end
	
  always @(posedge clk) begin
    if (regW) begin
      if (regDst != 0) begin  // Prevent writing to register 0
        regArray[regDst] <= BusW;
      end
    end
  end
	
endmodule



module mux2x1 #(
	parameter WIDTH = 16
) 	 

   (input [WIDTH-1:0] a, b,     
    input select,  
    output [WIDTH-1:0] out    
);


	assign out = select ? b : a;

endmodule 




//datapath
module datapath ( 
	
	input RegWrite, IRwrite, Pcwrite,
		  ExtOp , clk, reset, MemData, Mdr_signal ,

		  
		  
  input [15:0] data_out_instruction, data_out,
					  
  input [1:0] ALUsrcA, ALUsrcB,  RegSrcA,RegSrcB, RegDst, RegValue ,
				PCsrc, ALUop,
	
  output [3:0] opcode, 
	output  mode,
  output [15:0] address_data, address_instruction, data_in,
	output z, n, v,
  output [15:0] ALU_result
);

  wire [2:0] Rs1, Rs2, Rd, Rd_R,Rs1_R, Rs2_R, Rd_I, Rs1_I, Rs_S ; 
  wire [15:0] pc_temp , pc_adder , data_out_mdr;
	
	assign pc_temp = address_instruction;
	
  wire [15:0] instruction, BUSA, BUSB, B_operand, A_operand, 
				increment, extended_immediate, extended_immediate_S,ALU_operand1, ALU_operand2,  
				jumpTargetAddress, PCtype, ALU_result_buffer , data_out_Lwb;
	
  wire[15:0] MDR_out, Register_result ;
    wire [4:0] immediate;
  wire [8:0] immediate_S;
	
  


  assign opcode = instruction[15:12];
  assign mode = instruction[11];
  assign Rd_R = instruction[11:9];
  assign Rs1_R = instruction[8:6];
  assign Rs2_R = instruction[5:3];
  
  
  assign Rd_I = instruction[10:8];
  assign Rs1_I = instruction[7:5];

	
  assign immediate = instruction[4:0];
  
  
  assign jumpTargetAddress={address_instruction[15:12], instruction[11:0]}; 
  
  assign Rs_S = instruction[11:9];
  assign immediate_S = instruction[8:0];
  
  assign pc_adder = pc_temp + 4;


	
	flop IR (.out(instruction), .clk(clk), .writeEn(IRwrite), .in(data_out_instruction), .reset(1'b1));
	
  flop A (.out(A_operand), .clk(clk), .writeEn(1'b1), .in(BUSA), .reset(1'b1));
	
  flop B (.out(B_operand), .clk(clk), .writeEn(1'b1), .in(BUSB), .reset(1'b1)); 
  
  	flop ALUout(.in(ALU_result), .clk(clk), .writeEn(1'b1), .out(ALU_result_buffer), .reset(1'b1));
	
	
	flop MDR(.out(MDR_out), .clk(clk), .writeEn(1'b1), .in(data_out_mdr), .reset(1'b1));
	
  flop pc(.out(address_instruction) , .clk(clk), .writeEn(Pcwrite), .in(PCtype) , .reset(reset));

	


	
  mux4x1 #3 Rd_mux (.a(Rd_I), .b(Rd_R), .c(3'b111), .d(3'b0), .s(RegDst), .out(Rd));
  mux4x1 #3 Rs2_mux (.a(Rs1_I), .b(Rs2_R), .c(Rd_R), .d(Rd_I), .s(RegSrcB), .out(Rs2));
  mux4x1 #3 Rs1_mux (.a(3'b111), .b(Rs1_R), .c(Rs1_I), .d(Rd_I), .s(RegSrcA), .out(Rs1));


  
	reg_file file (
	
		.clk(clk),
		.regW(RegWrite),
      .regDst(Rd), .regSrcA(Rs1),
		.regSrcB(Rs2),
		.BusW(Register_result),
      .BusA(BUSA), .BusB(BUSB)
	);


  
	
  
  mux4x1 ALUsrc1_mux (.a(pc_temp), .b(A_operand), .c(16'b0), .d(16'b0), .s(ALUsrcA), .out(ALU_operand1));
	
  mux4x1 ALUsrc2_mux (.a(B_operand), .b(extended_immediate), .c(16'b10), .d(16'b0), .s(ALUsrcB), .out(ALU_operand2));
  
  
	ALU alu(
	
		.ALUop(ALUop), 
		.a(ALU_operand1), 
		.b(ALU_operand2),
		.zero(z), 
      .overflow(v),  
		.negative(n),
		.result(ALU_result) 
	);
  
  


  
  assign address_data = ALU_result_buffer;
  

  
  mux4x1 pcMux(.a(jumpTargetAddress), .b(ALU_result), .c(ALU_result_buffer), .d(16'b0) ,.s(PCsrc), .out(PCtype));
  
  mux4x1 #16 RegRes(.a(pc_adder), .b(ALU_result_buffer), .c(MDR_out), .d(address_instruction), .s(RegValue), .out(Register_result));
	
	
  mux2x1 dataIn(.a(extended_immediate_S), .b(B_operand), .select(MemData), .out(data_in));
  mux2x1 Mdr(.a(data_out), .b(data_out_Lwb), .select(Mdr_signal), .out(data_out_mdr));

	
	
  extender ext(.in(immediate), .sign_ext(ExtOp), .out(extended_immediate));	
  extender #8 ext1(.in(immediate_S), .sign_ext(ExtOp), .out(extended_immediate_S));	
  extender #8 ext2(.in(data_out[7:0]), .sign_ext(ExtOp), .out(data_out_Lwb));	

  

endmodule




//flop

module flop (  
	
  output reg [15:0] out,
	input clk,
	input writeEn,
  input [15:0] in,
	input reset
);
	always @(posedge clk or negedge reset) begin
	
		if (!reset)
			out <= 0;
		
		else if (writeEn)
			out <= in; 
	end
	
endmodule




//mux4x1
module mux4x1  #(
	parameter WIDTH = 16
) 
	
	(input [WIDTH-1:0] a, b, c, d,  	 
	input [1:0] s,	 
	
	output reg [WIDTH-1:0] out
);
	
	
	always @* begin 
	
		case (s) 
			2'b00 : out = a;
			2'b01 : out = b;
			2'b10 : out = c;
			2'b11 : out = d;
		endcase
end


endmodule


//Alu 
module ALU (
	
    input [1:0] ALUop, 
    input signed [15:0] a,
    input signed[15:0] b,
    output zero, overflow, negative,
    output reg signed [15:0] result 
);

	reg [1:0] carry;

    assign zero = (result == 0);
    assign negative = result[15];
    assign overflow = carry[1] ^ carry[0];
	
  

  
	always @(*) begin
          
		
		case (ALUop)
			
			2'b00 : result = a & b;
			2'b01 : begin 
              {carry[0], result[14:0]} = a[14:0] + b[14:0];
              {carry[1], result[15]} = a[15] + b[15] + carry[0];	
				end	
				
			2'b10 : result = a - b;
			2'b11 : result = b - a; 
		endcase
	end
endmodule

//data memory
module dataMemory #(
	parameter WIDTH = 256
) 
	
  (output reg [15:0] dataOut,
	input clk,
     input [15:0] address,
     input [15:0] dataIn,
	input MemR, MemW
);
	 
  reg [7:0] mem [0:100];

initial begin 
	mem[80] = 8;
	mem[81] = 44;
	mem[82] = 50;
	mem[83] = -12;
	mem[84] = -20;
	mem[85] = -2;
  mem[88] = 220;
  mem[89] = 13;
    mem[16'h12] = 16'h22;
    mem[16'ha] = 16'hAC0;
end
	
always @(posedge clk) begin
    if (MemW) 
              // Write to memory in little endian format
      mem[address] <= dataIn[7:0]; // Lower byte
      mem[address + 1] <= dataIn[15:8]; // Upper byte
end

always @* begin
    if (MemR)
      // Read from memory in little endian format
      dataOut <= {mem[address + 1], mem[address]};end
endmodule

//pc control



module extender #(
	parameter WIDTH = 5
) 
  ( input [WIDTH - 1:0] in,
  input sign_ext,
  output reg [15:0] out
);

  always @* begin
    if (sign_ext) begin
      if (in[WIDTH - 1])
        out = {11'b11111111111, in}; // Extend with 1s if the sign bit (MSB) is 1
      else
        out = {11'b00000000000, in}; // Extend with 0s if the sign bit (MSB) is 0
    end
    else begin
      // Perform zero extension
      out = {11'b00000000000, in};
    end
  end
  
endmodule





module PCcontrol (

    input [3:0] opcode, 
	input z, v, n,
	input PcWriteUncond,
    input [3:0]state,
	output writeEn , branch_signal
  
);

  parameter BGT = 4'b1000,
            BGTZ =4'b1000,
            BLT = 4'b1001,
            BLTZ =  4'b1001,
            BNE = 4'b1011,
            BNEZ = 4'b1011,
            BEQ = 4'b1010,
            BEQZ = 4'b1010;

			  
	wire branch;

	
      assign branch = ((opcode == BNE) && !z) || 
                      ((opcode == BEQ) && z) || 
                      ((opcode ==BGT) && (!z && !(n ^ v))) || 
                      ((opcode == BLT) && (n ^ v))|| 
                      ((opcode == BNEZ) && !z) || 
                      ((opcode == BEQZ) && z) || 
                      ((opcode ==BGTZ) && (!z && !(n ^ v))) || 
                      ((opcode == BLTZ) && (n ^ v)) ; 

  assign branch_signal = branch;
					
  assign writeEn = ((state == 7) && branch) ||  ((state == 8) && branch) || PcWriteUncond || ((state == 15) && branch);
  

  

endmodule





//Alu Control 
module ALUcontrol (
	
	input [1:0] ALUctrl,
    input [3:0] opcode,
	output reg [1:0] ALUop
); 

parameter  	   
			  AND = 2'b00,
			  ADD = 2'b01,
			  SUB = 2'b10,
			  RSB = 2'b11;
			  

always @* begin 
		case (ALUctrl)
		
			RSB, ADD, SUB : ALUop = ALUctrl; //the operation is generated by the main control
			2'b00 : begin
		case (opcode) //determine the operation based on the opcode 
					4'b0001, 4'b0011 : ALUop = ADD; //opcode = ADDI, ADD (R-TYPE)
					4'b0010 : ALUop = SUB; //opcode = SUB R-TYPE
					4'b0000, 4'b0100 : ALUop = AND; //opcode = AND, ANDI
				endcase
			end
		endcase
	end
	
endmodule




//MAIN CONTROL 

module Maincontrol(
  
  //Signals 1-bit
  
  output reg IRwrite,MemRead,MemWrite,RegWrite,ExtOp,memData, PcWriteUncond, Mdr_signal,
  
  //Signals 2-bit
  
  output reg [1:0] RegSrcA,RegSrcB,RegDest,ALUsrcA,ALUsrcB,PCsrc,regValue,ALUctrl,
  
  output reg [3:0] state,
	
	input clk, reset, 
    input [3:0] opcode,
	input  mode , branch_signal
  
  
);
  
  
parameter     InstructionFetch = 0, 
		  	  InstructionDecode = 1, 
		  	  AddressComputation = 2, 
		  	  LoadAccess = 3, 
		  	  StoreAccess = 4,
			  ALUcomputationR = 5,

		  	  
               AluResultStoreI = 6,
               AluResultStoreR = 11,
               AluResultStoreM = 13, // FOR CALL
               LoadResultStore = 14,
               Branch = 7,
               BranchZero = 8,
               Branch_comp = 15,

			  ALUcomputationI = 9, 
			
			
			
              Call = 10,
			  Return = 12;
				
	parameter AND = 4'b0,
			  ADD = 4'b01,
			  SUB = 4'b10,
			  ADDI= 4'b11,
			  ANDI = 4'b100,
			  LW = 4'b0101,
			  LBu = 4'b0110,
			  LBs = 4'b0110,
			  SW = 4'b0111,
			  BGT = 4'b1000,
			  BGTZ = 4'b1000,
			  BLT = 4'b1001,
			  BLTZ = 4'b1001,
			  BEQ = 4'b1010,
			  BEQZ = 4'b1010,
			  BNE = 4'b1011,
			  BNEZ = 4'b1011,
			  JMP = 4'b1100,
			  CALL= 4'b1101,
  			  RET= 4'b1110,
    		  SV= 4'b1111;
  
  
  always @* begin 
		
		case (opcode) 
			JMP : begin
				
			   jmp = 1;
			end
			
			BGT, BLT,
			BEQ, BNE,
			 SW :  begin 
				jmp = 0;
			end
			
			default : begin 
				jmp = 0;
			end
		endcase
	end

 
  
    reg jmp;
	wire logical; 
  
  assign logical = (opcode == ANDI); 

  
  
  always @(posedge clk or negedge reset) begin
    		PcWriteUncond = 0;

		
    if (!reset)
			state <= InstructionFetch;
		
		else begin
			
		case (state)  
			
			InstructionFetch : state <= InstructionDecode;
			
			InstructionDecode :  begin
              		IRwrite = 1'b0;

				
				case (opcode)
						
					AND, ADD, SUB: state <= ALUcomputationR;   //R-type			  
					LW, SW, LBu,LBs,SV : state <= AddressComputation; //memory access
									
					BEQ, BNE, BGT, BLT : begin 
                      
                      if (!mode) begin

                      state <= Branch; // Normal Branch
                      end
                      else begin
                        state <= BranchZero; // Zero Branch
                      end

                    end
									
					JMP : state <= InstructionFetch; //jmp instruction	
					
                    ANDI, ADDI: state <= ALUcomputationI;  // I-type
					
                      
                  
					CALL : state <= Call;
					RET : state <= Return;
                  
				endcase
			 end

									
		  	AddressComputation : begin
				  
				case (opcode)
					LW,LBu,LBs : state <= LoadAccess; 
					SW,SV : state <= StoreAccess;
				endcase
			end
					
			LoadAccess : begin
              
              state <= LoadResultStore;
				
			end
          
          Branch, BranchZero: state <= Branch_comp;

		  	 StoreAccess, LoadResultStore,
			 AluResultStoreI,AluResultStoreR,
			Branch_comp ,Return, 
			 Call : state <= InstructionFetch;
	
			 ALUcomputationI : state <= AluResultStoreI;
             ALUcomputationR : state <=    AluResultStoreR;
			
		endcase	
		end
	
	end 
  /////////////////
  
  always @(*) begin 
		
		memData = 0;

		RegWrite = 0;
		MemRead = 0;
		MemWrite = 0;
		IRwrite = 1'b0;
		PcWriteUncond = 0;
		ExtOp = 0;
	    Mdr_signal = 0;
		ALUctrl = 0;



			
		case (state) 
			
			InstructionFetch : begin
                
              	IRwrite = 1'b1;
                ALUctrl = 2'b00;
 				ALUsrcA=2'b00;
 				ALUsrcB=2'b10;
  				ALUctrl=2'b01;
                PcWriteUncond = 1'b1;
                PCsrc = 2'b01;



			end
			
		  	InstructionDecode : begin
              PcWriteUncond = jmp ;

              
              case(opcode)
                   AND, ADD, SUB:  begin

                   ExtOp= 1'b0;
                   ALUsrcB = 2'b00;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b01;
                   RegSrcB= 2'b01;
                   RegDest = 2'b01;
                   ALUctrl=2'b00;
                   PCsrc = 2'b01;
                  	RegWrite = 1;
                     		



                     
                   end
                
                ANDI, ADDI : begin
                  
                  if (opcode == ANDI) 
                    begin
                        ExtOp= 1'b0;
                    end
                  else
                    begin 
                      ExtOp= 1'b1;
                    end

                  ALUsrcB = 2'b01;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b10;
                   RegDest = 2'b00;
                   ALUctrl=2'b00;
                   PCsrc = 2'b01;
                   RegWrite = 1;

              
                end
             
                	JMP : begin
                      PCsrc=0;
                      
                      
                       
                      
			     end
			
                BGT, BLT,
                BEQ, BNE :  begin 
                  
                  
                
                   ALUsrcB = 2'b00;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b11;
                   RegSrcB= 2'b00;
                   ALUctrl=2'b10;
                   PCsrc = 2'b10;

                    ExtOp= 1'b1;
                   ALUsrcB = 2'b01;
                   ALUsrcA = 2'b00;
                   ALUctrl=2'b01;
                end

                
                
              LBu :begin
                
                  
                   ALUsrcB = 2'b01;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b10;
                   RegDest = 2'b00;
                   ALUctrl=2'b01;
                   PCsrc = 2'b01;
                  RegWrite = 1;
                  
                
                
              end
                   
               LW :begin
                 
                   ALUsrcB = 2'b01;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b10;
                   RegDest = 2'b00;
                   ALUctrl=2'b01;
                   PCsrc = 2'b01;
                  RegWrite = 1;


              end
                
                 SW: begin
                   
                   ALUsrcA = 2'b01;
                   ALUsrcB = 2'b01;
                   RegSrcA= 2'b10;
                   RegSrcB= 2'b11;
                   ALUctrl=2'b01;
                   PCsrc = 2'b01; 
                   memData= 1'b1;

                end
                
                
               	CALL : begin
		      
                 RegDest = 2'b10;
                  PCsrc = 0;

         
			end
                
                	
			RET : begin
				
				PCsrc = 2'b10;
                ALUsrcA = 2'b01;
                ALUsrcB = 2'b11;
                RegSrcA= 2'b00;
                ALUctrl=2'b01;

				
				
			end
                
              
             SV: begin
                   ALUsrcB = 2'b00;
                   ALUsrcA = 2'b10;
                   RegSrcB= 2'b10;
                   memData = 1'b0;
                   ALUctrl=2'b01;
                   PCsrc = 2'b01;
                   ExtOp = 1'b1;
                   RegDest = 2'b10;

               end
		     
                  
                  endcase
           

			end

		  	AddressComputation : begin
				  
              if (opcode == LBu) begin
                     ExtOp= 0;
              end
              else begin
                   ExtOp= 1;
               end

				ALUctrl = 2'b01;
			
            end
			 
          LoadAccess : begin
            
            if (!mode && opcode == LBu) begin
                Mdr_signal = 1;
                ExtOp = 0;
            end else if (mode && opcode == LBs) begin
                Mdr_signal = 1;
                ExtOp = 1;
            end
            
            if (opcode == LW) begin
            ExtOp = 1 ;
            end
            
            MemRead = 1'b1; MemWrite = 1'b0; end
	 		
          StoreAccess :begin	
              MemWrite = 1'b1;
              MemRead = 1'b0; 
			  memData = 1'b1;
          end

			 
			ALUcomputationR :	begin
				
                ALUctrl = 2'b00;


            end
          

				  
			AluResultStoreI,AluResultStoreR :begin
              RegWrite = 2'b01;
              regValue = 2'b01;

              
            end
          
          LoadResultStore :begin
              RegWrite = 2'b01;
              regValue = 2'b10;

              
            end
           
         
          BranchZero : begin
                             
                   ALUsrcB = 2'b11;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b11;
                   ALUctrl=2'b10;
                   PCsrc = 2'b10;
            
            
          end
        
       
				  
			Branch : begin
			                    
              
                ALUctrl = 2'b00;

              
                   ALUsrcB = 2'b00;
                   ALUsrcA = 2'b01;
                   RegSrcA= 2'b11;
                   RegSrcB= 2'b00;
                   ALUctrl=2'b10;
              
                
              end

              
              Branch_comp: begin
            if (branch_signal) begin
                  	PCsrc = 2'b01;
                   ALUsrcB = 2'b10;
                   ALUsrcA = 2'b00;
                   ALUctrl=2'b10;
                
                
              end

                  		
			end
			  
		
			  
			ALUcomputationI : begin
				  
							  
				ALUctrl = 2'b00;
				ExtOp = !logical;
			end
			
		
			
		Call : begin
		   regValue = 2'b00;   
           RegWrite = 1'b1;
            PcWriteUncond = 1;
			end
          
			
			Return : begin
				
				PCsrc = 2'b10;
                PcWriteUncond = 1;
		
			end
		
		endcase
		
	end

  
endmodule


module CPU (
	
  input [15:0] data_out, data_out_instruction, 
	input clk, reset,
  output [15:0] data_in, address_data,
				address_instruction,
	
	
	output MemWrite, MemRead,
	output [3:0] state,
    output [15:0] ALUresult,
	output [1:0] ALUop
);

  
  wire [3:0] opcode;
	wire  mode ,MemData , PcWriteUncond , PCwrite , Mdr_signal;
	
	wire    RegWrite, IRwrite,   ExtOp;
		   
  wire [1:0] ALUsrcA, ALUsrcB,  RegSrcA,RegSrcB, RegDst,RegValue, branch_signal,
				PCsrc , ALUctrl;
	
	wire z, n, v;


	datapath d1 ( 
	
      .MemData(MemData), .RegDst(RegDst),
      .RegValue(RegValue), .RegSrcA(RegSrcA),  .RegSrcB(RegSrcB),
      .RegWrite(RegWrite), .IRwrite(IRwrite), .Pcwrite(PCwrite),
      .ExtOp(ExtOp) , .clk(clk),
		  
		.data_out_instruction(data_out_instruction), .data_out(data_out),
					  
		.ALUsrcA(ALUsrcA), .ALUsrcB(ALUsrcB),
      .PCsrc(PCsrc), .ALUop(ALUop), .reset(reset), .Mdr_signal(Mdr_signal),
	
		.opcode(opcode), 
		.mode(mode), 
		.address_data(address_data), 
		.address_instruction(address_instruction), .data_in(data_in),
		.z(z), .n(n), .v(v),
		.ALU_result(ALUresult)
	);
	
	
	Maincontrol control(	 
	
		.memData(MemData),
	 	.regValue(RegValue), .RegSrcA(RegSrcA) , .RegSrcB(RegSrcB),
      .RegWrite(RegWrite), .IRwrite(IRwrite), .PcWriteUncond(PcWriteUncond),
      .ExtOp(ExtOp) ,
      .MemWrite(MemWrite), .MemRead(MemRead), . Mdr_signal(Mdr_signal), .branch_signal(branch_signal),
		   
		   
		.ALUsrcA(ALUsrcA), .ALUsrcB(ALUsrcB),
      .PCsrc(PCsrc), .ALUctrl(ALUctrl),  .RegDest(RegDst),
	
		.clk(clk), .opcode(opcode),
		.mode(mode), .reset(reset),
		.state(state)
	);
	
	
	PCcontrol pc_control(

		.opcode(opcode), 
		.z(z), .v(v), .n(n),
        .PcWriteUncond(PcWriteUncond),
		.writeEn(PCwrite), 
      .branch_signal(branch_signal),
		.state(state)
	);
	
	
	ALUcontrol ALU_control(
	
		.ALUop(ALUop),
		.opcode(opcode),
		.ALUctrl(ALUctrl)
	); 	
	
endmodule


module computer (
	
     input clk, reset,
  output [15:0] address_inst, 
  output [15:0] data_out_instruction,
     data_in, data_out, address_data,
  	 output MemRead,
     MemWrite,
	 output [3:0] state,
  output [15:0] ALUresult,
	 output [1:0] ALUop
  );

  
	
	instructionMemory inst_mem(
	
		.data(data_out_instruction), 
		.clk(clk),
		.address(address_inst)					  
	);
	
	dataMemory data_mem(
	
		.dataOut(data_out),
		.clk(clk),
		.address(address_data),
		.dataIn(data_in),
		.MemR(MemRead), 
		.MemW(MemWrite)
	);
	
	
		
  
  CPU cpu(
	
        .data_out(data_out),
        .data_out_instruction(data_out_instruction), 
        .clk(clk),
        .data_in(data_in),
        .address_data(address_data),
        .address_instruction(address_inst),
        .MemWrite(MemWrite),
        .MemRead(MemRead),
		.reset(reset), 
		.state(state),
		.ALUresult(ALUresult),
		.ALUop(ALUop)
    );
	
endmodule