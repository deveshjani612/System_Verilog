// Solution one ( Looped Instruction Stimulus )

// Define enumerations for opcode and register
typedef enum bit[2:0] {ADDI, SUBI, ANDI, XORI, JMP, JMPC, CALL} opcode_t;
typedef enum bit[1:0] {REG0, REG1, REG2, REG3} reg_t;

// Declare variables
opcode_t opcode;
reg_t    reg;
logic [7:0] data;

logic clk;

// DUT interface signals
logic [15:0] instr;

// Clock generation
initial clk = 0;
always #5 clk = ~clk;

// Function to assemble the 16-bit instruction
function automatic logic [15:0] pack_instruction(opcode_t opc, reg_t r, logic [7:0] d);
  return {opc, r, d};
endfunction

// DUT instantiation (placeholder)
// DUT dut (.instr(instr), .clk(clk)); // Uncomment and connect as per your DUT

// Stimulus generation process
initial begin
  $display("Starting Looped Instruction Generation...");

  // Loop through all opcodes
  foreach (opcode_t'(i)) begin
    opcode = opcode_t'(i);
    
    // Loop through all registers
    foreach (reg_t'(j)) begin
      reg = reg_t'(j);
      
      // Loop through all data values
      for (int k = 0; k < 256; k++) begin
        data = logic'(k);

        // Apply stimulus at posedge
        @(posedge clk);
        instr = pack_instruction(opcode, reg, data);

        // Optional: display stimulus
        $display("Opcode: %s, Reg: %s, Data: %0d --> Instr: %h", opcode.name(), reg.name(), data, instr);
      end
    end
  end

  $display("Completed all instruction combinations.");
  $finish;
end

// Solution two


// Define enumerations for opcode and register
typedef enum bit[2:0] {ADDI, SUBI, ANDI, XORI, JMP, JMPC, CALL} opcode_t;
typedef enum bit[1:0] {REG0, REG1, REG2, REG3} reg_t;

// Instruction class with constraints
class instr_seq;
  rand opcode_t   opcode;
  rand reg_t      reg;
  rand logic [7:0] data;

  // Constraint: CALL should not use REG3
  constraint call_c {
    if (opcode == CALL) reg != REG3;
  }

  // Constraint: ADDI and SUBI should use only REG0 or REG1
  constraint arith_reg_c {
    if (opcode == ADDI || opcode == SUBI)
      reg inside {REG0, REG1};
  }

  // Constraint: XORI data should be a power of 2
  constraint xori_data_c {
    if (opcode == XORI)
      data inside {8'b00000001, 8'b00000010, 8'b00000100, 8'b00001000};
  }
endclass

// Function to assemble the 16-bit instruction
function automatic logic [15:0] pack_instruction(opcode_t opc, reg_t r, logic [7:0] d);
  return {opc, r, d};
endfunction

// DUT interface signals
logic [15:0] instr;
logic clk;

// Clock generation
initial clk = 0;
always #5 clk = ~clk;

// DUT instantiation (placeholder)
// DUT dut (.instr(instr), .clk(clk)); // Uncomment and connect as per your DUT

// Stimulus generation process
initial begin
  instr_seq instr_obj = new();

  $display("Starting Constrained Random Instruction Generation...");

  repeat (1000) begin
    if (instr_obj.randomize()) begin
      @(posedge clk);
      instr = pack_instruction(instr_obj.opcode, instr_obj.reg, instr_obj.data);

      // Optional: display stimulus
      $display("Opcode: %s, Reg: %s, Data: %0d --> Instr: %h",
               instr_obj.opcode.name(), instr_obj.reg.name(), instr_obj.data, instr);
    end else begin
      $display("Randomization failed.");
    end
  end

  $display("Completed constrained random instruction generation.");
  $finish;
end
