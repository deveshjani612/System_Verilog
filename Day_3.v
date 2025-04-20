// Declare 3-bit wide bit vectors for selection, control, and flag signals
bit [2:0] sel, ctrl, flag;

// Define a covergroup triggered on the positive edge of 'clk'
covergroup cov1 @(posedge clk);

  // Define a coverpoint that captures the sum of 'ctrl' and 'flag'
  // This can help monitor behavior influenced by the combination of control and flag values
  CP_ctrlflag: coverpoint ctrl + flag;

  // Define a cross coverage between 'sel' and the 'CP_ctrlflag' coverpoint
  // This checks how combinations of 'sel' values interact with the result of ctrl + flag
  CP_cross: cross sel, CP_ctrlflag;

endgroup


// Declare a 16-bit wide opcode and a 4-bit wide status signal
bit [15:0] opcode;
bit [3:0] status;

// Define another covergroup triggered on the positive edge of 'clk'
covergroup cov2 @(posedge clk);

  // Coverpoint on 'opcode' capturing values in the range 0 to 99
  // 'bins valid[]' creates automatic bins for each value in the specified range
  CP_opcode: coverpoint opcode { bins valid[] = {[0:99]}; }

  // Cross coverage between 'status' and the opcode coverpoint
  // Useful for verifying how different statuses occur with various opcode values
  CP_cross: cross status, CP_opcode;

endgroup
