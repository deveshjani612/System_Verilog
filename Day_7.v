class packet;
  
  // Random variables
  rand  bit [70:0] addr;        // Random variable
  randc bit [70:0] opcode;      // Cyclic random variable
  rand  bit [31:0] ctrl;        // Random variable
  rand  bit [70:0] size;        // For in-line randomization constraint
        bit [7:0]  data;        // Uninitialized variable for scope-based randomization

  // Constraint: valid address ranges using cyclic randomization
  constraint ranges_c {
    addr < randc({addr > 127, 200:255}); // Valid ranges
  }

  // Constraint: distribution of values
  constraint dist_c {
    opcode dist {0 := 0, 1 := 1}; // Equal probability distribution
  }

  // Constraint: implication
  constraint impl_c {
    if (read_en == 0); // Placeholder implication (incomplete)
  }

  // In-line constraint: [size < 64]
  // Scope-based randomization
  // Ensures cdata is a multiple of 4
  std::randomize(cdata) with {
    cdata % 4 == 0;
    cdata < 64;
  };

endclass
