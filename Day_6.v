// Define a sequence that specifies timing between read_req, ready, and ack signals
sequence read_ready_ack_seq;
    // After read_req, ready should be asserted within 0 to 5 cycles,
    // and ack should be asserted within 1 to 5 cycles after ready
    read_req ##[0:5] ready ##[1:5] ack;
endsequence

// Define a property that checks if the above sequence follows a read request
property p_read_ready_ack;
    @(posedge clk)
    disable iff (!reset_n) // Disable assertion check when reset_n is low
    read_req |-> read_ready_ack_seq; // Implication: if read_req, then sequence must follow
endproperty

// Assert the property
assert property (p_read_ready_ack);
