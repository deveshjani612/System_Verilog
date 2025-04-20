// SystemVerilog Clocking Block Example for UVM/ASIC Verification

// Define an interface for I2C signals with a clock input
interface i2c_if(input logic clk);
    logic sda, scl, data;

    // Define a clocking block with skew for stable sampling
    clocking cb @(posedge clk);
        default input #1ns output #2ns; // Input sampled 1ns after posedge, output driven 2ns after posedge
        input  sda, scl;               // Input signals for sampling
        output data;                   // Output signal for driving
    endclocking

    // Define modports for driver and monitor access
    modport drv (input cb.sda, cb.scl, output cb.data); // Driver can read sda/scl and drive data
    modport mon (input cb.sda, cb.scl, data);           // Monitor can only observe all signals
endinterface


// In UVM Driver — driving signals using the clocking block
task drive_signal(virtual i2c_if vif);
    @(vif.cb);             // Wait for the clocking block event (posedge clk + skew)
    vif.cb.data <= 1'b1;   // Drive value through clocking block output
endtask
