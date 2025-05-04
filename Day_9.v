//Design: Simple FIFO

module fifo (
    input logic clk,
    input logic rst_n,
    input logic wr_en,
    input logic rd_en,
    input logic [7:0] data_in,
    output logic [7:0] data_out,
    output logic full,
    output logic empty
);

    logic [7:0] mem [3:0];
    logic [1:0] wr_ptr, rd_ptr;
    logic [2:0] count;

    assign full  = (count == 4);
    assign empty = (count == 0);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wr_ptr <= 0;
            rd_ptr <= 0;
            count  <= 0;
        end else begin
            if (wr_en && !full) begin
                mem[wr_ptr] <= data_in;
                wr_ptr <= wr_ptr + 1;
                count <= count + 1;
            end
            if (rd_en && !empty) begin
                data_out <= mem[rd_ptr];
                rd_ptr <= rd_ptr + 1;
                count <= count - 1;
            end
        end
    end
endmodule

//Assertions for the FIFO
module fifo_assertions (
    input logic clk,
    input logic rst_n,
    input logic wr_en,
    input logic rd_en,
    input logic full,
    input logic empty
);

    // 1. Interface Assertion: FIFO must not accept a write when full
    property no_write_when_full;
        @(posedge clk) disable iff (!rst_n)
            wr_en && full |-> $error("Write attempted when FIFO is full");
    endproperty
    assert property(no_write_when_full);

    // 2. Interface Assertion: FIFO must not read when empty
    property no_read_when_empty;
        @(posedge clk) disable iff (!rst_n)
            rd_en && empty |-> $error("Read attempted when FIFO is empty");
    endproperty
    assert property(no_read_when_empty);

    // 3. Functional Assertion: If FIFO is full, count must be 4
    property full_means_count4(logic [2:0] count);
        @(posedge clk) disable iff (!rst_n)
            full |-> (count == 4);
    endproperty
    // Example usage - bind this to actual count
    // assert property(full_means_count4(count));

endmodule


//Binding Assertions to the FIFO Instance
module tb_top;
    logic clk = 0, rst_n;
    logic wr_en, rd_en;
    logic [7:0] data_in, data_out;
    logic full, empty;

    fifo dut (
        .clk(clk), .rst_n(rst_n),
        .wr_en(wr_en), .rd_en(rd_en),
        .data_in(data_in), .data_out(data_out),
        .full(full), .empty(empty)
    );

    fifo_assertions assert_blk (
        .clk(clk), .rst_n(rst_n),
        .wr_en(wr_en), .rd_en(rd_en),
        .full(full), .empty(empty)
    );

    // Clock generator
    always #5 clk = ~clk;

    initial begin
        rst_n = 0;
        #10 rst_n = 1;
        // Drive some stimulus here
        wr_en = 1;
        rd_en = 0;
        data_in = 8'hAA;
        #10 wr_en = 0;
        #10 rd_en = 1;
        #10 rd_en = 0;
        #100 $finish;
    end
endmodule
