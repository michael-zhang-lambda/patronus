module Memory(input clk, input we, input [1:0] wa, input [3:0] wd);
    // Uninitialized memory: initial contents are chosen by the oracle
    reg [3:0] mem [0:3];

    // Shadow copy of the most recent write
    reg       valid = 1'b0;
    reg [1:0] last_addr = 2'h0;
    reg [3:0] last_data = 4'h0;

    always @(posedge clk) begin
        if (we) begin
            mem[wa] <= wd;
            valid <= 1'b1;
            last_addr <= wa;
            last_data <= wd;
        end
    end

    // Bad state: memory disagrees with the most recent write
    always @(*) begin
        assert (!valid || (mem[last_addr] == last_data));
    end
endmodule
