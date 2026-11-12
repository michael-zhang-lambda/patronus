module Accumulate(input clk, input en, input [3:0] d);
    reg [3:0] x = 4'h0;
    reg [3:0] y = 4'h0;

    always @(posedge clk) begin
        // When enabled, add input data to both accumulators
        if (en) begin
            x <= x + d;
            y <= y + d;
        end
    end

    // Bad state: accumulators differ
    always @(*) begin
        assert (x == y);
    end
endmodule
