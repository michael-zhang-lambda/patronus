module Constraint(input clk, input [3:0] a);
    reg [3:0] x = 4'h0;

    always @(posedge clk) begin
        x <= x + a;
    end

    always @(*) begin
        // constraint over an input only
        assume (a < 4'h3);
        // constraint mixing state and input: the accumulator never wraps around
        assume (x <= x + a);
        assert (x != 4'hf);
    end
endmodule
