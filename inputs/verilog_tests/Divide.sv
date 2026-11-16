module Divide(input clk, input [3:0] a, input [3:0] b);
    // Exercises udiv, urem, sdiv, srem (including division by zero)
    wire signed [3:0] sa = a;
    wire signed [3:0] sb = b;

    reg [3:0] r_udiv = 4'h0;
    reg [3:0] r_urem = 4'h0;
    reg [3:0] r_sdiv = 4'h0;
    reg [3:0] r_srem = 4'h0;

    always @(posedge clk) begin
        r_udiv <= a / b;
        r_urem <= a % b;
        r_sdiv <= sa / sb;
        r_srem <= sa % sb;
    end

    // Bad state: a != (a / b) * b + (a % b) (never fires, also for b == 0)
    always @(*) begin
        assert ((a / b) * b + (a % b) == a);
    end
endmodule
