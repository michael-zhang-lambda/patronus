module Bitwise(input clk, input [3:0] a, input [3:0] b);
    // Exercises and, or, xor, not, nand, nor, xnor and the reductions
    reg [3:0] r_and  = 4'h0;
    reg [3:0] r_or   = 4'h0;
    reg [3:0] r_xor  = 4'h0;
    reg [3:0] r_not  = 4'h0;
    reg [3:0] r_nand = 4'h0;
    reg [3:0] r_nor  = 4'h0;
    reg [3:0] r_xnor = 4'h0;
    reg [2:0] r_red  = 3'h0;   // {&a, |a, ^a}

    always @(posedge clk) begin
        r_and  <= a & b;
        r_or   <= a | b;
        r_xor  <= a ^ b;
        r_not  <= ~a;
        r_nand <= ~(a & b);
        r_nor  <= ~(a | b);
        r_xnor <= a ~^ b;
        r_red  <= {&a, |a, ^a};
    end

    // Bad state: De Morgan violated (never fires)
    always @(*) begin
        assert (r_nand == (~a | ~b) || r_nand != ~(a & b));
    end
endmodule
