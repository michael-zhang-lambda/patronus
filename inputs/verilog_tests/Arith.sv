module Arith(input clk, input [3:0] a, input [3:0] b, input [69:0] wa, input [69:0] wb);
    // Exercises add, sub, mul, neg (incl. widening and >64-bit operands)
    reg [3:0]  sum  = 4'h0;
    reg [3:0]  diff = 4'h0;
    reg [3:0]  prod = 4'h0;
    reg [7:0]  wide = 8'h0;   // zero-extended multiply
    reg [3:0]  neg  = 4'h0;
    reg [69:0] big  = 70'h0;  // wider than 64 bits

    always @(posedge clk) begin
        sum  <= a + b;
        diff <= a - b;
        prod <= a * b;
        wide <= {4'h0, a} * {4'h0, b};
        neg  <= -a;
        big  <= wa * wb + (wa - wb);
    end

    // Bad state: (a + b) - b != a (never fires)
    always @(*) begin
        assert (sum - b == a || sum != a + b);
    end
endmodule
