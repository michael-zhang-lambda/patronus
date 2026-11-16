module Compare(input clk, input [3:0] a, input [3:0] b);
    // Exercises unsigned and signed comparisons
    wire signed [3:0] sa = a;
    wire signed [3:0] sb = b;

    reg [5:0] ucmp = 6'h0;  // {==, !=, <, <=, >, >=} unsigned
    reg [3:0] scmp = 4'h0;  // {<, <=, >, >=} signed

    always @(posedge clk) begin
        ucmp <= {a == b, a != b, a < b, a <= b, a > b, a >= b};
        scmp <= {sa < sb, sa <= sb, sa > sb, sa >= sb};
    end

    // Bad state: signed and unsigned order disagree while both operands are non-negative
    always @(*) begin
        assert (a[3] || b[3] || ((a < b) == (sa < sb)));
    end
endmodule
