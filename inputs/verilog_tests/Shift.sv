module Shift(input clk, input [7:0] a, input [3:0] sh);
    // Exercises sll, srl, sra, including shift amounts >= the operand width
    wire signed [7:0] sa = a;

    reg [7:0] r_sll = 8'h0;
    reg [7:0] r_srl = 8'h0;
    reg [7:0] r_sra = 8'h0;
    reg [7:0] r_sla = 8'h0;   // <<< is the same as <<

    always @(posedge clk) begin
        r_sll <= a << sh;
        r_srl <= a >> sh;
        r_sra <= sa >>> sh;
        r_sla <= sa <<< sh;
    end

    // Bad state: arithmetic shift of a negative value became non-negative (never fires)
    always @(*) begin
        assert (!a[7] || (sa >>> sh) < 0);
    end
endmodule
