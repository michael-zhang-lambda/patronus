module Extend(input clk, input [3:0] a, input [3:0] b, input sel);
    // Exercises slices, concatenation, replication, zero/sign extension and ite
    wire signed [3:0] sa = a;

    reg [7:0] r_cat  = 8'h0;
    reg [1:0] r_mid  = 2'h0;
    reg [7:0] r_zext = 8'h0;
    reg [7:0] r_sext = 8'h0;
    reg [7:0] r_rep  = 8'h0;
    reg [3:0] r_ite  = 4'h0;
    reg [3:0] r_swap = 4'h0;

    always @(posedge clk) begin
        r_cat  <= {a, b};
        r_mid  <= a[2:1];
        r_zext <= {4'h0, a};
        r_sext <= {{4{sa[3]}}, sa};
        r_rep  <= {4{b[1:0]}};
        r_ite  <= sel ? a : b;
        r_swap <= {a[1:0], a[3:2]};
    end

    // Bad state: sign extension changed the low bits (never fires)
    always @(*) begin
        assert (r_sext[3:0] == r_zext[3:0] || r_sext[3:0] != r_cat[7:4]);
    end
endmodule
