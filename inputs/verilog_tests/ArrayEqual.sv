module ArrayEqual(input clk, input [1:0] a, input [3:0] d);
    // Two zero-initialized memories receive identical writes every cycle
    reg [3:0] m1 [0:3];
    reg [3:0] m2 [0:3];
    initial $readmemh("zeros4.hex", m1);
    initial $readmemh("zeros4.hex", m2);

    always @(posedge clk) begin
        m1[a] <= d;
        m2[a] <= d;
    end

    // Bad state: the memories differ. Verilog cannot compare whole memories,
    // so compare every entry instead.
    always @(*) begin
        assert (m1[0] == m2[0] && m1[1] == m2[1] && m1[2] == m2[2] && m1[3] == m2[3]);
    end
endmodule
