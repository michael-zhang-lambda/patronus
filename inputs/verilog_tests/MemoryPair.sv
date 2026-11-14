module MemoryPair(input clk, input we, input [1:0] wa, input [3:0] wd, input [1:0] ra);
    // Two zero-initialized memories that receive identical writes
    reg [3:0] mem_a [0:3];
    reg [3:0] mem_b [0:3];
    initial $readmemh("zeros4.hex", mem_a);
    initial $readmemh("zeros4.hex", mem_b);

    always @(posedge clk) begin
        if (we) begin
            mem_a[wa] <= wd;
            mem_b[wa] <= wd;
        end
    end

    // Bad state: the memories differ at the read address
    always @(*) begin
        assert (mem_a[ra] == mem_b[ra]);
    end
endmodule
