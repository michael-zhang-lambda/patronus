module MemoryUnsafe(input clk, input we, input [1:0] wa, input [3:0] wd);
    // Zero-initialized memory with an unconstrained write port
    reg [3:0] mem [0:3];
    initial $readmemh("zeros4.hex", mem);

    always @(posedge clk) begin
        if (we) begin
            mem[wa] <= wd;
        end
    end

    // Bad state (reachable): entry 3 holds 15
    always @(*) begin
        assert (mem[2'h3] != 4'hf);
    end
endmodule
