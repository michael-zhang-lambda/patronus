module MemoryInit(input clk, input we, input [1:0] wa, input [3:0] wd, input [1:0] ra);
    // Memory initialized to all zeros
    reg [3:0] mem [0:3];
    initial $readmemh("zeros4.hex", mem);

    always @(posedge clk) begin
        // Only values with the top bit cleared are ever written
        if (we) begin
            mem[wa] <= wd & 4'h7;
        end
    end

    // Bad state: some entry has its top bit set
    always @(*) begin
        assert (!(mem[ra] > 4'h7));
    end
endmodule
