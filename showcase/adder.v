module adder(input clk, input [1:0] a, input [1:0] b, output reg [1:0] out);
    reg r1, r2, r3, r4, r5, r6;
    
    always @(posedge clk)
    begin
        r1 <= a[0] & b[0];
        r2 <= a[0] ^ b[0];
        r3 <= r2 ^ 1'b0;
        out[0] <= r3;
        
        r4 <= a[1] ^ b[1];
        r5 <= a[0] & b[0];
        r6 <= r4 ^ r5;
        out[1] <= r6;
    end
endmodule