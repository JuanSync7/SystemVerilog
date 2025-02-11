module binary_tree_eviction_module #(
    LG2_DEPTH = 3,
    DW = 32
)
(
    input logic clk,
    input logic resetn,

    input logic [DW-1:0] din,
    input logic din_valid,
    output logic [DW-1:0] dout,

    input logic [LG2_DEPTH-1:0] index,

    output logic [LG2_DEPTH-1:0] data_evicted 
);


logic [(LG2_DEPTH**2)-1:1] next_bin_tree_ptr;
logic [(LG2_DEPTH*82)-1:1] bin_tree_ptr;

logic [LG2_DEPTH-1:0] data_evicted;

var int level;
begin

    always_comb begin
        next_bin_tree_ptr = bin_tree_ptr; // prevent latch

        next_bin_tree_ptr[1] = index[LG2_DEPTH-1]; // the 

        for ( int i = 2 ; i < LG2_DEPTH**2 ; i++) // make sure every pointer is observed
            level = $clog2(i);
            if(i[level-1:0] == index[LG2_DEPTH-1:LG2_DEPTH-1-(level-1)]);  // 
                next_bin_tree_ptr[i] = index[LG2_DEPTH-1-(level-1)-1]; 
    end

    always_ff @ (posedge clk or negedge resetn) begin
        if(~resetn) begin
                bin_tree_ptr <= '0; // refresh to point to index 0 of the fifo
        end else begin
            if(din_valid)
                bin_tree_ptr <= next_bin_tree_ptr;
        end
    end
    assign data_evicted = !binary_tree_ptr;
end
endmodule : binary_tree_eviction_module
