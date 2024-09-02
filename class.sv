// this is the parent class
class base_subsystem;
  logic [31:0] data;
  logic [31:0] addr;
  bit write;
  string amba_prot;
  string pkg_type;

  function new(logic [31:0] addr, logic [31:0] data);
    this.addr = addr;
    this.data = data;
  endfunction
endclass

class top_module extends base_subsystem;
  logic [3:0] id;
  logic [2:0] mode = 3;

  function new(logic [3:0] id, logic [2:0] mode, logic [31:0] offset, logic [31:0] addr, logic [31:0] data);
    super.new(addr+offset, data); // call the constructor of the base_subsystem
    this addr = addr; // set the addr var of the top_module the addr var
    this data = data; // set the data var of the top_module to the data var
    this id = id; // set the id 
    this mode = mode; // set the mode
  endfunction
endclass

module tb;

  logic [31:0] data;
  logic [31:0] addr;
  logic [3:0] id;
  logic [2:0] mode;
  logic [31:0] offset;
  
  initial begin

    //create top_module
    top_module top1;

    addr = 32'h0000_0100;
    offset = 32'h0000_0100;
    data = 32'h5555_AAAA;
    id = 1;
    mode = 2;
    // instantiate the top_module class
    top1 = new (id,mode,offset,addr,data);
    $display (top1.addr, top1.data, top1.id, top1.mode);
  end
endmodule
