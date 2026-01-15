interface mem_if (input clk, reset);

logic [1:0] addr;
logic wr_en;
logic rd_en;
logic [7:0]wdata;
logic [7:0]rdata;


clocking driver_cb @(posedge clk);
    default input #1 output #1;
    output addr;
    output wr_enl
    output wdata;
    output rd_en;
    input rdata;
endclocking


clocking monitor_cb @(posedge clk);
    default input #1 output #1;
    input addr;
    input wr_enl
    input wdata;
    input rd_en;
    input rdata;
endclocking

modport DRIVER (clocking driver_cb,input clk, reset);
modport MONITOR (clocking monitor_cb,input clk, reset);


endinterface

module tb_top;
bit clk;
bit reset;

always #5 clk = ~clk;// clock generation

initial begin
    reset = 1;
    #5;
    reset =0;
end

mem_if vif (clk,reset);

mem_ram DUT u1 (.clk(vif.clk),
                .reset(vif.reset),
                .addr(vif.addr),
                .wdata(vif.wdata),
                .rdata(vif.rdata),
                .wr_en(vif.wr_en),
                .rd_en(vif.rd_en)
)

initial begin
    uvm_config_db #( virtual mem_if)::set( uvm_root::get(),"*","vif",vif);
    run_test ();
end

endmodule


class my_seq_item extends uvm_sequence_item;


rand bit [7:0] addr;
rand bit [7:0] wdata;
rand bit  wr_en;
rand bit  rd_en;
     bit [7:0] rdata;


`uvm_object_utils_begin (my_seq_item)
    `uvm_field_int (addr,UVM_ALL_ON);
    `uvm_field_int (addr,UVM_ALL_ON);
    `uvm_field_int (addr,UVM_ALL_ON);
    `uvm_field_int (addr,UVM_ALL_ON);
    `uvm_field_int (addr,UVM_ALL_ON);
`uvm_object_utils_end


function new (string name = "my_seq_item") 
    super.new(name);
endfunction

constraint wr_rd {
    wr_en!=rd_en;
};

endclass

class my_seq extends uvm_sequence #(my_seq_item);
`uvm_object_utils (my_seq);

my_seq_item txns;
int N=30;

function new (string= "name")
 super.new (name);
endfunction



task body();
    repeat (N)  begin
        txns = my_seq_item::type_id::create ("txns");
        start_item (txns);
        txns.randomize();
        finish_item(txns);
    end
endtask:body
endclass


class some_sequencer extends uvm_sequencer#(my_seq_item);
    `uvm_component_utils (some_sequencer);
    function new (string name= " some_seuqnecer", uvm_component parent);
        super.new(name,parent);
    endfunction

endclass


class my_env extends uvm_env;

`uvm_component_utils (my_env);
my_agent agt;
my_scoreboard scrbrd;

function new (string name="my_env", uvm_component parent)
    super.new (name, parent); 
endfunction

function void build_phase (uvm_phase phase) 
    phase.raise_objection(this);
    agt = my_agent::type_id::create ("agt",this);
    srbrd = my_scoreboard::type_id::create ("scrbrd", this);
    phase.drop_objection(this);

endfunction

function void connect_phase(uvm_phase phase)
    agt.monitor.item_collected_port.connect(scrbrd.item_collected_export);
endfunction
endclass


class my_agent extends uvm_agent;
my_monitor monitor;
my_driver driver;
some_sequencer seqr;

    `uvm_component_utils (my_agent);

function new (string name="my_agent", uvm_component parent);
    super.new(name,parent);
endfunction

void function build_phase(uvm_phase phase) 
    monitor = my_monitor::type_id::create ("monitor",this);
    if (get_is_active() == UVM_ACTIVE) begin
        driver = my_driver::type_id::create ("driver",this);
        seqr = some_sequencer::type_id::create("seqr", this);
    end
endfunction

void function connect_phase(uvm_phase phase)
    phase.raise_objection(phase);
    driver.seq_item_port.connect(seqr.seq_item_export);
    phase.drop_objection(phase);
endfunction

agnt.drv.seq_item_port.connect(seq_export)