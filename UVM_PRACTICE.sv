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

class monitor extends uvm_monitor;
    `uvm_component_utils (monitor);
    virtual mem_if if;
    uvm_analysis_port #(mem_seq_item) item_collected_port;
    mem_seq_item trans_collected;
    function new (string name = "monitor",  uvm_component parent);
        super.new(name,parent);
        trans_collected=new();
        item_collected_port = new("item_collected_port",this);
    endfunction

    function void build_phase(uvm_phase phase)
       phase.raise_objection(phase);
        uvm_config_db #(virtual mem_if)::get(this,"", "vif", if);
       phase.drop_objection(phase);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        @(posedge if.monitor.clk);
        wait (if.wr_en);
        trans_collected.addr = vif.monitor_cb.addr;
        item_collected_port.write(trans_collected); 
    
    endtask 

endclass


class driver extends uvm_driver;

endclass

endclass




/*
AXI4 - ITEMS

5 channels

AW  - awaddr, awvalid, awready, awlen, awsize, awburst, awid  , awprot, awlock
W   -  wdata, wstrb, wlast, wready, wvalid
B   - bresp, bvalid, bid, bready
AR  - araddr, arvalid, arready, arburst, arlen, arsize, arid
R   - rlast, rdata, rvalid, rready, rid, rresp.
*/

import uvm_pkg::*
typedef enum bit[1:0] {INCR, WRAP, FIXED  } BurstType;


class my_base_tx #(data_width=16, addr_width=32) extends from uvm_sequence_item;
typedef my_base_tx #(data_width, addr_width) this_type_t;
    rand bit [31:0] addr;
    rand bit [7:0] data[][];
    rand bit valid, ready;
    rand bit [2:0]size;
    rand bit [7:0]len;  
    bit [1:0]resp;
    bit [7:0]id;
    bit last;
    rand BurstType btype;


/*
 Data - [   [byte1, byte2, byte3,....]
            [byte1, byte2, byte3.....]                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               
            [byte1, byte2, byte3.....]
            [byte1, byte2, byte3.....]
            ]
Data[beat][byte]
size = log2(bytes per beat)
*/

// GROUP CONSTRAINTS :-
    constraint b_size_val {
        8* (2**size)<=data_width;
    }
    
    constraint b_len_val {
        solve btype before b_len_val;
        if (btype == FIXED) {
            len inside 

        }
        else if (btype == INCR)

    }


    `uvm_object_param_utils_begin (my_base_tx #(data_width,addr_width))
        `uvm_field_int (addr,UVM_ALL_ON); // print, conver2string, copy, compare, clone.
        `uvm_field_int (data,UVM_ALL_ON);
    `uvm_object_utils_end

    function new (string name = "my_base_tx")
    super.new (name);
    endfunction

endclass


class my_tx #(d_width=16, a_width=16) extends uvm_sequence_item;

    rand bit [31:0] addr;
    rand  bit [7:0] data[][];
 

    `uvm_object_param_utils_begin(my_tx)
        `uvm_field_int (addr, UVM_ALL_ON)
    `uvm_object_params_utils_end

    constraint addr_val_align {

        (addr%1000)==0;
    }


endclass



class my_seq #(d_width = 16, a_width = 16) extends uvm_sequence_item #(my_tx #(d_width, a_width));
/* can have set_priorty()
        grab ()
        lock ()
        ungrab ()
        unlock ()
*/


    `uvm_object_param_utils (my_seq #(d_width,a_width));
    my_tx item;
    int no_of_tx;
    test_config tst_cfg;
    function new (string name = "my_seq") ;
        super.new (my_seq);
        if (!uvm_config_db #(test_config)::get( NULL, "*", "test_config", tst_cfg )) `uvm_fatal (get_type_name(), "FAILED TO GET TEST CONFIG" );
        tst_cfg.no_of_tx = no_of_tx;  
    endfunction
    task body ();
        item = my_tx#(d_width,a_width)::type_id::create("item");
        repeat (no_of_tx) begin
            start_item (item);
                assert (item.randomize() with b_type==FIXED);
            finish_item(item);
        end

    endtask
endclass



class my_sequencer #(d_width = 16, a_width=16) extends uvm_sequencer  #(item(d_width,a_width));
    `uvm_component_param_utils ("my_sequencer");

    function new (string name =  "my_sequencer", uvm_component parent);
        super.new (name,parent);
    endfunction


    function void build_phase (uvm_phase phase);
        super.new (phase);
        this.arb_mode - UVM_SEQ_ARB_FIFO;
        this.

    endfunction


/*
can have arbitration modes,
1) UVM_SEQ_ARB_FIFO
2) UVM_SEQ_ARB_STRICT_FIFO
3) UVM_SEQ_ARB_WEIGHTED_FIFO
4) UVM_SEQ_ARB_RANDOM
*/ 

endclass


class my_arb_seq#(a_width=16, d_width=16) extends uvm_sequence #(d_width,a_width);
    `uvm_object_param_utils (my_arb_seq #(d_width, a_width));

    function new (string name="my_arb_seq");
        super.new (name);
    endfunction
    virtual task pre_start ();
        super.pre_start();
        set_priorty(200);
    endtask


    task body ();

    endtask


endclass

