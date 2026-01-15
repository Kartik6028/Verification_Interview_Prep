// CONCEPT
    // DownCast & Upcase

    //UPCASTING Treating a child object as parent type

    class base_pkt extends uvm_sequence_item;
    endclass

    class burst_pkt extends base_pkt;
    endclass

    burst_pkt bp;
    base_pkt p;

    bp = new("bp");
    p = bp; //upcasting

    uvm_component comps [$];
    drv = my_driver::type_id::create ("drv");
    comps.pushback(drv);

    /*
    why do we ever need this ?
    ans - for a number of reasons
    1) you can use a generic base component handle and still be able to call the most derived method.
    2) factory always returns the base handle type but the actual object is derived type.
    3) phase execution
    4) reuseablitiy
    */


    // DURING UPCASTING YOU CANNOT USE A FUNCTION THAT IS EXCLUSIVELY IN THE DERIVED CLASS AND NOT OVERRIDEEN for that we need to downcast.
    // DOWNCAST Gives you the ability to check that whether this parent handle was upcasted before, ie does it really point to a child? if yes then you can safely use all the derived-only methods from the child
    p = burst_pkt::type_id::create("p");
    bp = p // illegal in SV
    if (!$cast (bp, p))
    begin
        `uvm_error("nope")
    end


    class parent;
        var x;
        virtual function vir;
        // some code
        endfunction

        function non_vir_parent
        endfunction
    endclass

    class child extends from parent;
        var y;
        virtual fuction vir;
        //somecode
        endfunction

        function non_vir_parent
        endfunction

        function fun_child;
       // some code
        endfunction
    endclass


    parent p;
    child c;
    c = new ("c");
    p =c  //  UPCASTING
    /*
    now this means that p.vir would actually execute function from child and not parent.
    but p.non_vir_parent will actually execute that function from parent.
    and p.fun_child is impossible as it is derived only ?
    and p.y can we use this var from child - cannot
    */
    parent p;
    child c;

    $cast(c,p); // downcasting
    // ye cast do kaam karta hai, 1) check karega ki parent kya sach me child ko point karta hai ? agaar haan to tumhe ek child ka handle dedega jo seedha child ko point karta hai to use child only methods.
    //then now if i do p.vir - same as before child's derived function, but now i can also do c.fun_child or access c.y which are both child only functions right ?
//CONCEPT

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

class my_base_pkt extends uvm_sequence_item;
    
    rand bit [31:0] addr;
    rand bit [31:0] data;
    
    `uvm_object_utils_begin (my_base_pkt)
        `uvm_field_int (data, UVM_ALL_ON)
        `uvm_field_int (addr, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name= "my_base_pkt");
        super.new (name);
    endfunction
    constraint addr_range {
        addr inside {[32'h00000000: 32'h60000000]};
    };

endclass
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

class my_tx #(d_width = 16,a_width = 16) extends uvm_sequence_item;

    rand bit [31:0] addr;
    rand bit [7:0] data[][];
    bit valid, ready;

    `uvm_param_utils_begin(my_tx #(d_width, a_width))
        `uvm_field_int(addr,UVM_ALL_ON);
        `uvm_field_array_int (data, UVM_ALL_ON);
    `uvm_param_utils_end

    function new (string name =  "my_tx") ;
        super.new (name);
    endfunction

    constraint addr_align_check {

        addr % 1000 ==0;
    }
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


class my_seq extends from uvm_sequence #(my_tx);
    my_tx #(d_width,a_width)item;
    `uvm_object_utils ("my_seq");

    function new (string name  = "my_seq")
        super.new (name);
    endfunction

    task body ()
        item= my_tx#(a_width,d_width)::type_id:create ("item");
        repeat (50) begin
            start_item(item);
                if (!item.randomize()) `uvm_fatal("RANDOMIZATION FAILED") ;
            finish_item(item);
        end

    endtask
endclass


class my_wr_seq #(d_width=16, a_width=16)extends uvm_sequence;
    `uvm_object_param_utils (my_wr_seq #(d_width,a_width))
    
    my_tx #(d_width,a_width) item;
    const int no_of_trans;
    test_config tst_cfg;

    function new(string name = "my_wr_seq");
        super.new (name);
        tst_cfg = new ();
        if (!uvm_config_db#(test_config)::get(NULL,"*","test_config",tst_cfg )) `uvm_fatal (get_type_name(), "failed to get config db");
       no_of_trans=tst_cfg.no_of_trans; 
    endfunction

    task body ();
        repeat (no_of_trans) begin
        start_item (item);
            assert (item.randomize());
        finish_item (item);
        item.print();
            #10;
        end

    endtask
endclass

class my_sequence extends  uvm_sequence #(my_base_pkt);
    `uvm_object_utils(my_sequence)
    my_base_pkt item;
    function new (string name="my_sequence")
        super.new (name);
    endfunction

    task body ();
    repeat (50)
    begin
        item = my_base_pkt::type_id::create("item",this); // here what "this" does is actually create a parent, and says that everything under me comes from me as aparent. helps in doing override_by_inst if required.
        start_item(item);
        if(!item.randomize() with {data == 32'hFF;}) `uvm_error sformatf(("randomization failed"))
        finish_item(item);
    end

    endtask:body
endclass

class some_sequencer extends uvm_sequencer#(my_seq_item);
    `uvm_component_utils (some_sequencer);
    function new (string name= " some_seuqnecer", uvm_component parent);
        super.new(name,parent);
    endfunction
endclass

class my_driver extends uvm_driver #(my_base_pkt);
    
    `uvm_component_utils(my_driver)
    virtual my_interface if;
    my_base_pkt item;
    function new(string name = "my_driver", uvm_component parent);
        super.new (name,parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        if (!(uvm_config_db#(virtual my_interface)::get(this,"*", "intf", if))) `uvm_error (get_type_name(),"failed to get virtual interface driver class");

        
    endfunction

    function void end_of_elaboration_phase (uvm_phase phase);
    endfunction

    function void start_of_simulation_phase (uvm_phase phase);
    endfunction

    function void connect_phase (uvm_phase phase);
    endfunction

    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        phase.raise_objection();
        /*
        pre_reset_phase
        //reset_phase
        //post_reset_phase

        //pre_configure
        //configure
        //post_configure

        //pre_main
        //main
        //post_main

        //pre_shutdown
        //shutdown
        post_shutdown
        */
        forever begin
            item = my_base_pkt::type_id::create("item");
            seq_item_port.get_next_item (item);
            drive(item);
            item_done();
        end
        phase.drop_objection();

    endtask

    function void report_phase();
    endfunction

    function void extract_phase();
    endfunction

    function void check_phase();
    endfunction
endclass


class my_env extends  uvm_env;
    `uvm_component_utils (my_env)
    my_scoreboard myscrbrd;
    my_agent agnt;
    my_coverage_collector cvrge;


    function new (string name = "my_env", uvm_component parent);
        super.new (name,parent);  
    endfunction


    function void build_phase (uvm_phase phase);
        super.new(phase);
        myscrbrd = my_scoreboard::type_id::create ("myscrbrd",this);
        agnt = my_agent::type_id::create ("agnt",this);
        cvrge = my_cvrge::type_id::create ("cvrge",this);
    endfunction

    function void connect_phase (uvm_phase phase);
        super.new (phase);
        my_agent.read_port.connect(myscrbrd.read_port_export);
        my_agent.write_port.connect(myscrbrd.write_port_export);
        my_agent.write_port.connect(my_coverage_collector.analysis_export);
    endfunction
                            
endclass

class my_agent extends uvm_agent;
    `uvm_component_utils (my_agent);
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    // we need to create the virt seq or main seq, drv, mon, scoreboard
    // connect seq <-> driver
    // connect monitor <-> scoreboard
    my_driver my_drv;
    my_sequencer my_seqr;
    my_monitor mon;
    uvm_analysis_export #(my_base_pkt) read_port;
    uvm_analysis_export #(my_base_pkt) write_port;

    function new (string name = "my_agent", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        mon = my_monitor::type_id::create("mon", this);
        if (is_active == UVM_ACTIVE) begin
            my_drv = my_driver::type_id::create("my_drv",this);
            my_seqr = my_sequencer::type_id::create("my_seqr",this);
        end
        read_port = new (this);
        write_port = new (this);
    endfunction

    function void connect_phase (uvm_phase phase);
        super.connect_phase(phase);
        mon.monitor_port_read.connect(read_port.uvm_analysis_export);
        mon.monitor_port_tx.connect(write_port.uvm_analysis_export);
       if (is_active == UVM_ACTIVE)  my_drv.seq_item_port.connect(my_seqr.seq_item_export);
    endfunction

endclass


class my_monitor extends uvm_monitor;
    `uvm_component_utils (my_monitor)
    my_base_pkt item;
    uvm_analysis_port#(my_base_pkt) monitor_port_tx;
    uvm_analysis_port#(my_base_pkt) monitor_port_read;
    vif intf;
    function new (string name = "my_monitor", uvm_component parent);
        super.new (name, parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);

        uvm_config_db #(virtual intf)::get(this, "*", "intf", intf);
        monitor_port_tx = new ("this");
        monitor_port_read = new ("this");
    endfunction

    task run_phase (uvm_phase phase);
        forever begin
            fork begin
                item = my_base_pkt::type_id::create (this);
                readfromdut(item);
                monitor_port_read.write (item);
            end
            begin
            end
                item = my_base_pkt::type_id::create (this);
                readtodut(item);
                monitor_port_tx.write (item);
            join
        end
    endtask
endclass
class my_coverage_collector extends uvm_subscriber #(my_base_pkt);
    `uvm_component_utils(my_coverage_collector);

    my_base_pkt tx;
    covergroup test;
       cv_data: coverpoint tx.data {


        }
        

    endgroup

    function new (string name="my_coverage_collector", uvm_component parent);
        super.new (name,parent);
        test=new ();
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    function void write (my_base_pkt t);
        tx = t;
        test.sample();
    endfunction 


    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info ( "COVERAGE_DEBUG", $sformatf (" coverage for collector instance %s :- %f \n\n",this.get_full_name(), test.get_inst.coverage()), UVM_HIGH)
    endfunction
endclass

class my_scoreboard extends uvm_subscriber #(my_base_pkt);
// SPLIT INTO EVALUATOR AND PREDICTOR
    `uvm_component_utils (my_scoreboard)
    
    uvm_analysis_export #(my_base_pkt) expected_passthrough_export;
    uvm_analysis_export #(my_base_pkt) actual_passthrough_export;
    my_predictor prdctor;
    my_evaluator evaltor;
    function new (string name = "my_scoreboard", uvm_component parent); 
        super.new (name,parent);
    endfunction 


    function void build_phase (uvm_phase phase);
        super.build_phase (phase);

        expected_passthrough_port = new ("this");
        actual_passthrough_port = new ("this");
        prdctor = my_predictor::type_id::create ("prdctor", this);
        evaltor = my_evaluator::type_id::create ("evaltor", this);
    endfunction 

    function void connect_phase(uvm_phase phase);
        super.connect_phase (phase);
        prdctor.expected_port.connect(evaltor.expected_export);
        expected_passthrough_export.connect(prdctor.analysis_export);
        actual_passthrough_export.connect (evaluator.actual_export);
    endfunction
endclass

class my_predictor extends uvm_subscriber #(my_base_pkt);
// Get txns written to the DUT - from the monitor, and predict results and send them to evaluator.
    my_base_pkt item;

    uvm_analysis_port #(my_base_pkt) expected_port;

    `uvm_component_utils (my_predictor)
    function new (string name = "my_predictor", uvm_component parent);
        super.new (name,parent);
        expected_port = new("expected_port",this);
    endfunction

    function write (my_base_pkt t);
        item = my_base_pkt::type_id::create("item");
        case (t.opcode) 
            ADD: item.data = t.a+t.b;
            SUB: item.data = t.a-t.b;
        endcase
        expected_port.write (item);
    endfunction
endclass

class my_evaluator extends uvm_subscriber #(my_base_pkt);
    `uvm_component_utils (my_evaluator);
    uvm_analysis_export #(my_base_pkt) expected_export;
    uvm_analysis_export #(my_base_pkt) actual_export;

    uvm_tlm_analysis_fifo #(my_base_pkt) expected_fifo;
    uvm_tlm_analysis_fifo #(my_base_pkt) actual_fifo;

    function new (string name = "my_evaluator", uvm_component parent);
        super.new(name,parent);
    endfunction

    function void build_phase (uvm_phase phase);
        super.build_phase (phase);
        expected_export = new ("expected_port",this);
        actual_export = new ("actual_port",this);
        expected_fifo = new ("expected_fifo",this);
        actual_fifo = new ("actual_fifo",this);
    endfunction


    function void connect_phase (uvm_phase phase);
        super.connect_phase (phase);
        expected_export.connect ( expected_fifo.analysis_export);
        actual_export.connect ( actual_fifo.analysis_export);
    endfunction

    task run_phase (uvm_phase phase);
        my_base_pkt expected_item;
        my_base_pkt actual_item;
        forever begin
            expected_fifo.get(expected_item);
            actual_fifo.get (actual_item);
            if (actual_item.result != expected_item.result) begin
                `uvm_error ( "EVALUATOR_ERROR", sformatf ("expected results :- %s mismatched with actual results %s", expected_item.conver2string(), actual_item.convert2string()))
            end 
        end

    endtask


    function write (my_base_pkt t);

    endfunction
endclass


// Virtual Sequencer is used to remove hierarichal paths like seq.start (env.agent.sequencer)
//phase.phase_done.set_drain_time(this,10 ); - used to  delay dropping an objection for the scoreboard to allow time for pending transactions to be processed.
// so agent would have something like, actual_sequencer seqr;
//and connect it the driver, in the ENV, you would do uvm_sequencer #( type same as the actual seqr) my_virt_seqr
// and in connect phase this.my_virt_seqr = agnt.seqr
// now the benefit is that in the test itself you can do
// my_virtual_seq seq1;
// seq1 type_id::Create, 
// and configure the env, and do seq1.seqr = env.seqr, and seq1.start (null);
class my_virtual_sequence extend uvm_sequence #(uvm_sequence_item);
    `uvm_component_utils (my_virtual_sequence);
    my_sequence seq1;
    my_sequence2 seq2;
    uvm_sequencer #(uvm_sequence_item) seqr; // a virtual sequencer, this is just a handle to the actual sequencer. Hence no need to type_id:: create
    // The agent will actually have the real sequenccer, that would be connected to the driver, Agent passes the handle to this seqr up the chain, to ENV and to TEST, which in turn passes it to the seq it is starting.
    function new  (string name = "my_virtual_sequence");
        super.new(name);
    endfunction

    task body ()
        fork 
            begin
                seq1 = my_sequence::type_id::create ("seq1", this);
                seq1.start (seqr);
            end

            begin
                seq2 =  my_sequence2::type_id::create("seq2", this);
                seq2.start (seqr);
            end

        join
    endtask
endclass



// You can do v_seqr.set_arbtritration (SEQ_ARB_RANDOM)  in the virtual sequence if two or more sequences running on the same seqr.
// you can do set_priority (100) inside the actual sequence itself, and pair it with sequencer with arb mode set as SEQ_ARB_WEIGHTED
// you can use lock() and  unlock () within a sequence to get exclusive access to the seqr, once the inflight tx items are sent
// Or do grab () and ungrab () if you want to force the inlfight TX items as well.
// can use get_response(item) in the seq paired with seq_item_port.put(item) to send feedback back to the sequence for maybe control
//p_sequencer and m_sequencer, later is the base that is given to you by default. But you don't have the actual handles to the actual seqr inside that base virt seqr, for that you need to do cast with p_sequencer, and you get visibility to the initernal seqrs.


// ARBITRATION SEQUENCE
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
/// ARBITRATION SEQUENCE


