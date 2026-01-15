// Import UVM package for base classes and macros (assumes UVM library is available)
import uvm_pkg::*; 

/**********************************************************************
 * UVM Study Session Q&A Summary
 * This file contains a series of questions (Q) and answers (A) 
 * covering various UVM (Universal Verification Methodology) topics.
 * Each question is given as a commented header (original phrasing),
 * followed by an answer with explanations (in comments) and 
 * SystemVerilog code examples (with inline comments to explain behavior).
 **********************************************************************/

////////////////////////////////////////////////////////////////////////
// Q1: How does inheritance work in UVM, and what is the class hierarchy of UVM base classes?
////////////////////////////////////////////////////////////////////////
// A: UVM is an object-oriented methodology built on SystemVerilog classes. 
// UVM base classes form a hierarchy through inheritance. Key points:
// - **uvm_object** is the base class for *all* UVM classes (both data objects and components).
// - **uvm_component** extends uvm_object (via an intermediate uvm_report_object) and is the base for all testbench components.
//    * Examples of uvm_component subclasses: uvm_env, uvm_agent, uvm_monitor, uvm_driver, uvm_sequencer, uvm_scoreboard, uvm_test, etc. 
// - **uvm_transaction** is a subclass of uvm_object used for transaction data. **uvm_sequence_item** extends uvm_transaction, and **uvm_sequence** extends uvm_sequence_item (for stimulus sequences).
// - All UVM components are static (constructed during build and persist throughout simulation), while UVM sequence items/transactions are dynamic (created and used on the fly).
// - **uvm_root** (type of `uvm_top`) is an implicit top-level uvm_component that is parent to any component created with a null parent.
// - When writing a UVM testbench, you create your own classes by extending these base classes. For example, a custom monitor extends uvm_monitor, and a config object extends uvm_object:
class my_monitor extends uvm_monitor;
  `uvm_component_utils(my_monitor)
  // Constructor: includes name and parent for hierarchy
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction
  // ... (other methods like build_phase, run_phase would be defined in a real monitor)
endclass : my_monitor

class my_config extends uvm_object;
  `uvm_object_utils(my_config)
  // Example configuration fields
  rand int cfg_value;
  function new(string name="");
    super.new(name);
  endfunction
  // ... (could override copy/compare/print if needed, or use uvm_object defaults)
endclass : my_config

// In the above example, my_monitor is a component (will be part of the hierarchy and uses `parent`), 
// whereas my_config is a pure data object (no parent, not in hierarchy). Both leverage UVM base classes.

////////////////////////////////////////////////////////////////////////
// Q2: Explain upcasting and downcasting in SystemVerilog (and UVM) with examples.
////////////////////////////////////////////////////////////////////////
// A: In object-oriented terms, *upcasting* means treating a subclass object as an instance of its parent class. 
// *Downcasting* is the opposite: taking a base class handle and casting it back to a subclass type.
// - **Upcasting** is implicit and always safe: a `Derived` can be used wherever a `Base` is expected (since a Derived *is-a* Base).
// - **Downcasting** requires an explicit cast and is only safe if the object is actually of the target subclass type (SystemVerilog provides `$cast` for this, which returns 0/1 for failure/success).
// In UVM, upcasting and downcasting are common with factory and config DB usage (e.g., `uvm_object::create()` returns a uvm_object handle that you downcast to your actual class).
// Below, we illustrate upcasting and downcasting with simple classes and objects:
class BaseClass;
  // Base class with a virtual method
  virtual function void foo();
    $display("BaseClass::foo()"); 
  endfunction
endclass : BaseClass

class DerivedClass extends BaseClass;
  // Derived class overrides foo and adds a new method
  function new();
    super.new();
  endfunction
  virtual function void foo();
    $display("DerivedClass::foo()"); 
  endfunction
  function void uniqueMethod();
    $display("DerivedClass::uniqueMethod() called");
  endfunction
endclass : DerivedClass

// We can demonstrate upcasting and downcasting via a simple test:
module test_casting;
  initial begin
    // Upcasting example:
    DerivedClass d = new();
    BaseClass b = d;                // implicit upcast: DerivedClass handled as BaseClass
    b.foo();                       // calls DerivedClass::foo() because foo() is virtual in BaseClass

    // Downcasting example:
    DerivedClass d2;
    if ($cast(d2, b)) begin        // attempt to downcast b back to DerivedClass
      d2.uniqueMethod();           // safe to call DerivedClass-specific method after successful cast
    end else begin
      $display("Cast failed: b is not a DerivedClass");
    end
  end
endmodule

// Note: In UVM, a typical downcast scenario is retrieving a base uvm_object from uvm_config_db or factory and then `$cast`-ing it to the actual subclass (e.g., to a my_config object).

////////////////////////////////////////////////////////////////////////
// Q3: What is the difference between calling `MyClass::type_id::create("name")` without a parent vs with a parent (`this`) in UVM?
////////////////////////////////////////////////////////////////////////
// A: UVM factory `create()` methods differ for uvm_components and uvm_objects in terms of the parent argument:
// - For **uvm_component**-derived classes, `YourClass::type_id::create(name, parent)` takes an optional parent. Passing `this` (the handle of the parent component) is important to place the new component in the hierarchy as a child. If you omit the parent (or pass `null`), the new component's parent will be `null`, meaning it becomes a top-level component under `uvm_top` instead of under the current component.
// - For **uvm_object**-derived classes (e.g. sequence items, config objects), the create method signature typically does **not** include a parent (these objects are not part of the hierarchy). The parent argument is ignored or not applicable.
// **Summary:** When constructing sub-components inside another component's `build_phase`, always use the parent (usually `this`). Only omit the parent if you're intentionally creating a top-level component (like the test itself) or if the class is not a component.
// Example usage:
module test_create_usage;
  initial begin
    // Creating a component without specifying parent:
    my_monitor comp_top = my_monitor::type_id::create("comp_top");
    // comp_top.parent will be null -> it resides under uvm_top (global root)

    // Creating a component with a parent:
    my_monitor comp_child = my_monitor::type_id::create("comp_child", comp_top);
    // comp_child.parent is comp_top -> comp_child is now a child in the hierarchy under comp_top

    // Creating a UVM object (no parent parameter needed):
    my_config cfg_obj = my_config::type_id::create("cfg_obj");
    // (For uvm_object types like my_config, the parent argument is not used since it's non-hierarchical)
  end
endmodule

////////////////////////////////////////////////////////////////////////
// Q4: What’s the purpose of calling `super.new(name, parent)` in a UVM component's constructor, and what does the `parent` argument do?
////////////////////////////////////////////////////////////////////////
// A: In a class that extends a UVM base class, calling `super.new(name, parent)` in the constructor ensures the base class is properly initialized:
// - It calls the parent class's constructor (`uvm_component::new` or `uvm_object::new`). For uvm_component, the base constructor will record the object’s name and parent.
// - The `parent` argument is a uvm_component that becomes the hierarchical parent of this new component. This is how UVM knows the component hierarchy (who is the parent of whom).
// - If `parent` is `null`, the component is considered top-level (under uvm_top). Otherwise, the component is inserted into its parent's child list.
// 
// Always call `super.new` in your constructor to propagate name/parent to the UVM base class. For uvm_object-derived classes (which have no parent), you still call super.new(name) but parent isn't an argument.
// Example:
class my_component extends uvm_component;
  `uvm_component_utils(my_component)
  function new(string name="", uvm_component parent=null);
    super.new(name, parent); // initialize base uvm_component with this name and parent
  endfunction
endclass : my_component

// In the above, super.new will ensure UVM knows this component’s name and where it lives in the hierarchy (under `parent`). 
// The `parent` is typically the handle of the enclosing component (e.g., an env or agent). If no parent is provided, UVM will attach the component to uvm_top.

////////////////////////////////////////////////////////////////////////
// Q5: What is the difference between the `uvm_component_utils` macro and the `super.new()` call in UVM class definitions?
////////////////////////////////////////////////////////////////////////
// A: `uvm_component_utils` (and its counterpart `uvm_object_utils`) and `super.new()` serve **different purposes** in a UVM class:
// - The **`uvm_component_utils(MyClass)` macro *registers* the class with the UVM factory.** It automates the implementation of factory interface methods for that class (like create). Without this macro, you cannot use `MyClass::type_id::create()` or factory overrides for that class. (`uvm_object_utils` does the same for uvm_object-based classes. Always use the appropriate macro for factory registration.)
// - The **`super.new(name, parent)` call constructs the object at runtime by calling the base class constructor.** It sets up the object's name and parent hierarchy (as explained above in Q4).
// In practice, every UVM component class definition includes both. For example:
class sample_comp extends uvm_component;
  `uvm_component_utils(sample_comp)   // factory registration macro
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);          // call base class constructor
  endfunction
endclass : sample_comp

// In this example, the macro enables factory operations on sample_comp, and super.new actually creates the instance properly. 
// **If you omit the macro:** you can't use factory overrides or `create()` for that class (you'd get an error if you try). 
// **If you omit super.new:** the object’s base portion isn’t initialized (it won’t have a valid parent/name in the UVM hierarchy), likely causing runtime errors or misbehavior. 
// They address different needs and are both required for user-defined UVM classes that participate in the factory and hierarchy.

////////////////////////////////////////////////////////////////////////
// Q6: Can you explain each of the arguments to `uvm_config_db::get()` (context, inst_name, field_name, and output)? 
////////////////////////////////////////////////////////////////////////
// A: The `uvm_config_db` is a mechanism to store and retrieve configuration data by key. The get function is parameterized by type and has signature:
//    `uvm_config_db#(T)::get(uvm_component cntxt, string inst_name, string field_name, output T value)`
// Breaking down the arguments:
// - **cntxt (context)**: The component context from which to start the lookup. Often you pass `this` (meaning "search from this component up the hierarchy"). The config DB will search in this component and upwards to ancestors for a matching entry.
// - **inst_name**: The instance name (or pattern) of the target relative to the context. This can be:
//    * a specific immediate child name or hierarchical path (e.g., `"agentA"` or `"agentA.monitor"`),
//    * an empty string `""` which means "the context itself",
//    * or a wildcard (e.g., `"*"` or `"agent*"` or `"agentA.*"`) to match multiple names.  
//   The `inst_name` should match how the configuration was set. Using `""` in get means you're retrieving a value intended for the context component itself.
// - **field_name**: The name of the configuration field (string key). This identifier labels the particular piece of configuration data (for example, `"bus_speed"` or `"timeout"`). The same string must have been used in the corresponding `set()` call.
// - **value (output)**: A reference to a variable where the retrieved value will be stored. The get function returns `1` (true) if it finds a matching config entry and writes it into this variable, or `0` if not found.
// 
// Typically, a higher-level component does `uvm_config_db#set(...)` to set a value for one of its descendants, and the lower-level component calls get to retrieve it. The `cntxt`, `inst_name`, and `field_name` in the get call must match a set entry up the hierarchy. 
// 
// **Example:** The parent environment sets a config for its child agent, and the agent retrieves it:
class my_env extends uvm_env;
  `uvm_component_utils(my_env)
  my_agent agentA;
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Set a configuration value for the agent named "agentA":
    uvm_config_db#(int)::set(this, "agentA", "bus_speed", 100);
    // ^ context=this (my_env), inst_name="agentA" (target child by name), field_name="bus_speed", value=100.
    // This makes the int value 100 available to my_env's descendant named "agentA" under the key "bus_speed".
    agentA = my_agent::type_id::create("agentA", this);
  endfunction
endclass : my_env

class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)
  int bus_speed;
  my_monitor monitor;
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Get the "bus_speed" config value intended for this agent
    if (!uvm_config_db#(int)::get(this, "", "bus_speed", bus_speed)) begin 
      // context=this (my_agent), inst_name="" (empty string means this instance), field_name="bus_speed".
      `uvm_warning("CFGNF", "bus_speed not set in config DB, defaulting to 0")
      bus_speed = 0;
    end
    // Now use bus_speed (e.g., pass to sub-components or print it)
    monitor = my_monitor::type_id::create("monitor", this);
  endfunction
endclass : my_agent

// In the above example, the env set the value for "agentA"."bus_speed". 
// The agent (named "agentA") calls get with context itself (`this`) and inst_name "" to retrieve config meant for itself. 
// Because the env's set used inst_name "agentA" (matching the agent's name in the env's context), the get finds the value 100 and stores it in bus_speed.
// If we had used a wildcard inst_name (for example, "agentA.*") in set, then that value would apply not only to agentA but also to its children. In such a case, a child of agentA (say monitor) could do `uvm_config_db::get(this, "", "bus_speed", ...)` and still retrieve the value. 
// The key is that the combination of context and inst_name in set and get calls must align so that the search finds the entry.

// (Note: uvm_config_db::set has a similar signature with context, inst_name, field_name, and a value. The context in set specifies where in the hierarchy the entry is placed, and inst_name can include wildcards to apply to multiple components.)

////////////////////////////////////////////////////////////////////////
// Q7: Could you explain the roles of the non-run UVM phases (connect, end_of_elaboration, start_of_simulation, extract, check, report) and give examples of how they're used?
////////////////////////////////////////////////////////////////////////
// A: UVM has several simulation phases besides `run_phase`. These phases occur in a specific order around the runtime and serve particular purposes. Key non-run phases and their roles:
// - **build_phase** – (not asked, but precedes connect) constructs the testbench components (top-down).
// - **connect_phase** – used to hook up cross-component connections like TLM ports/exports after all components are built. This runs after build (connections are typically made bottom-up).
// - **end_of_elaboration_phase** – used for final adjustments after build/connect, but before simulation starts. Often used to print the testbench topology or finalize configuration settings. (Runs just before time 0, after connect phase.)
// - **start_of_simulation_phase** – called at time 0, just before entering run. Often used to display banners, or final information, or perform any last-minute setup (since time advances after this).
// - **run_phase** – the main simulation phase (time-consuming, where stimulus is generated and applied). (Not detailed here since the question is about non-run phases.)
// - **extract_phase** – occurs after run is complete (after all objections dropped). Used to extract and collate results, such as pulling final coverage or checking scoreboard data. Think of it as gathering data for pass/fail criteria.
// - **check_phase** – follows extract. Here you implement checks to determine if the test passed or failed. For example, compare expected vs actual results, check that error counters are zero, etc. This phase is for reporting any discrepancies as UVM errors.
// - **report_phase** – the final phase, used to report the outcome of the test and clean up. This could print a summary, call `uvm_print_topology()` again for logging, or close files. It runs after check.
// 
// All these phase callbacks are functions (except run_phase, which is a task). They are typically implemented in your components if needed. Below is a simplified example illustrating how some components might implement these phases:
class example_monitor extends uvm_monitor;
  `uvm_component_utils(example_monitor)
  uvm_analysis_port#(int) analysis_port;  // This monitor will send int transactions via an analysis port
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
    analysis_port = new("analysis_port", this);
  endfunction

  // (In a real monitor, you would implement run_phase to sample interface signals and write data into analysis_port)
endclass : example_monitor

class example_scoreboard extends uvm_component;
  `uvm_component_utils(example_scoreboard)
  // Analysis imp port to receive transactions from the monitor. It will call write() on this scoreboard.
  uvm_analysis_imp#(int, example_scoreboard) analysis_export; 
  int total_transactions;
  int expected_total;
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
    analysis_export = new("analysis_export", this);  // analysis_export will call this.write()
    total_transactions = 0;
    expected_total = 10;  // Suppose we expect 10 transactions for this test (could be set via config)
  endfunction

  // This write() method is called whenever a transaction is forwarded to the scoreboard's analysis_export
  function void write(int trans);
    // The scoreboard receives a transaction (int in this case)
    total_transactions += 1;
    `uvm_info("SCOREBOARD", $sformatf("Received transaction (val=%0d). Total count=%0d", trans, total_transactions), UVM_LOW)
  endfunction

  function void extract_phase(uvm_phase phase);
    super.extract_phase(phase);
    // Extract phase: gather results after run. For example, finalize any remaining analysis or compute final metrics.
    `uvm_info("SCOREBOARD", $sformatf("Extract phase: final transaction count = %0d", total_transactions), UVM_LOW)
    // (In a real scoreboard, you might calculate final expected values or aggregate coverage here.)
    // No additional extraction needed in this simple example.
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // Check phase: verify the results of the test. Compare total vs expected, or check for errors.
    if (total_transactions != expected_total) begin
      `uvm_error("SCOREBOARD", $sformatf("Expected %0d transactions, but observed %0d", expected_total, total_transactions))
    end else begin
      `uvm_info("SCOREBOARD", "Check phase: All transactions accounted for as expected.", UVM_LOW)
    end
    // (Real check_phase code might also verify data integrity, absence of protocol errors, etc.)
  endfunction

  function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    // Report phase: output final test outcome or statistics.
    if (get_report_severity_count(UVM_ERROR) == 0) begin
      `uvm_info("SCOREBOARD", "Report phase: TEST PASSED", UVM_LOW)
    end else begin
      `uvm_info("SCOREBOARD", $sformatf("Report phase: TEST FAILED with %0d errors", get_report_severity_count(UVM_ERROR)), UVM_LOW)
    end
    // (In report_phase you might close files or print a detailed summary. Here we just declare pass/fail based on error count.)
  endfunction
endclass : example_scoreboard

class example_env extends uvm_env;
  `uvm_component_utils(example_env)
  example_monitor mon;
  example_scoreboard sb;
  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Construct sub-components
    mon = example_monitor::type_id::create("mon", this);
    sb  = example_scoreboard::type_id::create("sb", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect phase: connect analysis ports/exports between components
    mon.analysis_port.connect(sb.analysis_export);
    // ^ We connect the monitor's analysis_port to the scoreboard's analysis_export so that transactions flow into the scoreboard.
  endfunction

  function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    // End of elaboration: final adjustments before simulation starts
    `uvm_info("ENV", "End of elaboration: Testbench topology constructed, finalizing configuration.", UVM_LOW)
    uvm_top.print_topology(); 
    // ^ Example: print the hierarchy of components for logging.
  endfunction

  function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    // Start of simulation: just before time 0
    `uvm_info("ENV", "Starting simulation... (all components are built and connected)", UVM_LOW)
    // You might print a banner or a summary of config here.
  endfunction
endclass : example_env

// In a real testbench, you would have a uvm_test that creates example_env, and run the simulation (run_phase).
// The non-run phases shown above would execute in the order: build -> connect -> end_of_elaboration -> start_of_simulation -> run -> extract -> check -> report.
// This sequence ensures that components are constructed, connected, and configured before time 0, and that results are collected and verified after the main stimulus (run_phase) completes.
// UVM Learning Compilation: All Questions Asked in This Session
// Author: ChatGPT (compiled on request)
// Format: SystemVerilog file with explanations and examples in comments

////////////////////////////////////////////////////////////
// Q1: Teach me how inheritance works in UVM
////////////////////////////////////////////////////////////

// Inheritance in UVM allows you to extend base classes like uvm_component
// or uvm_sequence_item and reuse/override functionality.

class base_pkt extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  
  `uvm_object_utils_begin(base_pkt)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "base_pkt");
    super.new(name);
  endfunction
endclass

class burst_pkt extends base_pkt;
  rand int burst_len;

  function new(string name = "burst_pkt");
    super.new(name);
  endfunction
endclass

// burst_pkt inherits fields and methods from base_pkt.
// UVM also supports method overriding and polymorphism.

////////////////////////////////////////////////////////////
// Q2: Can you explain upcasting and downcasting?
////////////////////////////////////////////////////////////

// Upcasting: Child to Parent (always safe)
base_pkt pkt;
burst_pkt bp = new();
pkt = bp; // Upcasting — safe

// Downcasting: Parent to Child (requires $cast)
burst_pkt bp2;
if (!$cast(bp2, pkt)) begin
  `uvm_error("CAST", "Downcast failed")
end else begin
  `uvm_info("CAST", "Downcast succeeded", UVM_LOW)
end

////////////////////////////////////////////////////////////
// Q3: What’s the difference between passing 'this' to create vs not?
////////////////////////////////////////////////////////////

// With parent:
my_base_pkt::type_id::create("item", this);
// → Registers the object in hierarchy under 'this'

// Without parent:
my_base_pkt::type_id::create("item");
// → Object is created but not connected in UVM hierarchy

// Use 'this' to allow instance overrides, config_db access, etc.

////////////////////////////////////////////////////////////
// Q4: What does super.new(name, parent) do?
////////////////////////////////////////////////////////////

// super.new initializes the base class. In uvm_component it:
// - Sets instance name
// - Sets parent
// - Registers with factory, phases, etc.

function new(string name = "my_sequencer", uvm_component parent);
  super.new(name, parent);
endfunction

// For uvm_object, there is no parent — only name is passed.

////////////////////////////////////////////////////////////
// Q5: Difference between uvm_component_utils and super.new()
////////////////////////////////////////////////////////////

// `uvm_component_utils(my_class)` → registers the *type* with the factory
// super.new(...) → initializes the *instance* and places it in hierarchy

// You need BOTH in most UVM classes.

////////////////////////////////////////////////////////////
// Q6: Explain arguments to uvm_config_db::get()
////////////////////////////////////////////////////////////

// Syntax:
// uvm_config_db#(T)::get(context, inst_name, field_name, output_value);

// Example:
virtual my_if intf;
if (!uvm_config_db#(virtual my_if)::get(this, "*", "intf", intf))
  `uvm_fatal("NOCFG", "Interface not set")

// - 'this' = context where to start lookup
// - "*" = instance pattern to match
// - "intf" = field name
// - intf = output variable

////////////////////////////////////////////////////////////
// Q7: What are the other phases (besides build and run)?
////////////////////////////////////////////////////////////

// connect_phase → connect TLM ports
function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  drv.seq_item_port.connect(sqr.seq_item_export);
endfunction

// end_of_elaboration_phase → sanity checks, print topology
function void end_of_elaboration_phase(uvm_phase phase);
  uvm_top.print_topology();
endfunction

// start_of_simulation_phase → banners, initialize logs
function void start_of_simulation_phase(uvm_phase phase);
  `uvm_info("SIM", "Simulation starting", UVM_LOW)
endfunction

// extract_phase → gather results
function void extract_phase(uvm_phase phase);
  total_errors = err_count;
endfunction

// check_phase → compare expected vs actual
function void check_phase(uvm_phase phase);
  if (total_errors != 0)
    `uvm_error("CHK", "Errors found")
endfunction

// report_phase → final verdict
function void report_phase(uvm_phase phase);
  if (total_errors == 0)
    `uvm_info("REPORT", "TEST PASSED", UVM_NONE)
  else
    `uvm_info("REPORT", "TEST FAILED", UVM_NONE)
endfunction

////////////////////////////////////////////////////////////
// Q8: What is uvm_phase phase and when do we raise_objection?
////////////////////////////////////////////////////////////

// uvm_phase phase is an object passed to each phase callback
// It allows you to control phase behavior:
// e.g., raise and drop objections in run_phase

task run_phase(uvm_phase phase);
  phase.raise_objection(this);
  #1000ns;
  phase.drop_objection(this);
endtask

// Objections keep the phase alive — simulation ends when no objections are raised.
   