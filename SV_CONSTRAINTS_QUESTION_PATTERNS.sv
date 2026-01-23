//SystemVerilog Constraint Patterns
//Bit Count Constraint (Fixed Number of 1s)

//Description: Ensures that a bit-vector has an exact number of bits set to 1. This is a bit-level constraint often used to control parity or Hamming weight. SystemVerilog provides the $countones function to count the number of 1 bits in a vector, which can be equated to a desired value.
//Sample Interview Question: "Given an 8-bit random variable, write a constraint to ensure it has exactly 4 bits equal to '1'."

Solution (SystemVerilog):

class BitCountExample;
  rand bit [7:0] data;
  constraint exactly_four_ones {
    $countones(data) == 4;
  }
endclass

/*
This uses $countones on the 8-bit data vector and constrains it to 4. The constraint solver will then only produce values of data with exactly four 1 bits.
Non-Adjacent Bits Constraint (No Two 1s in a Row)
Description: Ensures that no two 1 bits are adjacent in a binary vector. In other words, it prevents consecutive 1 bits. One way to express this is by iterating over bit positions and forbidding any position from having a 1 if the previous position also has a 1. This pattern is useful for generating bit patterns with spacing (for example, avoiding back-to-back errors or flags).
Sample Interview Question: "Write a constraint for a 16-bit random variable such that no two consecutive bits are 1."
*/
Solution (SystemVerilog):
class AdjacentBitsExample;
  rand bit [15:0] val;
  constraint no_two_adjacent_ones {
    // No adjacent 1s: for each bit i>0, if previous bit is 1, current must be 0
    foreach (val[i]) if (i > 0) !(val[i-1] && val[i]);
  }
endclass

/*
In this solution, the foreach loop iterates over each bit i of val (except the 0th bit) and ensures that you never have val[i-1] and val[i] both equal to 1 at the same time. An equivalent compact form is ((val & (val >> 1)) == 0), which uses a bitwise trick to ensure no two adjacent 1s exist. This constraint pattern guarantees that any two 1 bits in val will be separated by at least one 0 bit.
Weighted Distribution Constraint (Probabilistic Selection)
Description: Applies a weighted random distribution so that some values occur more frequently than others. The SystemVerilog dist operator allows assigning weights to specific values or ranges. This is useful when certain stimulus values (corner cases, common cases) should appear with different probabilities during randomization.
Sample Interview Question: "We have a 4-bit random variable addr. Write a constraint such that addr takes the value 10 much more often than it takes 7 or 2."
*/
Solution (SystemVerilog):

class DistributionExample;
  rand bit [3:0] addr;
  constraint weighted_addr {
    addr dist { 4'd2 := 5, 4'd7 := 8, 4'd10 := 12 };
  }
endclass

/* 
Here the dist constraint gives addr the value 2 with weight 5, 7 with weight 8, and 10 with weight 12. As a result, addr is most likely to be 10 (highest weight), less likely to be 7, and least likely to be 2. All other 4-bit values not explicitly listed get a default weight of 1 by solver rules. In practice, you would observe addr = 10 occurring more frequently than 7 or 2 in randomizations.
Conditional Constraint (Implication and If-Else)
Description: Constrains a variable based on a condition, effectively creating an "if-then" relationship between random variables. SystemVerilog supports implication constraints using the -> operator to mean if LHS is true, then enforce RHS. It also allows an if...else style within constraint blocks for mutually exclusive conditions. This pattern captures conditional dependencies (e.g., "if X is true, Y must satisfy some condition").
Sample Interview Question: "You have a random field addr_range (string) and an 8-bit addr. Write a constraint so that if addr_range is "small", then addr is less than 8; otherwise addr can be higher."
*/
Solution (SystemVerilog): 
class ConditionalExample;
  rand bit [7:0] addr;
  rand string addr_range;
  constraint range_dependent {
    (addr_range == "small") -> (addr < 8);
  }
  // Alternatively, using if/else inside constraint:
  //constraint range_if_else {
  //  if(addr_range == "small") addr < 8;
  //  else                      addr >= 8;
  //}
endclass


/* In this example, when addr_range is "small", the implication constraint forces addr < 8. If addr_range is anything else, the constraint on addr is not applied (so addr can be any legal value in its range). The commented section shows an equivalent if/else form: if the condition is true, one sub-constraint applies, otherwise an alternate constraint applies. Both forms ensure the conditional relation is honored during randomization.
Inter-Variable Relationship Constraint (Arithmetic Relation)

Description: Enforces a specific arithmetic or relational relationship between two or more random variables. This pattern is used to model dependency like sums, differences, ratios, or ordering between variables. Because SystemVerilog constraints are solved simultaneously (like equations), you can directly write arithmetic expressions involving multiple random vars, and the solver will find values satisfying all such expressions.

Sample Interview Question: "You have two 8-bit random variables a and b. Write a constraint so that their sum is always 255 (0xFF) on randomization."
 */
Solution (SystemVerilog):

class RelationshipExample;
  rand bit [7:0] a;
  rand bit [7:0] b;
  constraint sum_rule {
    a + b == 8'hFF;
  }
endclass

/* 
This constraint makes a and b add up to 255 on every randomization. For instance, if a gets 100, the solver will force b to 155, and so on. Inter-variable constraints can also enforce inequalities (e.g. a < b) or formulas (e.g. b == 2 * a). The solver treats such constraints as mathematical equations linking the variables, solving them simultaneously to find any combination that satisfies all constraints.

Fixed-Size Array Order Constraint (Sorted Array)

Description: Applies constraints across elements of a fixed-size array, often using a foreach construct to impose an order or pattern. A common use-case is to ensure array elements are in ascending or descending order, or follow an arithmetic sequence. All elements are randomizable, but the constraints link them together (e.g., arr[i] > arr[i-1] ensures a sorted order).

Sample Interview Question: "Given an array arr of 10 random 8-bit elements, write a constraint so that the array is strictly increasing (each element larger than the previous one)." */
Solution (SystemVerilog):

class FixedArrayExample;
  rand bit [7:0] arr[10];  // fixed-size array of 10 bytes
  constraint ascending_order {
    foreach (arr[i]) if (i > 0) arr[i] > arr[i-1];
  }
endclass

/* 
Here the foreach (arr[i]) loop iterates over indices and enforces arr[i] > arr[i-1] for all i > 0. This means arr[1] > arr[0], arr[2] > arr[1], and so on, yielding a strictly increasing sequence. The solver will produce a sorted array (e.g., {5, 17, 34, ...} ascending). This pattern can be modified for non-strict order (≥) or descending order (using < instead). It demonstrates constraining relationships among array elements.

Dynamic Array Size and Content Constraint

Description: Constrains both the size of a dynamic array and its elements’ values. Dynamic arrays have a runtime-determined length which can be randomized by treating array.size() as a pseudo-random variable. Common patterns include specifying a range for the array length and then using foreach to impose conditions on each element (such as value ranges, parity, etc.).

Sample Interview Question: "You have a dynamic array data of 4-bit values. Write constraints to randomize its size between 5 and 10, and ensure every element in odd index positions is even."

Solution (SystemVerilog): */

class DynArrayExample;
  rand bit [3:0] data[];  // dynamic array of 4-bit values
  constraint size_and_parity {
    data.size() inside {[5:10]};               // size between 5 and 10
    foreach (data[i]) if (i % 2 == 1) data[i] % 2 == 0;
  }
endclass
/* 

The first constraint uses data.size() to restrict the length of the array from 5 to 10 elements. The second constraint iterates through each element: for every odd index i (i%2==1), it enforces data[i] is even (value mod 2 equals 0). Unconstrained indices (like even positions here) can take any value by default. When randomized, the solver will choose a length in the specified range and assign values fulfilling the parity rule at odd positions. This pattern shows how to handle dynamic arrays by constraining both their size and their content. (Note: You could similarly impose other per-element rules, ranges, or relationships as needed.)

Associative Array Constraint (Size and Keys)

Description: Constrains an associative array’s number of entries and possibly the properties of its keys or values. Associative arrays are indexed by arbitrary key types (e.g., integers, enums). While they don’t have an inherent static size, you can randomize an associative array by constraining its .size() (or .num()) and letting the solver pick distinct keys automatically (keys default to iteration order or enumeration of the index type). You can also use foreach on associative arrays to constrain all existing elements.

Sample Interview Question: "You have an associative array mem of type int -> byte. Write a constraint so that on randomization mem has exactly 4 entries, with each value less than 16."
 */
Solution (SystemVerilog):

class AssocArrayExample;
  rand byte mem[*];  // associative array with int key and byte data
  constraint four_entries {
    mem.size() == 4;
    foreach (mem[ii]) mem[ii] < 16;
  }
endclass
/* 

By constraining mem.size() == 4, we direct the solver to create 4 entries in the associative array. The solver will generate four distinct keys (for an int index, most tools will use 0,1,2,3 as keys by default in such cases) and randomize each corresponding byte value. The foreach (mem[ii]) constraint then ensures every value mem[key] is less than 16 (0x10). After randomization, mem.num() (number of entries) will be 4, and all values will satisfy the constraint. This pattern demonstrates controlling an associative array’s size and uniformly constraining all its elements. (If random key values are needed, one approach is to use an enum or limited-range index type or to generate keys via a separate array, since pure random keys beyond default sequencing may require manual handling.)

Solve-Before Dependency Constraint

Description: Uses the solve ... before ... construct to force the solver to determine one variable’s value prior to another’s. Normally, SystemVerilog’s constraint solver treats relations as bi-directional and gives all solutions equal weight. By specifying solve A before B, you impose an ordering on the solving process: A is effectively chosen first, then B is solved given A. This can alter the distribution of solutions, especially in conditional constraints, to bias certain outcomes.

Sample Interview Question: "In a class with rand bit a; rand bit [3:0] b; there’s a constraint (a == 1) -> (b == 0). By default, a ends up false most of the time. How can you change the constraints so that a being 1 is more likely during randomization?"
*/
Solution (SystemVerilog): 

class SolveBeforeExample;
  rand bit       a;
  rand bit [3:0] b;
  constraint dependency {
    (a == 1) -> (b == 0);
    solve a before b;
  }
endclass

/* 
Originally, without solve before, the solver sees many more solutions where a=0 (since b has 16 possible values when a=0, but only 1 possible when a=1). This biases a toward 0. By adding solve a before b, we tell the solver to pick a first, giving a=1 a fair 50% chance, and then choose b accordingly. In effect, a is no longer overshadowed by the wide range of b. The result is that a will be 1 in roughly half of the randomizations (with b forced to 0 in those cases). This pattern illustrates influencing solver decisions when one variable’s distribution should not be unfairly reduced by another’s range.

Unique Values Constraint

Description: Ensures a set of random variables or array elements all have distinct (non-equal) values. SystemVerilog offers the unique constraint keyword for this purpose. It can enforce uniqueness across multiple scalar variables or across all elements of an array. This pattern is important when generating, for example, a list of unique IDs or ensuring no duplicates in a random stimulus set.

Sample Interview Question: "You have three random 4-bit variables var1, var2, var3. Write a constraint to guarantee that all three get unique values on each randomization."
 */
Solution (SystemVerilog):

class UniqueValuesExample;
  rand bit [3:0] var1, var2, var3;
  constraint all_unique { 
    unique { var1, var2, var3 }; 
  }
endclass
/* 

The unique { var1, var2, var3 } constraint ensures that no two of var1, var2, var3 are the same. For instance, if var1 = 5 and var2 = 5 was a potential solution, the solver would discard it due to the uniqueness rule and find a different combination (such as 5, 7, 2). The unique construct also works for arrays: if these variables were in an array, constraint unique { array }; would ensure all elements are distinct. Under the hood, the solver effectively adds var1 != var2, var1 != var3, and var2 != var3 simultaneously. This pattern is very useful for avoiding collisions or duplicate values in random tests.

Set Membership Constraint (Inside / Not Inside)

Description: Restricts a random variable’s value to be within a given set of values or range, or explicitly outside of a set. The inside keyword is used to specify a set or range of legal values. Conversely, using a negation (or the inside with an exclude) can ensure a value is not in a given set. This pattern is commonly used to model legal opcode values, address ranges, or to exclude invalid codes.

Sample Interview Question: "We have an 8-bit random opcode. Write a constraint so that opcode can only be one of 0x10, 0x20, or 0x30, and not 0x00 or 0xFF."
 */
Solution (SystemVerilog):

class SetMemberExample;
  rand bit [7:0] opcode;
  constraint opcode_legal {
    opcode inside {8'h10, 8'h20, 8'h30};    // allowed set
    opcode != 8'h00 && opcode != 8'hFF;     // or: !(opcode inside {8'h00, 8'hFF})
  }
endclass
/* 

The first line uses an inside constraint to limit opcode to the set {0x10, 0x20, 0x30}. The second line explicitly rules out 0x00 and 0xFF (demonstrating a “not inside” condition – we could also write it as !(opcode inside {8'h00, 8'hFF}) for clarity). With these constraints, on randomization opcode will only ever be 0x10, 0x20, or 0x30. This pattern cleanly defines a whitelist or blacklist of values for a variable. It’s especially useful for encoding limited-choice scenarios (like specific command values) or excluding reserved/illegal values.

Nested Object Constraint (Hierarchical Constraints)

Description: Constrains random variables that belong to a nested object or a class within a class. When you have a rand object as a field of another class, you can impose constraints that reach into the sub-object’s members. This pattern allows hierarchical relationships, e.g., ensuring a sub-object’s field meets a condition that depends on the parent object’s state. All constraints across the hierarchy are solved together. (Similarly, in class inheritance, constraints in a derived class effectively stack with base class constraints, though base constraints can be turned off if needed.)

Sample Interview Question: "Consider a class Engine with a rand int horsepower, and a class Car with rand Engine engine and rand bit sports_mode. Write a constraint such that if sports_mode is true in Car, then the engine.horsepower is at least 300."
 */
Solution (SystemVerilog):

class Engine;
  rand int horsepower;
endclass

class Car;
  rand Engine engine;    // nested random object
  rand bit sports_mode;
  constraint power_req {
    sports_mode -> (engine.horsepower >= 300);
  }
endclass
/* 

In the Car class, we directly reference the nested object’s member (engine.horsepower) in the constraint. The implication (sports_mode -> engine.horsepower >= 300) means whenever sports_mode is 1, the solver must ensure the Engine object’s horsepower is ≥300. Both engine and its field horsepower will be randomized together in one shot. This hierarchical constraint causes the randomization of Engine (a sub-object) to be influenced by Car’s other fields. It illustrates how constraints can span across object boundaries: any rand member of a class, even if it’s an object with its own internal constraints, can be further constrained by the parent class. (Note: One must ensure the sub-object is allocated before randomize; here engine would be constructed before use. Also, if needed, you can disable or override a base object’s constraints via methods like constraint_mode() or using soft constraints in the sub-object.)

Soft Constraint (Default Value Hint)

Description: A soft constraint provides a default or preferred value for a random variable, which can be overridden by other constraints or by explicit randomize-with directives. Declared with the soft keyword, it basically says "try to satisfy this, unless a stronger constraint contradicts it". If no other constraint drives the variable, the soft constraint will be applied; but if there is a conflict or an explicit value is provided, the soft constraint is ignored. This pattern is useful for setting default configurations that tests can override.

Sample Interview Question: "In a packet class, we want the packet length to default to 64 bytes, but still allow testcases to override the length. How would you write such a constraint?"
 */
Solution (SystemVerilog):

class Packet;
  rand int unsigned length;
  // Preferred default length is 64, but it's a soft constraint
  constraint default_len { soft length == 64; }
  constraint valid_len   { length inside {[1:1500]}; }  // for example, valid range
endclass
/* 

Here soft length == 64 sets a default target value. If nothing else influences length, the solver will choose 64 (assuming it also meets other constraints like valid_len). However, if another constraint or a with clause in randomize() specifies a different length, the soft constraint yields and does not produce a conflict. In practice, when you randomize Packet as-is, you’ll get length = 64 almost every time (since the soft constraint is the only guidance besides range). But a test can do pkt.randomize() with { length == 100; } and that will succeed, effectively overriding the default. Soft constraints thus act as tunable default values, providing flexibility in stimulus generation. Only one soft constraint will apply if no stronger constraint contradicts it, making them ideal for default settings or "suggestions" to the solver.

Random Cyclic Constraint (No Repetition until Cycle)

Description: Uses randc (random-cyclic) variables to ensure all possible values are iterated through before any value repeats. This isn’t a constraint in the usual sense, but a property of the random variable itself. A randc variable will cycle through its entire value range (or specified subset via constraints) in random order without repetition, which is useful when you need to exhaustively use values (like unique IDs, or all packet types) before reusing them. One caveat: randc variables are always solved before regular rand variables (they have an implicit highest priority in solving).

Sample Interview Question: "How can you ensure a 3-bit random field cycles through all values 0–7 without repeating any value until all have been used?"
 */
Solution (SystemVerilog):

class RandcExample;
  randc bit [2:0] field;
  // (Optional: you can still add constraints, e.g., to skip some values if needed)
endclass

/* 
Declaring field as randc achieves the requirement. For a 3-bit randc variable, the first 8 randomizations will produce a permutation of 0 through 7 (each value exactly once in some random order). Only on the ninth randomization will it start cycling again (and even then, it will go through 0–7 in a new random permutation). The solver internally keeps track of used values for each randc until the set is exhausted. This pattern is powerful for generating sequences without repetition. For example, if you randomize 10 times, you might see outputs like: 6, 3, 4, 7, 0, 1, 5, 2, 5, 0 – note how 5 and 0 only appear again after all 0–7 were seen once. randc variables can be combined with constraints (except solve before is not allowed on them, since they inherently solve first). This feature guarantees coverage of all values in cycles, which is useful in certain verification scenarios requiring exhaustive stimulus.

Constrained Value Change Across Calls (Limited Reuse)

Description: Imposes a relationship between successive randomization calls, typically by referencing the previous value to constrain the current value. While each randomize() call generally has no memory of the last, you can achieve cross-call constraints by storing the last value (for example, in a static class property or an external variable) and using it in a constraint. This pattern is used to limit how much a value can change between cycles or to avoid immediate repetition of values. (It often requires a pre_randomize or post_randomize hook to update the reference of the "previous" value.)

Sample Interview Question: "You have a 32-bit random variable that changes every cycle. Write a constraint so that on each new randomization, the new value differs from the previous value in exactly 2 bit positions."
 */
Solution Concept:

class LimitedChangeExample;
  rand bit [31:0] cur_val;
  static bit [31:0] prev_val;
  // Only allow exactly 2 bits to flip relative to prev_val:
  constraint two_bit_flip {
    (prev_val ^ cur_val).countones() == 2;
  }
  function void pre_randomize();  
    // Update prev_val to current before next randomization
    prev_val = cur_val;
  endfunction
endclass

/* 
In this approach, prev_val holds the previous random value (declared static so it persists across randomize calls). The constraint uses the XOR (^) between the previous and current value and counts the 1 bits in the result, forcing that count to be 2. In other words, exactly two bits differ between prev_val and cur_val. The pre_randomize() function is used to set prev_val to the last generated cur_val before each new randomization, so that the constraint always compares to the most recent value. This pattern allows controlled evolution of a random stimulus over time – here limiting bit flips to two per cycle. It can be adapted to other forms (e.g., prev and cur must not be equal, or must differ by at most N bits, etc.). Note that some simulators provide a const() cast to capture the pre-randomization value without a static, but using a stored static variable is the clearer approach. The end result is a sequence of random 32-bit values where each consecutive pair differs in exactly two bit positions, as required. */