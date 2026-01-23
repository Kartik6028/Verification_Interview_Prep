/* SystemVerilog Temporal Assertion Patterns (Testbench Level)

SystemVerilog concurrent assertions (SVA) allow checking temporal behaviors in verification testbenches. Below is a comprehensive list of common temporal assertion patterns, organized by category. Each pattern includes a clear name, description of the behavior it checks, and an example SVA code or template. (All examples assume a clock clk for sampling and use assert property on that clock, with resets or conditions handled via disable iff as needed.)

Response Patterns

1. Request-Acknowledge (Unbounded Response): Ensures that whenever a request event occurs, a corresponding acknowledge event will eventually occur at some later time (no fixed upper bound on delay). This captures a liveness property that an ack always follows a request. For example, if req goes high, ack must happen sometime after (even if many cycles later). In SVA, an unbounded delay can be coded with ##[1:$], meaning “after at least 1 cycle, eventually (no limit)”.
 */
// If req asserted, ack will occur eventually (after at least 1 cycle)
assert property (@(posedge clk) req |-> ##[1:$] ack);

/* 
This property spawns a check whenever req is true; the use of ##[1:$] means it will look arbitrarily far in the future for an ack. If no ack ever occurs after the request, the assertion will fail. (In practice, unbounded waits are often avoided or accompanied by a timeout, below.)

2. Bounded Response (Latency Limit): Ensures the responding event comes within a fixed number of cycles, enforcing an upper latency bound. For example, “A Request should be followed by an Acknowledge occurring no more than two clocks after the Request is asserted.”. This pattern catches situations where the response is missing or too slow.
 */
// If req asserted, ack must be seen 1, 2, or 3 cycles later (within 3 cycles)
assert property (@(posedge clk) req |-> ##[1:3] ack);

/* 
In this example, if req is high, ack must go high in 1 to 3 cycles after the request. If ack doesn’t arrive by the 3rd cycle, the assertion fails. (Adjust the range 1:N for other latency bounds as needed. For instance, ##[1:4] would allow 1 to 4-cycle latency.)

3. Immediate (Next-Cycle) Response: A special case of bounded response with a 1-cycle window. It ensures the response happens in the next clock after the trigger. For example, if a grant signal should be acknowledged on the very next cycle, we assert req |-> ##1 ack. This pattern is useful for strict pipeline handshakes or lockstep events:
 */
// If req asserted, ack must assert in the next clock cycle
assert property (@(posedge clk) req |-> ##1 ack);

/* 
If ack is not high on the cycle immediately following a req, the assertion will fail. (Use the non-overlapping implication operator |=> instead of |-> if you prefer to explicitly start checking from the next cycle.)

4. Absence of Response (Negative): It’s also possible to assert that a response does not occur within a certain window, by asserting the negation of a sequence. For instance, to ensure an ack never comes too early (e.g. not in the same cycle as the request), one can forbid that sequence. This is covered under Latency Bounds and Forbidden Patterns below (ensuring minimum latency).

Forbidden Sequence Patterns

These patterns forbid illegal sequences of events – the assertion fails if the undesired sequence ever occurs. In SVA, this is done by asserting the negation of the bad sequence.

1. No Double Request without Ack: Forbids a second request from occurring before the first request’s acknowledge has happened. In other words, once a req is asserted, there must not be another req until after an ack. This pattern prevents two back-to-back requests that would violate a request/ack handshake (commonly phrased as “no new request until previous request is acknowledged”). We can express this by saying if a request occurs, then until an ack occurs, there should be no further request. For example:
 */
// Illegal sequence: a req followed by another req before an ack in between
assert property (@(posedge clk) not (req |=> !req[*0:$] ##1 req) );


Here, (!req)/* [*0:$] ##1 req describes “another req eventually, with no req in between (only possible ack or idle cycles)” – effectively two req events in the same outstanding transaction. Wrapping not(...) around it asserts this sequence never happens. If a second req does occur before seeing an ack, the inner sequence will match and the outer not(...) will make the assertion fail. (This check addresses the no back-to-back req requirement.)

Variation: If the protocol specifically forbids consecutive cycle requests (no two req high in adjacent cycles), a simpler assertion can be used: assert property(@(posedge clk) not (req && $past(req))); – this fails if req is true in two successive cycles.

2. No Acknowledge without Request: Forbids an ack from occurring spontaneously when there was no request pending. In a well-formed handshake, the ack signal should only be asserted in response to a prior req. We can check that there isn’t an ack with “no preceding req.” One approach is to assert that it’s never the case that ack occurs after a period of absolutely no req activity leading up to it:
 */
// Illegal sequence: ack happening without any prior req
assert property (@(posedge clk) not ( (!req)[*0:$] ##1 ack ));


T/* his property says “it is never true that we have some interval of no req at all and then an ack.” In other words, whenever ack happens, there must have been a req at some point before it (the sequence (!req)[*0:$] ##1 ack would match if an ack appears with no request ever in the prior cycles, which we forbid). This captures the idea “the server shall not provide an ack signal without receiving a req signal.” If an ack does occur out of the blue (with no prior request in the simulation up to that point), the assertion fails.

Variation: In cases where the protocol allows multiple requests and acks (tagged or pipelined), a more precise check would tie each ack to a specific request (often by tracking IDs or using auxiliary state). But the above generic form is useful for simple one-to-one handshakes.

3. Other Forbidden Sequences: You can forbid any disallowed temporal pattern using the same “not (sequence)” structure. For example, if it’s illegal for a Done signal to occur before a Grant signal, one could assert not (done ##1 grant) to catch a done followed (next cycle) by grant sequence. Similarly, mutual exclusions like never assert X and Y in the same cycle are a forbidden condition (see Stability/Invariance patterns). The key is identifying any sequence of events that should never happen in a correct design and writing an assertion as its negation.

Handshake Protocol Patterns

These patterns combine multiple checks to verify a typical request/acknowledge handshake or similar protocol. A handshake usually involves a requestor and a responder signal with certain rules. Below are common handshake-related patterns:

1. Persistent Request Until Ack: Once a request is made, it should remain asserted (stay high) until the acknowledge is received. This applies to handshakes where req is a level signal (not just a one-cycle pulse). The client must hold req=1 until the server drives ack=1. We can assert that req doesn’t drop prior to ack:
 */
// If req goes high, it stays high until ack is observed
assert property (@(posedge clk) $rose(req) |=> req[*1:$] ##0 ack);

/* 
This uses $rose(req) to trigger on the rising edge of req, then req[*1:$] ##0 ack says that from the next cycle onward, req must continuously stay high until an ack occurs in the same cycle as it eventually (the ##0 concatenation means ack coincides with the last cycle of the req sequence). In effect, ack must arrive while req is still asserted. If req deasserts (goes low) before ack comes, the sequence fails and so does the assertion. This pattern ensures the request isn’t prematurely withdrawn. (It’s a formalization of “client waits for ack and doesn’t drop req until handshake completes.”)

2. Acknowledge Response (Timing and Presence): This is the basic request-acknowledge response pattern, covered in Response Patterns above. In a handshake context, typically there’s a maximum wait time: e.g. ack must arrive within N cycles after req and not in the same cycle as req. For example, a property req |-> ##[1:5] ack means if req is asserted, ack must follow 1 to 5 cycles later. Often an additional check ensures ack is not combinatorial in the same cycle (in SVA, you can insert !ack immediately after req in the sequence to ensure they don’t overlap). For instance:
 */
// Handshake: req -> ack within 1 to 5 cycles (not in same cycle as req)
assert property (@(posedge clk) $rose(req) |-> !ack ##[1:5] $rose(ack));
/* 

This assertion triggers on a rising edge of req and requires that ack goes high 1 to 5 cycles later (and ack was low at the request time). If no ack arrives in that window, the handshake timed out (assertion fails).

3. No New Request During Handshake: The requestor should not issue another request while one is still pending (i.e. before the ack). This is essentially the No Double Request pattern described earlier, but it’s an integral part of handshake protocols. For clarity, one can write: if req is high, it should not go high again until after an ack. For example:
 */
// Once req is asserted, it cannot assert again before ack (no overlap of handshakes)
assert property (@(posedge clk) req |=> !req[*1:$] ##1 ack);

/* 
This uses a non-overlapping implication: when req happens, from the next cycle until an ack occurs, req must remain false. In other words, between a request and its acknowledge, req is not allowed to re-assert. This prevents overlapping or back-to-back handshakes. If a second req occurs before the ack, the sequence !req[*1:$] ##1 ack is violated and the assertion fails. (This aligns with the rule that a client “shall not assert another req while waiting for ack.”)

4. No Ack Without Request: The responder should not assert ack unless a request is active or pending. This was described in Forbidden Patterns, but in a handshake context it ensures the server only responds when there is a valid request. A simple check is that whenever ack is high, there should be a current or recent req. If req is a persistent level, one can require ack implies req is high at the same time (e.g. assert property (ack |-> req); for overlapping implication, meaning ack can only occur when req is asserted). If req is a pulse, one might instead track that a request has occurred in the recent past. For example, one could set a flag when req is seen and clear it on ack, then assert ack |-> past_req_flag. Conceptually, we ensure “server’s ack must correspond to a prior req”. If an ack is ever observed with no corresponding request context, it’s a failure.

5. Single-Cycle Pulse Handshake Signals: Often handshakes use pulses (one-clock assertions) for req and/or ack. Two common patterns are: Req is a one-cycle pulse and Ack is a one-cycle pulse. These are stability checks on those signals: if they go high, they should go low on the very next cycle (no lingering high). For example, to ensure req is a single-cycle pulse:
 */
// Request pulse: if req is high, it goes low on next cycle
assert property (@(posedge clk) req |=> !req);
/* 

And similarly for ack being one-clock wide: */

// Ack pulse: if ack is high in one cycle, it must be low in the next cycle
assert property (@(posedge clk) ack |=> !ack);

/* 
These use non-overlapping implication so that if the signal is 1 at a clock edge, the next sampled value must be 0. The example above corresponds to the rule “the server sets the ack signal for one pulse.” If either req or ack stays asserted for more than one cycle (when we expected a pulse), the assertion will fire. (If pulses are expected to be a specific width other than one cycle, see Repetition Patterns for how to enforce a minimum or maximum width.)

6. Four-Phase Handshake (Request/Ack De-assertion Ordering): In a four-phase handshake (common in asynchronous protocols), after req is asserted and ack is asserted in response, both must eventually return to zero (handshake complete) before the next cycle. One can write assertions to ensure the de-assertion ordering: e.g. req should drop after ack is seen, and ack should drop after req has dropped. For instance, assert that once ack is high, req goes low by the next cycle, and that once req goes low, ack goes low by the next cycle. In SVA:
 */
// Handshake completion: req must drop within 1 cycle after ack, and vice versa
assert property (@(posedge clk) $rose(ack) |-> ##[1:1] $fell(req));
assert property (@(posedge clk) $fell(req) |-> ##[1:1] $fell(ack));
/* 

These ensure the handshake is properly cleared (no “stuck” signals). This pattern might vary depending on the exact protocol (some require ack to drop only after req drops, etc.). It’s included for completeness in complex protocols.

(In summary, handshake protocols often require a combination of the above patterns: a bounded response time, single-cycle or persistent signaling, no re-assertion until complete, and proper de-assertion ordering. By composing multiple assertions, one can fully specify the handshake behavior.)*

Ordering and Precedence Patterns

These patterns enforce that certain events occur in a specified order or that one event cannot happen before another. They address scenarios like initialization sequences, protocol ordering, or causality requirements.

1. Precedence Constraint (Event B after Event A): Ensures that an event B never occurs until event A has occurred previously. In other words, A must always happen before B. A typical example is requiring a system to be initialized before any operations: e.g. a signal init_done must be true at least once before any oper_start can happen. One way to assert this is to forbid the scenario where B occurs without A having happened. We can say: it is never the case that we have had no A and then see B. In SVA:
 */
// B cannot occur before A has occurred at least once
assert property (@(posedge clk) not( (!A)[*0:$] ##1 B ));

/* 
Here (!A)[*0:$] ##1 B describes a sequence where for some stretch (possibly from time 0), A is false throughout and then a B happens. By asserting the negation of that, we ensure that any time B happens, the sequence “no A until B” was false – meaning there must have been an A at some point prior to B. This effectively enforces that A precedes B (B is only allowed after A). If a B event occurs without a prior A, the forbidden sequence matches and the assertion fails.

2. Immediate Precedence (B directly follows A): Sometimes we require that whenever event A happens, event B must occur immediately after (in the next cycle). This is a stricter ordering: no other events in between. For example, if an instruction decode (decode) must be followed in the next cycle by issue (issue), we assert: decode |-> ##1 issue. Or, to phrase as B immediately after A: whenever A occurs, B occurs in the next time step. In code:

// If A event occurs, B must occur in the very next cycle */
assert property (@(posedge clk) A |-> ##1 B);

/* 
This uses overlapping implication (|->) with a one-cycle delay to state the next-cycle requirement. If B does not follow on the next clock, the assertion will fire. (This pattern is akin to a pipeline stage completion or a request followed by an immediate action.)

3. Causal Ordering (If A then eventually B, and if B then previously A): This is a combination of response and precedence ensuring a cause-effect relationship. For instance: “Every request is eventually followed by a done, and any done implies a request happened before it.” You would use a Response pattern for the first part and a Precedence pattern for the second. This ensures not only that A leads to B, but also that B doesn’t occur out of context of A. In SVA, you could write both: A |-> ##[1:$] B (response) and not((!A)[*0:$] ##1 B) (precedence). Together, they guarantee ordering in both directions (B cannot happen without A, and A eventually triggers B).

4. Strict Order of Multiple Events: For sequences of more than two events that must occur in order (e.g., X then Y then Z in that order), one can break it down into pairwise orderings or write a single sequence. For example, require that whenever X occurs, eventually a Y occurs, and after that eventually a Z occurs. A single property could be: X |-> ##[1:$] Y ##[1:$] Z; which means if X, then later Y and later Z in that sequence. Another approach is to assert no reordering: forbid Y happening before X, and Z happening before Y. E.g., not((!X)[*0:$] Y) and not((!Y)[*0:$] Z). This way, you ensure X precedes Y and Y precedes Z. These patterns are useful for enforcing protocol phases in order.

(In general, precedence patterns ensure a certain event has occurred prior to another. They are often implemented by forbidding the “bad” order (no A before B) as shown above. Conversely, response patterns ensure the forward direction (A leads to B). Combining both yields a strong ordering guarantee.)

Stability and Invariance Patterns

Stability and invariance patterns check that certain conditions hold steady – either some signals remain stable under specified conditions, or some boolean invariants are always true. These are essentially safety properties that must hold at all times or for a duration.

1. Mutual Exclusion (Invariance): Ensures two (or more) signals are never asserted at the same time. This is an invariant condition that holds in every cycle. For example, if Read and Write should never be 1 simultaneously (perhaps because a bus cannot be read and written at once), you assert that the expression !(Read && Write) is always true. In SVA (concurrent assertion), this can be as simple as:

// Mutual exclusion: Read and Write are never high together */
assert property (@(posedge clk) !(Read && Write));

/* 
Because the antecedent here is just a boolean (no sequence), the assertion effectively checks on every clock that not(Read and Write) is true. If both signals go high in the same cycle, the expression is false and the assertion fails. You can extend this to more than two signals (e.g., no two masters request the bus at the same time, etc.) by combining conditions accordingly.

2. One-Hot Encoding: A special case of mutual exclusion for a group of signals, where exactly one is high (or at most one, depending on definition). One-hot means out of a set of N signals, one and only one is 1 at any given time. An assertion for one-hot can be written as an invariant using a boolean check or using a system function. For example, for signals a, b, c being one-hot:

// One-hot: exactly one of a, b, c is 1 at any time */
assert property (@(posedge clk) $onehot({a,b,c}));


/* The $onehot system function returns true if exactly one bit of the vector is high. If the design requires “one-hot or all-zero” (allowing the case of none asserted), one could use $onehot0 instead. Alternatively, without system tasks, one could assert (a + b + c == 1) for single-hot (if they are single-bit signals) or use pairwise exclusion and at least one high: e.g. !(a&&b || a&&c || b&&c) (no two high at once) and (a||b||c) (at least one high).

3. Signal Stability (No Glitch) Under Condition: Ensures a signal remains stable (does not change) during a certain condition or time period. For instance, a common requirement in pipelined or handshake protocols: data must remain stable while valid is high until ready is asserted. In other words, if a data bus is presented with valid, it shouldn’t change until the receiving side ready comes. We can assert that when valid is 1 and no handshake complete yet (!ready), the data stays the same from cycle to cycle. Using the $stable() function:

// Data stability: when valid is asserted (and before ready), data remains constant */
assert property (@(posedge clk) (valid && !ready) |-> $stable(data));

/* 
This says if at a clock edge valid is 1 and ready is 0 (meaning we have a pending valid data that’s not yet accepted), then in the next cycle the data must be the same as it was (and this continues as long as the antecedent holds true). Essentially, as long as valid && !ready remains true, $stable(data) must hold each cycle, preventing any change. If data changes before ready goes high, the assertion fails, catching the protocol violation (as described, “Data should remain stable while valid is high until ready is asserted.”).

Variation: Another way to express this is using implication across a delay: assert property((valid && !ready) |=> data == $past(data)); which checks that one cycle later the data is unchanged whenever the condition was true. The form above with $stable is more succinct. This pattern is crucial for ensuring no glitches or unintended updates to signals that are supposed to stay constant during a transaction.

4. Constant Invariance: A simpler invariance is that certain signals should never change value after initial configuration or should remain constant during certain modes. For example, if a configuration bit cfg_mode should not toggle after reset, one could assert $stable(cfg_mode) globally or after an initial phase. Similarly, if a FIFO’s depth must never exceed a limit: assert property(depth <= MAX_DEPTH); at all times. These are straightforward invariants (they either hold or not in each cycle).

5. No Unexpected Transition: Stability patterns can also ensure that certain forbidden transitions don’t occur. For example, if a state machine should not transition directly from State1 to State3 (skipping State2), you could write an assertion on state changes that flags an illegal jump. E.g., assert property(@(posedge clk) state == S1 |-> ##1 state != S3); meaning if we were in S1, we shouldn’t be in S3 on the next cycle (thus requiring going through S2 or others in between). This is an invariance over transitions.

(Overall, stability checks often use $stable(signal) or equality with $past(signal) to ensure no change, and invariance checks use boolean conditions that must hold every cycle. They catch glitches, multi-cycle pulse requirements, and general “always” conditions of the design.)

Sliding Window Constraints

Sliding window patterns constrain events within any sliding time window of a given length. They can enforce minimum or maximum frequencies of an event, such as “at least one event every N cycles” or “no more than M occurrences in N cycles.” These are useful for watchdog timers, throughput limits, or spacing requirements.

1. Event Must Happen Regularly (Watchdog/Liveness): Ensures that an event occurs at least once within every N cycle window – i.e., you never go N consecutive cycles without seeing the event. This can detect if an expected periodic or frequent event stalls. One way to assert this is to forbid a sequence of N cycles with no event. For example, “The signal heartbeat should toggle at least once every 100 cycles” can be checked by asserting that you never have 100 cycles of it being idle. If event is a Boolean that is true when the event occurs (pulse), then (!event)[*N] is the sequence of N cycles of no event. We write:
 */
// Never go N cycles without the event occurring at least once
assert property (@(posedge clk) not( (!event)[*N] ));
/* 

This assertion will fail if there is any interval of N consecutive clock cycles during which event remains false (meaning no occurrence). In practical terms, it guarantees within any span of N cycles, at least one event happened. This is a classic watchdog pattern.

Example: If a “kick” signal should occur at least every 100 cycles to reset a watchdog, use N=100. If the simulation ever sees 100 ticks with kick low throughout, the assertion fires.

2. Minimum Spacing Between Events: Ensures that once an event happens, it doesn’t happen again too soon – enforcing a cooldown period. For example, “no two requests within 3 cycles” (meaning at least 3 cycles gap between any two req pulses). We can assert that if event happens, it will not happen again for the next M cycles. In SVA:
 */
// After an event, the event is prohibited from re-occurring in the next M cycles
assert property (@(posedge clk) event |=> !event [*M]);

/* 
Using non-overlapping implication, when event is true, the consequent !event[*M] requires the event to stay false for M cycles after. For instance, if M=2, and an event occurs at cycle t, this asserts that event is false at t+1 and t+2 – so the earliest next event can be at t+3. This pattern is useful to enforce things like no back-to-back operations, bus turnaround times, or rate limiting. If another event occurs too early (inside the forbidden window), the sequence is violated and the assertion fails.

3. At Most M Events in N Cycles: Limits the frequency so that in any window of N cycles, you see no more than M occurrences. This is essentially a generalized rate limit. SVA can express simple cases; for instance, “at most one event every N cycles” is the M=1 case covered by the spacing pattern above. For M > 1, one approach is to construct a sequence that describes M+1 events in N cycles and forbid it. For example, “at most 2 events in 5 cycles” – you would forbid seeing 3 events within some 5-cycle span. This can be done with a sequence like: event ##[1:$] event ##[1:$] event constrained to a total length of 5 or fewer cycles. Writing such sequences can get complex; sometimes a small checker or a saturating counter in SystemVerilog may be simpler. But conceptually, you might do:
 */
// Example: Forbid more than 2 events in any 5-cycle window (no 3 events in 5 cycles)
assert property (@(posedge clk) not ( event ##[1:4] event ##[1:4] event ));

/* 
This sequence attempts to match three occurrences of event separated by up to 4-cycle gaps (so that the total span is at most 5 cycles from first to last). Wrapping not(...) ensures the simulation will fail if it ever finds such a rapid trio of events. By adjusting the counts, you can target different M-in-N limits.

4. Windowed Sum/Count Invariants: Another way to enforce limits in a sliding window is by using auxiliary counters or $countones with a moving window. For example, one could track a running count of events in the last N cycles and assert it’s ≤ M. This often requires some additional modeling (like shifting register or using $past N times). In formal verification, PSL’s “suffix implications” or SVA’s strong abort and [*] can sometimes encode it, but it can be advanced. For learning purposes, understanding the simpler patterns above covers most needs (watchdog and spacing).

(Sliding window checks ensure activity or inactivity constraints over time. They are particularly useful for performance verification, ensuring a design meets minimum throughput (no long idle gap) and maximum throughput (no burst beyond limit).)

Latency Bound Patterns

Latency patterns enforce explicit timing bounds between cause and effect events – both maximum (deadline) and minimum (earliness) latency constraints.

1. Maximum Latency (Deadline): This is the same as the Bounded Response pattern earlier, but emphasizing the deadline aspect. It ensures the effect happens within N cycles of the cause. For example, “If a START signal is asserted, a DONE signal must assert within 10 cycles”. SVA:
 */
// Max latency: DONE must go high 1 to 10 cycles after START
assert property (@(posedge clk) START |-> ##[1:10] DONE);
/* 

If DONE doesn’t appear by 10 cycles after a START, the assertion will fire (the sequence fails after the 10th cycle passes with no DONE). This pattern is common for real-time checks or protocol timeouts. We cite the previous example of ack within 4 cycles or 5 cycles as a typical usage.

2. Minimum Latency (No Earlier Than): Ensures the effect does not happen too soon after the cause – i.e., there’s a required minimum delay. This prevents unrealistic or out-of-order early responses. For instance, maybe an operation always takes at least 3 cycles to complete, so DONE should not assert until 3 or more cycles after START. We can assert that any occurrence of the effect before the minimum time is illegal. One way is to directly require the delay in the implication:

// Min latency: DONE should occur only after at least 3 cycles of START */
assert property (@(posedge clk) START |-> ##[3:$] DONE);

/* 
Here ##[3:$] means the first opportunity for DONE to satisfy the sequence is 3 cycles after START (or any time later) – effectively mandating at least 2 full cycles of delay in between. If DONE happens at 1 or 2 cycles after START, the property will not be fulfilled (it will keep waiting for a later DONE which may never come, resulting in failure). Another way is to forbid any early appearance of DONE: e.g. assert property( not (START ##[1:2] DONE) ); would flag a failure if a DONE showed up 1 or 2 cycles after a START. By ruling out the disallowed early windows, you enforce the minimum latency.

3. Exact Latency: In some cases, you expect an event to occur exactly N cycles after another. For example, if a pipeline is fixed-length: “Instruction issue is followed by writeback 4 cycles later exactly.” You can combine a minimum and maximum in one ##[N:N] delay. E.g.:

// Exact latency: B occurs exactly 4 cycles after A */
assert property (@(posedge clk) A |-> ##[4:4] B);
/* 

This will only pass if B happens precisely 4 clocks after A (no earlier, no later). If B occurs at a different time or not at all, the assertion fails. This pattern is useful for deterministic latency components (like fixed pipelines, bus delays, etc.).

(Latency patterns essentially mirror the response patterns but highlight timing requirements: a maximum latency is a safety deadline, and a minimum latency is a safety spacing. Both can be critical in protocols like memory access timing, bus turnarounds, or any time-critical logic.)

Event Filtering and Conditional Assertions

Sometimes we only want to check an assertion under certain conditions or we want to filter out irrelevant events. SVA provides mechanisms like conditional enabling, edge triggers, and disable conditions for this.

1. Reset/Idle Filtering (disable iff): It’s common to disable assertions during reset or when the system is idle. The disable iff (<cond>) clause in an assertion causes it to not evaluate (be vacuous) when <cond> is true. For example, to ignore assertion checks during an active-low reset signal rst_n being 0:
 */
// Example: disable the property during reset (rst_n==0)
assert property (@(posedge clk) disable iff (!rst_n) req |-> ##[1:4] ack);

/* 
Here, if rst_n is low (reset active), the implication req |-> ack is turned off. The assertion will simply not check or report failures in reset. This pattern is important to avoid false failures on reset or power-up conditions when signals might be in undefined states. Always include appropriate disable iff for resets or any global condition where the property shouldn’t apply.

Likewise, you can disable when a device is in an idle mode. For instance, disable iff (!enable) would make the assertion only active when enable is true. This is effectively a conditional qualification on the entire property.

2. Conditional Antecedent (Only Check When...): Another way to only check under certain conditions is to include the condition in the antecedent of an implication. For example, “whenever mode=1, then signal X must be 0” can be written as mode |-> (X==0). This means if mode is not 1, the implication antecedent is false and the property holds vacuously – so it only matters in cycles where mode is 1.

Similarly, “if error_flag is set, an interrupt must occur within 3 cycles” could be: error_flag |-> ##[1:3] intr. This will only trigger the timing check when error_flag is high, otherwise do nothing.

3. Edge-Based Event Filtering ($rose, $fell): Using edge-detection functions in assertions helps to filter out continuous assertions. For example, using $rose(signal) as the antecedent will only spawn the property when the signal transitions from 0 to 1, rather than for every cycle the signal is high. This is important for performance and correctness: it avoids creating multiple parallel threads for a sustained high signal. A pattern example:

// Only trigger when 'req' rises, not on every cycle of being high */
assert property (@(posedge clk) $rose(req) |-> ##[1:5] $rose(ack));

/* 
Here, $rose(req) filters the check to only the moment of the rising edge, so we don’t start a new “req implies ack” check on every clock when req remains high. This is a form of event filtering that ensures we only react to the event’s edge. It’s particularly useful in handshake patterns (to only react to the first cycle of req asserted) and any scenario where a level could be true for multiple cycles but you only want to respond once.

Using $fell(signal) similarly can trigger a property on a falling edge. The general pattern is: use $rose(sig) or $fell(sig) in the antecedent to treat changes as discrete events and ignore steady-state.

4. Conditional Sequences and Gating: You can also conditionally start sequences with an initial if: for instance, if condition C holds, then sequence S must hold. This is effectively C |-> S as noted. Another feature is the and/or operators on properties which can combine conditions. For example, to assert a property only in a certain state, you might do: assert property(@(posedge clk) state==IDLE or P); meaning either we are in IDLE state (so we don’t require P), or if not, then property P must hold. However, this can often be simplified with disable iff or implication as above.

5. Ignoring Irrelevant Cycles: Sometimes you want to filter out cycles where an enable is low – i.e., the property should effectively skip those cycles. This can be done by incorporating the enable into the sequence using [*0:$] repetition. For instance, “when valid goes high, within 3 cycles of some subsequent ready” might need to ignore cycles where ready is low. Advanced constructs like [*] intersect or first_match exist, but typically it’s easier to restructure the sequence or use an implication conditioned on the relevant signal.

(In summary, event filtering and conditional assertions allow you to tailor when assertions are active. Use disable iff for broad off conditions like reset, incorporate mode conditions in antecedents for context-specific checks, and use $rose/$fell to treat signals as discrete events rather than levels. These techniques prevent false failures and reduce performance overhead by focusing on the meaningful scenarios.)

Sequence Combination Patterns (Overlapping vs. Non-Overlapping)

SystemVerilog allows combining sequences in time, and the implication operator comes in two flavors: overlapped (|->) and non-overlapped (|=>). Understanding and using these correctly is itself a pattern, since it dictates whether sequences can overlap or must occur in strict order.

1. Overlapping Implication: The consequent sequence can start in the same cycle that the antecedent succeeds. This is useful when the trigger and response can coincide or you want to allow parallel behavior. For example, A |-> B (with no delay) means if A is true in a cycle, B must also be true in that same cycle. More generally, if the antecedent is a multi-cycle sequence, the consequent begins at the first cycle of the antecedent. Overlapping is typically used when you want to check things during an ongoing sequence or immediately at its start.

Example: In a bus protocol, “if a read command is issued, the read acknowledge may even happen in the same cycle” – you would use overlapped implication to allow that: read_cmd |-> read_ack (no delay, so ack can be concurrent with cmd if the design allows). Overlap is also used with delays: e.g. A |-> ##2 B means B is two cycles after A, counted from the time A started (not after A finished if A is multi-cycle). Overlapped is the default implication used in many patterns unless you specifically need to wait for the antecedent to finish.

2. Non-Overlapping Implication: The consequent sequence starts after the antecedent sequence has fully completed. Denoted by |=>, it ensures no overlap in time between antecedent and consequent. If antecedent is a single-cycle event, |=> means the consequent begins the next cycle. If antecedent is a multi-cycle sequence, |=> begins the cycle after that sequence ends. This is useful when the occurrence of the antecedent must finish before the next part begins – e.g., one transaction must complete before the next starts.

Example: A |=> B means if A is true in one cycle, then B must be true in the following cycle. Or if A is a 4-cycle-long sequence, |=> C means sequence C should start at the cycle after those 4 cycles. Non-overlapping implication is often used for pipeline stages (where one stage’s end triggers the next stage’s beginning on the next clock) or when combining sequences without interference.

Difference Illustrated: If A is just a boolean condition, A |-> B checks B in the same clock as A, whereas A |=> B checks B one clock later. For example:
 */
// Overlapped vs Non-overlapped simple example:
assert property(@(posedge clk) req |-> ack);
// (If req is 1 this cycle, ack must be 1 in this **same** cycle)

assert property(@(posedge clk) req |=> ack);
// (If req is 1 this cycle, ack must be 1 in the **next** cycle)
/* 

Overlapping might not make sense in this particular case (because if req and ack are sampled at the same time, req|->ack essentially says req implies ack combinatorially in that cycle), but it shows the semantic difference. In practice, one uses overlapping vs non-overlapping based on protocol behavior. For instance, in a synchronous handshake where ack is combinatorially dependent on req, you might use |->. But if ack is registered and only comes later, |=> or an explicit delay is appropriate.

3. Sequence Fusion (##0) and Intersection: Another combination is concatenating sequences with zero delay (##0) which effectively overlaps the end of one sequence with the start of the next in the same cycle. This is used to merge sequences or add a simultaneous condition. For example, seq1 ##0 seq2 means seq1 and seq2 share the same ending cycle (they finish at the same time). The and (or intersect) operator requires two sequences to hold true over the same time span. These are advanced, but one pattern use is: if you want to ensure two conditions hold concurrently for a number of cycles, you can intersect them. For example, (!req[*1:$] intersect ack[->1]) seen in some code means ack eventually, and until then !req holds, combining the two requirements in one sequence.

4. Overlapping Instances of a Sequence: Sometimes you need to allow (or disallow) overlapping occurrences of the same sequence. For example, if two transactions can be in flight, an assertion might need to handle overlapping sequences. By default, concurrent assertions will spawn a new thread for each time the antecedent is satisfied, even if a previous one is still in progress. If overlapping occurrences are allowed by design, the assertion should be written to accommodate that (often by using $rose to spawn only on distinct edges, or by structuring the sequence so that a new start can happen before the old one ended). If overlapping occurrences are not allowed, then an assertion like the “no double request” pattern already prohibits a new start before the old one’s ack.

In summary, overlapping vs non-overlapping is about whether the consequential sequence starts in parallel with or strictly after the antecedent sequence. They are denoted by |-> (overlap) and |=> (non-overlap) respectively and are a key part of combining sequences. Use |=> when you need a clean separation in time, and |-> (the default choice) when the consequence can be checked immediately or concurrently.

(As a tip: many authors stick to |-> for most properties and insert explicit delays as needed, since any non-overlapped implication A |=> B is equivalent to A |-> ##1 B in many cases. But understanding the difference is crucial when antecedent is multi-cycle. Always choose the one that matches your intended timing.)

Repetition and Counting Patterns

These patterns leverage SVA’s sequence repetition operators to specify how many times an event or condition should repeat, either consecutively or over time.

1. Consecutive Repetition (Fixed Length): The [ *n ] operator means “repeat the preceding Boolean sub-expression n times in a row”. A common use is to detect or enforce a signal staying high (or low) for a certain number of cycles. For example, “Signal X must remain high for 3 consecutive cycles when triggered”. If we want to assert that whenever X goes high, it stays high for at least 3 cycles:

// If X rises, X must stay high for 3 cycles (no premature drop) */
assert property (@(posedge clk) $rose(X) |-> X[*3]);
/* 

Here X[*3] means X is true for 3 cycles in a row (including the current one). If X were to drop earlier, the sequence fails. This can be used for minimum pulse width checks. For instance, if a reset must be asserted for at least 5 clocks, use a similar construction with $rose(reset) and then reset[*5]. Conversely, for maximum width, you would ensure a signal does not stay high too long (see below).

2. Bounded Repetition (Range): The [ *m:n ] form allows a range. For example, sig[*1:4] means sig is true for 1 to 4 consecutive cycles. This could be used to allow some flexibility in pulse width, or to describe a sequence of events occurring a certain number of times. If you wanted to allow a pulse between 1 and 4 cycles long: $rose(X) |-> X[*1:4] ##1 !X (ensuring X deasserts after at most 4 cycles). Or if you want to specify “2 to 5 identical transactions in a burst,” you could structure a sequence that repeats a sub-sequence 2 to 5 times.

3. Unbounded Repetition ([*0:$] or [*1:$]): We saw this in earlier patterns – it means “repeat 0 or more times” or “1 or more times” until some other condition. It’s often used to consume an arbitrary number of idle or don’t-care cycles. For instance, (!req)[*0:$] was used to mean "any number of cycles of no request" (could be zero) in the forbidden and handshake properties. Unbounded repetition is powerful: A [*1:$] basically means A continues true for one or more cycles (i.e. A holds for some positive length, undefined upper bound). It’s often paired with a subsequent event. For example, A [*1:$] ##1 B means A holds continuously for some time and then B happens; if B doesn’t happen, the sequence can keep extending A... potentially forever (so in simulation, if B never occurs, the property remains alive waiting).

4. Conditional Repetition and Goto Repetition ([->]): In the advanced table, you might notice [->n] and [=n] notations. These are more advanced and less commonly needed in basic assertions. [->n] is a “goto repetition” meaning the expression occurs n times but not necessarily consecutively – it allows interleaving of other stuff. [=n] is a non-consecutive (scattered) repetition which is seldom used. For most practical purposes, [ * ] consecutive repetition suffices, and you can allow “don’t care” cycles with [*0:$] in between if needed.

5. At-Least/At-Most Patterns: You can combine repetition with the not property to enforce at most or at least counts:

At least N consecutive occurrences: e.g. the earlier pulse-width example ensures at least N cycles high. If you wanted to simply detect it (for a cover property or error), you could use a cover on X[*N] to see if it ever happens.

At most N consecutive occurrences: to ensure a signal doesn’t stay true too long, you can forbid N+1 in a row. For instance, “X shall not be high for more than 4 cycles continuously” – assert not( X[*5] ). This will fail if X ever stays high 5 or more cycles in a row.

Exact N repetitions: If you need exactly N, you often enforce at least N and at most N together. SVA also has an [=N] operator that can mean exactly N occurrences of a non-consecutive event, but for consecutive cycles, X[*N] combined with a check that cycle N+1 breaks the pattern is typically how to do it.

6. Counting Occurrences in a Sequence: Sometimes you want to ensure something happens a specific number of times during a larger sequence. For example, “During a frame of 100 cycles, exactly 3 error flags should be raised (no more, no fewer).” SVA alone might not easily count without additional logic, but one approach is using local counters or the $countones function on a history buffer of length 100 (which is complex to set up). In formal verification, one might unroll a loop or use $past in a recursive way to count. However, this goes beyond simple patterns. If needed, you can also utilize the property sequence [*-> N] (a trick with goto repetition) or layer assumptions on the environment to limit counts.

For learning and interviews, it’s usually enough to explain how to use [*] for consecutive repeats and mention that counting more arbitrary sequences might require helper logic or coverpoints.

7. Repetition in Protocols: A practical example: consider a serial interface that sends a start bit followed by 8 data bits. You could assert something like: start_bit ##1 data_bit[*8] ##1 stop_bit to ensure exactly 8 data bits between start and stop. Or for a run-length limited code, you might assert a maximum run length with a not of a repetition beyond a limit.

(Overall, repetition patterns allow succinct specification of behaviors that occur multiple times in a row. They help with pulse width checks, sequential protocols, and detecting bursts or idle stretches. Use [*N] and [*M:N] to directly encode consecutive repeats, and remember you can always invert a long repetition with not(...) to forbid too many repeats.)

Each of these patterns can be mixed and combined to create more complex assertions. When writing reusable assertion libraries or preparing for interviews, it’s important to not only memorize these templates but also understand their meaning in timing diagrams:

Ensure you choose the right implication (overlap vs non-overlap) for the intended sequence of events.

Use disable iff and edge qualifiers to avoid false positives.

Always double-check off-by-one cycle issues in latency (e.g., “within N cycles” vs “after N cycles exactly”).

By mastering these fundamental patterns – from simple request/acknowledge to complex sequence combinations – you can write assertions that capture a wide range of design behaviors. These serve as a reference toolkit for building up properties in verification environments. Happy asserting! */