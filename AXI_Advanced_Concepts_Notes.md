
# AXI Advanced / Tricky Concepts – Cheat Sheet

Author: ChatGPT + Kartik study notes  
Scope: AXI4 (with some AXI3 comparisons)

---

## 1. AXI Channels & VALID/READY Rules

### 1.1 Five AXI Channels

- **Write Address (AW)**
- **Write Data (W)**
- **Write Response (B)**
- **Read Address (AR)**
- **Read Data (R)**

Each channel is **logically independent** and uses a VALID/READY handshake:

- Sender drives `*_VALID`
- Receiver drives `*_READY`
- A transfer happens when **VALID && READY == 1** on a rising clock edge.

### 1.2 VALID / READY Rules (Master-side)

- Master must **not wait** for `READY` before asserting `VALID`.
- `VALID` must be driven based on *internal* intent, not on `READY`.
- If master waits for `READY` and slave waits for `VALID` → **deadlock**.

**Key rule:**
> VALID must not depend on READY.

### 1.3 Slave / Interconnect Responsibility

- Slave/interconnect can use `READY` to apply backpressure.
- But they must guarantee **forward progress** – they cannot hold `READY` low forever in a way that creates a circular wait.

---

## 2. IDs: AWID / BID / ARID / RID (and why no WID)

### 2.1 Write Path IDs: AWID and BID

- **AWID**: tag for a write transaction on the AW channel.
- **BID**: tag on the B (write response) channel.

These allow:

- Multiple outstanding writes with different IDs.
- Slave/interconnect can **complete writes out-of-order** across IDs.
- Within a **single ID**, ordering must be preserved.

**Example:**

- `AWID=3, AWADDR=0x1000` (long latency)
- `AWID=7, AWADDR=0x2000` (short latency)

Possible completion order on B channel:

- First: `BID = 7` (write to 0x2000 done)
- Later: `BID = 3` (write to 0x1000 done)

Master uses BID to know which write finished.

### 2.2 Read Path IDs: ARID and RID

- **ARID**: tag for a read request on the AR channel.
- **RID**: tag returned with read data on the R channel.

Reads are **more flexible** than writes:
- Multiple outstanding read bursts with different ARIDs.
- RDATA beats for different IDs can be **interleaved** on the R channel.
- For each ID separately, data must still be ordered and bursts must be contiguous.

**Example:**

- `ARID=3` → burst of 4 beats
- `ARID=7` → burst of 2 beats

R channel can return:

- `RID=3, beat0`
- `RID=7, beat0`
- `RID=3, beat1`
- `RID=7, beat1 (and RLAST for ID=7)`
- `RID=3, beat2`
- `RID=3, beat3 (RLAST for ID=3)`

RID tells the master which ARID each data beat belongs to.

### 2.3 Why AXI4 Removed WID (AXI3 vs AXI4)

**AXI3**:
- Had a **WID** signal on the W channel.
- Allowed write data for different IDs to **interleave**.
- Very complex for slaves/memory controllers:
  - Reorder logic
  - Large tag/FIFO structures
  - Many deadlock corner-cases.

**AXI4**:
- **Removed WID**.
- Forbids write data interleaving across IDs:
  - All W beats must appear **in-order**, matching the accepted AW order.
  - For any given ID, write data beats must be contiguous and not interleave with other IDs.

**Result:**

- Slave keeps an **AW FIFO**.
- On every W transfer (WVALID && WREADY), it consumes from the FIFO head.
- Each W beat is associated with the **oldest unmatched AW**.
- No ID needed on W channel → **no WID**.

---

## 3. Ordering Between AW, W, and B

### 3.1 Independence of AW and W

- W channel is **logically independent** of AW.
- WDATA **may appear before** AW handshake completes.
- Slave must handle:
  - AW first, then W
  - W first, then AW
  - AW and W arriving in the same or different cycles
- Matching is done via **AW FIFO ordering**, not by timing.

### 3.2 W Channel Ordering Restrictions

- AXI4 requires that W beats for a transaction:
  - Are **contiguous**.
  - Follow the **acceptance order** of AW.
- No interleaving of WDATA between IDs in AXI4.
- This is what allows AXI4 to safely remove WID.

### 3.3 Write Response Ordering (B)

- Per-ID ordering:
  - For a given ID, B responses must be ordered.
- Across different IDs:
  - B responses **may be out-of-order**.
  - BID indicates which AWID the response belongs to.

---

## 4. WLAST and AWLEN

### 4.1 Purpose of WLAST

- **WLAST** marks the **last beat of a write burst**.
- Slave relies on WLAST to know:
  - When the burst is complete.
  - When it can move to the next AW entry.
  - When to issue a B response.

### 4.2 Why AWLEN Alone is Not Enough

Even though AWLEN encodes the burst length (beats - 1):

- AW and W are **independent channels**.
- Stalls / bubbles can occur on W channel.
- Slave cannot reliably know which W beat is “beat 0/1/2/…/N” just from AWLEN and the passage of cycles.
- WLAST is required for unambiguous end-of-burst detection.

**Key point:**
> AXI requires WLAST on the final data beat of a burst, even though AWLEN provides the length.

---

## 5. Typical AXI Deadlock Scenarios

These are **hot interview topics**.

### 5.1 Deadlock Scenario #1 – BREADY vs AWREADY/WREADY

**Setup:**

- Master issues a write (AW + W).
- Slave wants to send B response.
- Master:
  - Holds **BREADY = 0**, waiting for more AWREADY/WREADY (trying to push more writes before accepting responses).
- Slave / interconnect:
  - Holds **AWREADY/WREADY = 0**, because its internal buffers are full until the B response is accepted.

**Circular wait:**

- Master waits for AWREADY/WREADY.
- Slave waits for BREADY.

Result: **Deadlock**.

**Fix / Correct behavior:**
- Master should usually keep **BREADY = 1** (or at least make sure it never creates such a circular wait).

---

### 5.2 Deadlock Scenario #2 – Response Buffering Between S0 and S1

**Topology:**

- Master M0 connected via interconnect to two slaves S0 and S1.
- Interconnect uses a **shared response buffer** for R/B responses from S0 and S1.

**Sequence:**

1. S0 generates many read responses (R channel).
2. Master is not asserting RREADY (for whatever reason).
3. Response buffer fills with S0’s RDATA.
4. Now S1 wants to send a B response for a write.
5. Shared buffer is full → S1’s B response cannot be stored.
6. Master is waiting for S1’s B response to proceed (e.g., to resume reads or issue more traffic).
7. Master still does not assert RREADY for S0 because it is waiting for S1’s completion.

**Circular wait:**

- Buffer is full of S0 responses.
- S1 cannot push its B response.
- Master waits for S1’s B.
- Master doesn’t read S0’s RDATA.
- Buffer never drains.

Result: **Deadlock**.

---

### 5.3 Deadlock Scenario #3 – Outstanding Read Limit Blocking Writes

**Setup:**

- Interconnect or slave has a finite table of “outstanding transactions” per master (e.g., 8 entries).
- Master sends 8 **read** requests (AR).
- Outstanding slot table becomes **full**.

**Behavior:**

- Interconnect deasserts **ARREADY** (no more reads).
- It might also deassert **AWREADY** because:
  - Same outstanding table or a shared resource is used for both reads and writes.
  - Or internal policy forces serialized handling.

If the master is designed such that:

- It waits for some write completion before draining read data,
- And the interconnect waits for read data to be accepted before allowing writes,

You can get:

- Master waiting for writes.
- Interconnect waiting for master to take reads.
- Writes never issued; reads never drained.

Result: **Deadlock**.

---

### 5.4 Deadlock Scenario #4 – AW FIFO Full and W Channel Stalled

**Setup:**

- Slave keeps an internal **AW FIFO** and **W acceptance logic**.

Bad implementation example:

1. AW FIFO becomes full → slave deasserts AWREADY.
2. Master continues to send WVALID for a new transaction whose AW hasn’t been accepted (or slave disallows W without AW entry).
3. Slave keeps WREADY = 0 because it has no AW slot reserved.
4. Master might be blocked waiting for AWREADY/WREADY, but doesn’t accept B or R from previous transactions.

If this is combined with some dependency on responses (B/R) that cannot be sent because of buffer limits, you end up with a circular wait.

---

### 5.5 Deadlock Scenario #5 – Interconnect Circular Dependency

In a more complex NoC:

- M0 → S0, M1 → S1, with shared interconnect resources.
- S0’s ability to send responses depends on S1’s path being free.
- S1’s ability to make progress depends on some transaction routed via S0.

If the routing / arbitration / buffering are not carefully designed, the NoC can create a cycle of dependencies → **network-level deadlock**.

---

## 6. “Independence” of Channels vs Real Implementations

### 6.1 Spec vs Reality

- AXI **specification**:
  - Channels are logically independent (AW/W/B vs AR/R).
- Real **implementation**:
  - Interconnect often uses shared resources:
    - Common FIFOs
    - Shared outstanding tables
    - Shared arbitration state machines
  - As a result, AW can be indirectly throttled by AR or by R/B channels, etc.

This is **legal** as long as **forward progress** is guaranteed and no deadlocks are created.

### 6.2 Interview-Style Explanation

> By spec, AXI channels are independent. In practice, interconnects couple them via shared resources (outstanding transaction tables, common buffers, DRAM schedulers). If these couplings create circular waits — for example, reads filling a shared buffer such that writes can’t return responses which the master needs before draining the reads — you get AXI deadlock.

---

## 7. Quick Recap Statements (Interview Sound Bites)

- **WID removed in AXI4** because write data interleaving was banned; W channel now follows AW order, so IDs are unnecessary there.
- **AWID/BID** pair write requests and responses; **ARID/RID** pair read requests and data.
- **WLAST** is required even though AWLEN gives the length, because AW and W are independent channels and the slave must not infer last beat from timing.
- **VALID must not depend on READY** – masters must assert VALID when they have something to send, not when READY is seen.
- **Deadlocks** usually arise from circular waits involving:
  - BREADY vs AWREADY/WREADY
  - Shared response buffers between multiple slaves
  - Outstanding transaction limits
  - Badly coupled read/write arbitration.

---


AW CHANNEL

| Signal       | Width | Purpose (Short)                                    |
| ------------ | ----- | -------------------------------------------------- |
| **AWVALID**  | 1     | Master: Address/control valid                      |
| **AWREADY**  | 1     | Slave: Ready to accept AW                          |
| **AWID**     | IDW   | Transaction ID (tags write burst)                  |
| **AWADDR**   | AddrW | Start address of write burst                       |
| **AWLEN**    | 8     | Burst length (beats–1)                             |
| **AWSIZE**   | 3     | Bytes per beat (2^size)                            |
| **AWBURST**  | 2     | Burst type (FIXED, INCR, WRAP)                     |
| **AWLOCK**   | 1     | Atomic/exclusive access                            |
| **AWCACHE**  | 4     | Cache attributes (bufferable, cacheable, allocate) |
| **AWPROT**   | 3     | Protection flags (priv, secure, instr)             |
| **AWQOS**    | 4     | QoS / priority                                     |
| **AWREGION** | 4     | NoC routing hint                                   |
| **AWUSER**   | U     | User-defined sideband                              |



WCHANNEL
| Signal     | Width   | Purpose                              |
| ---------- | ------- | ------------------------------------ |
| **WVALID** | 1       | Master: Write data valid             |
| **WREADY** | 1       | Slave: Ready to accept data          |
| **WDATA**  | DataW   | Actual write data                    |
| **WSTRB**  | DataW/8 | Byte enables (which bytes are valid) |
| **WLAST**  | 1       | Final beat of write burst            |
| **WUSER**  | U       | User-defined                         |


BCHANNEL

| Signal     | Width | Purpose                             |
| ---------- | ----- | ----------------------------------- |
| **BVALID** | 1     | Slave: Write response valid         |
| **BREADY** | 1     | Master: Ready to accept response    |
| **BID**    | IDW   | ID of the completed write           |
| **BRESP**  | 2     | Write response (OKAY/SLVERR/DECERR) |
| **BUSER**  | U     | User-defined                        |



ARCHANNEL
| Signal       | Width | Purpose                     |
| ------------ | ----- | --------------------------- |
| **ARVALID**  | 1     | Master: Read address valid  |
| **ARREADY**  | 1     | Slave: Ready to accept AR   |
| **ARID**     | IDW   | ID tag for read burst       |
| **ARADDR**   | AddrW | Read address                |
| **ARLEN**    | 8     | Beats–1 for read burst      |
| **ARSIZE**   | 3     | Bytes per beat              |
| **ARBURST**  | 2     | Burst type                  |
| **ARLOCK**   | 1     | Exclusive access indication |
| **ARCACHE**  | 4     | Cache properties            |
| **ARPROT**   | 3     | Protection properties       |
| **ARQOS**    | 4     | QoS tag                     |
| **ARREGION** | 4     | NoC region hint             |
| **ARUSER**   | U     | User-defined                |



RCHANNEL
| Signal     | Width | Purpose                           |
| ---------- | ----- | --------------------------------- |
| **RVALID** | 1     | Slave: Read data valid            |
| **RREADY** | 1     | Master: Ready to accept read data |
| **RDATA**  | DataW | Actual read data                  |
| **RID**    | IDW   | ID of returning read burst        |
| **RRESP**  | 2     | Read response                     |
| **RLAST**  | 1     | Final beat of read burst          |
| **RUSER**  | U     | User-defined                      |




| Feature                      | **AXI4**                                 | **AXI4-Lite**                                   |
| ---------------------------- | ---------------------------------------- | ----------------------------------------------- |
| **Burst support**            | ✔ Yes (up to 256 beats, INCR/WRAP/FIXED) | ❌ No (single beat only)                         |
| **Outstanding transactions** | ✔ Multiple outstanding reads/writes      | ❌ Only 1 outstanding read + 1 outstanding write |
| **IDs (ARID/AWID/RID/BID)**  | ✔ Supported                              | ❌ Removed                                       |
| **Interleaving**             | ✔ Allowed for reads (RID)                | ❌ Not allowed (no bursts)                       |
| **Write strobes (WSTRB)**    | ✔ Required                               | ✔ Required (but single beat only)               |
| **Channel structure**        | Full 5 channels                          | Same 5 channels but simplified functionality    |
| **Complexity**               | High (used in DRAM/CPU/GPU fabrics)      | Very low (for register access)                  |
| **Use case**                 | High-bandwidth memory, DMA, CPUs, GPUs   | Control/status registers, low-speed config      |
| **Transaction size**         | Parameterized (supports wide data buses) | Typically 32 or 64-bit                          |
| **Pipelining**               | ✔ Deep pipelining allowed                | Minimal pipelining                              |
| **Response rules**           | Full AXI semantics                       | Simplified OKAY/SLVERR                          |
| **Ordering model**           | ID-based ordering                        | No ID → strict in-order                         |



🟦 When to Use Which?
AXI4

Used for:

DRAM interfaces

High-performance interconnects

DMA engines

GPU/CPU traffic

Streaming data pipelines

AXI4-Lite

Used for:

MMIO registers

Peripheral control interfaces

Configuration/status blocks

Timer/UART/SPI register access

Think of AXI4-Lite like a “simple register bus that follows AXI rules.”