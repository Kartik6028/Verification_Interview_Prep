
# AHB / AHB-Lite Advanced Notes

Author: ChatGPT + Kartik Study Notes  
Scope: AMBA AHB & AHB-Lite

---

# 1. AHB / AHB-Lite Signals

## 1.1 Global Signals
| Signal | Purpose |
|--------|---------|
| **HCLK** | Global system bus clock |
| **HRESETn** | Active-low reset |

---

## 1.2 Master → Slave (Address + Control)
| Signal | Purpose |
|--------|---------|
| **HADDR** | Address of transfer |
| **HTRANS** | Transaction type: IDLE, BUSY, NONSEQ, SEQ |
| **HWRITE** | 1 = write, 0 = read |
| **HSIZE** | Transfer size (byte/halfword/word) |
| **HBURST** | Burst type (SINGLE, INCR, WRAP) |
| **HPROT** | Protection/privilege flags |
| **HMASTLOCK** | Locked transfer sequence |
| **HWDATA** | Write data |

---

## 1.3 Slave → Master (Response)
| Signal | Purpose |
|--------|---------|
| **HRDATA** | Read data |
| **HREADY** | Indicates transfer completion (1 = done) |
| **HRESP** | Response (OKAY, ERROR) |

---

## 1.4 Arbitration Signals (AHB only, not AHB-Lite)
| Signal | Purpose |
|--------|---------|
| **HBUSREQ** | Master requesting bus |
| **HGRANT** | Arbiter granting bus |
| **HMASTER** | Indicates current master |
| **HMASTERLOCK** | Exclusive / locked access |
| **HSELx** | Slave select lines |

AHB-Lite removes multi-master signals (HBUSREQ/HGRANT/etc.).

---

# 2. AHB Transfer Phases

AHB uses a **two-phase pipelined protocol**:

| Phase | Description |
|--------|-------------|
| **Address Phase** | HADDR, HTRANS, HWRITE, HSIZE, HBURST, HPROT |
| **Data Phase** | HWDATA (write) or HRDATA (read) |

Address phase of next transfer overlaps with data phase of current transfer.

---

# 3. Tricky AHB Concepts / Corner Cases

## 3.1 HTRANS Behavior (IDLE/BUSY/NONSEQ/SEQ)
- **NONSEQ**: Start of a new burst or single transfer  
- **SEQ**: Continuation of burst  
- **BUSY**: Master keeps bus but is not transferring  
- **IDLE**: No transfer

**Trick:** BUSY does *not* advance address phase.

---

## 3.2 AHB Arbitration Deadlock
Possible if:
- Two masters request and hold LOCK (`HMASTLOCK`)
- Arbiter grants incorrectly and no master releases lock
- Or one master continuously asserts BUSY, preventing progress

---

## 3.3 HREADY Low for Too Long
If a slave holds `HREADY=0`, bus activity stalls:

- No new address phases accepted  
- No new data phases proceed  
- Pipeline freezes  

In complex multi-master systems, this can block higher-priority traffic → starvation.

Not as flexible as AXI’s independent channels.

---

## 3.4 Split and Retry (AHB only, deprecated in AHB-Lite)
Slaves can generate:
- **SPLIT**: Tells master to back off; arbiter removes master until slave ready.
- **RETRY**: Master retries later.

AHB-Lite does not use split/retry → simpler but less flexible.

---

## 3.5 Misaligned Access Handling
AHB does **not** inherently support misaligned transfers.
Common approaches:
- CPU generates two transfers
- Bus fabric aligns internally
- Or misaligned access causes exception

---

# 4. Why AHB Exists / Where It’s Used

## 4.1 Why AHB?

AHB was designed as:
- **High-performance** bus for earlier AMBA systems (before AXI)
- Shared bus with pipelining
- Easier than AXI, more flexible than APB

Key strengths:
- 1-cycle throughput for sequential bursts  
- Simple pipelining  
- Low complexity compared to AXI  

## 4.2 Where AHB is Used Today

### AHB
- Legacy ARM-based MCUs
- Flash/ROM interfaces
- DMA engines
- SRAM controllers
- Simpler SoC fabrics

### AHB-Lite
- Cortex-M microcontrollers (M0/M3/M4/M7)
- Peripheral buses
- Memory-mapped interfaces
- AMBA bridges (AXI-to-AHB, AHB-to-APB)

### Why not AXI everywhere?

AXI is heavier:
- More channels  
- Out-of-order rules  
- Needs complex interconnect  
- Overkill for low-latency, low-area microcontrollers

AHB-Lite is perfect when:
- Only **1 master** (e.g., Cortex-M)
- Simple memory subsystem
- Area/power efficiency needed

---

# 5. Comparison: AHB vs AXI (Quick Table)

| Feature | AXI | AHB |
|---------|------|------|
| Channels | 5 | 1 |
| Out-of-order | Yes (IDs) | No |
| Multiple outstanding | Yes | No |
| Burst flexibility | High | Medium |
| Handshake | VALID/READY | HREADY only |
| Interleave | Yes (R channel) | No |
| Complexity | High | Medium |
| Usage | High-end SoCs, GPUs, CPUs | MCUs, simple SoCs |

---

# 6. Summary Statements (Interview-Ready)

- **AHB-Lite is single-master only; AHB supports multiple masters.**
- **AHB uses a 2-phase pipeline (address + data).**
- **AXI has 5 channels with independent handshakes; AHB does not.**
- **AHB is in-order with no outstanding transactions; AXI is out-of-order with IDs.**
- **AHB-Lite used in Cortex-M MCUs, AXI used in Cortex-A systems.**
- **Split/retry only in full AHB, not AHB-Lite.**

---
