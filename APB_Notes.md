
# APB (Advanced Peripheral Bus) – Complete Notes

Author: ChatGPT + Kartik Study Notes  
Scope: AMBA APB2 / APB3 / APB4 (modern SoCs)

---

# 1. APB Overview

APB is the **simplest** AMBA protocol.  
Designed for **low-power**, **low-bandwidth**, **non-pipelined** peripheral access.

Used for:
- UART, SPI, I2C
- GPIO, Timers
- Watchdog
- Configuration registers
- Low-speed control/status interfaces

APB is NOT for:
- High-throughput memory
- Burst transfers
- Out-of-order or pipelined behavior

---

# 2. APB Signals (Full List)

APB is a **single channel**, non-pipelined protocol.

## 2.1 Global Signals

| Signal | Purpose |
|--------|---------|
| **PCLK** | APB clock |
| **PRESETn** | Active-low reset |

---

## 2.2 Master → Slave Signals

| Signal | Purpose |
|--------|---------|
| **PADDR** | Address of peripheral register |
| **PWRITE** | 1 = write, 0 = read |
| **PWDATA** | Write data from master |
| **PENABLE** | Enables 2nd cycle of transfer (ACCESS phase) |
| **PSELx** | Slave select (decoded) |
| **PPROT** (APB4) | Protection bits |
| **PSTRB** (APB4) | Byte strobes for writes |
| **PCLKEN** (optional) | Clock enable for low-power gating |

---

## 2.3 Slave → Master Signals

| Signal | Purpose |
|--------|---------|
| **PRDATA** | Read data from slave |
| **PREADY** (APB3+) | Slave ready (wait-state insertion) |
| **PSLVERR** (APB3+) | Error response |

APB2 did NOT have PREADY/PSLVERR.

---

# 3. APB Transfer Phases

APB has **two phases**:

## 3.1 SETUP Phase (Cycle 1)
- `PSEL = 1`
- `PENABLE = 0`
- `PADDR`, `PWRITE`, `PWDATA` stable

## 3.2 ACCESS Phase (Cycle 2+)
- `PENABLE = 1`
- Slave drives:
  - `PREADY` = 1 → transfer completes
  - `PREADY` = 0 → insert wait states

**IMPORTANT:**  
APB is **not pipelined** → cannot start a new transfer until previous one finishes.

---

# 4. Tricky Concepts / Corner Cases

## 4.1 PREADY Stretching (Wait States)
Slave may hold:
```
PREADY = 0
```
to indicate it is not ready with data yet.

Master must:
- Hold `PADDR`, `PWRITE`, `PWDATA`, `PSEL`, `PENABLE` stable
- Wait until slave sets `PREADY = 1`

---

## 4.2 PSLVERR
Usually used for:
- Invalid address region
- Unsupported access size
- Access protection fault

If `PSLVERR = 1` on **final ACCESS cycle**, transfer is considered failed.

---

## 4.3 APB4 Write Strobes (PSTRB)
Like AXI/AHB WSTRB but simpler.

Used for partial writes:
- `PSTRB[0] = 1` → byte 0 valid
- `PSTRB[1] = 1` → byte 1 valid
- ...

Without PSTRB, APB writes must be full-word.

---

## 4.4 Clock Enable (PCLKEN)
Some low-power SoCs gate APB clock per peripheral.

`PCLKEN = 0` → PCLK is stopped  
`PCLKEN = 1` → PCLK active

---

## 4.5 No Bursts / No IDs / No Pipelining
APB is deliberately simple:

- No bursts  
- No outstanding transfers  
- No VALID/READY-style protocol  
- No overlapping transfers  

APB = **fully blocking bus**.

---

# 5. Why APB Exists / Where It Is Used

## 5.1 Why APB
APB is:
- Low power
- Low area
- Easy to implement
- Ideal for “register-style” slaves
- Stable timing (no pipeline hazards)
- Perfect for simple memory-mapped control interfaces

## 5.2 Where APB is used

### Typical devices:
- UART  
- SPI  
- I2C  
- Timers  
- PWM  
- GPIO  
- Watchdog  
- RTC  
- ADC/DAC controller register access  

### Inside SoCs:
- AXI → AHB → APB bridges  
- Used as final stage for peripheral control

---

# 6. AXI vs AHB vs APB — Quick Summary Table

| Feature | AXI | AHB | APB |
|---------|-----|-----|------|
| Channels | 5 | 1 | 1 |
| Pipelining | Yes | Yes | No |
| Out-of-order | Yes | No | No |
| Bursts | Yes | Yes | No |
| Wait states | Yes | Yes | Yes |
| Best for | High BW | Mid-range BW | Low power / simple regs |
| ID support | Yes | No | No |
| Use case | CPUs, DMA, DRAM | Flash / SRAM | Peripherals |

---

# 7. Interview Sound Bites

These are perfect 1-line answers:

- **APB is non-pipelined and fully blocking.**
- **APB uses a simple 2-phase protocol: SETUP then ACCESS.**
- **PREADY allows variable-latency peripheral responses.**
- **APB4 adds PSTRB and PPROT for more advanced systems.**
- **APB is used for low-power, register-based peripherals, never for memory.**

---

