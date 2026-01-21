//WRITE A FUNCTION TO GET STREAMING VALUES OF DATA IN AND CREATE AN INTERNAL BUFFER OF LET'S SAY 10 ITEMS. NOW YOU HAVE KEEP CALCULATING THE MAX VALUE FROM THAT BUFFER, BASICALLY KEEP A HISTORY OF LAST 10 ITEMS.. AND WHEN ASKED POP OUT THE MAX FROM THOSE


function void buffmax  (input bit [31:0] data_in, input bit get_max, output bit [31:0] max_val);
    static bit [31:0] que[$];
    
    if (que.size() <10 ) begin
        que.push_back(data_in);
    end
    else begin
        que.pop_front();
        que.push_back (data_in);
    end
    if (get_max) begin
        max_val = 0;
        foreach (que[i])begin
                if (que[i]>max_val) begin
                    max_val =  que[i];
                end
        end
    end
endfunction

// Infinite stream of incoming data no history, just give max when asked

function bit [31:0] stream_max (bit [31:0] data_in, bit get_max );
    static bit [31:0] max_val;
    if (data_in >= max_val) begin
        max_val = data_in;
    end
    if (get_max)return max_val;
endfunction



// LOGIC and BIT difference is 4 staate and 2 state respectively
// With functions use automatic making each func call independent or thread sage for concurrent calls.
// with sv void functions you can pass by value using input keyword. and within a void function you can use output keyword and get the output value by refernece.
//main diff between using input output pattern as opposed to using a return function is that you with later you cannot have multiple outputs from a function.

// functions are automatic by default, and tasks are static by default.
// Main difference between function and a task, is that functions must end in zero sim time, whereas tasks may consume sim time and have timing control.


// factorial of n 
function void fact ( input bit [31:0] n, output bit [31:0] fact);
    
    for (int unsigned i =1 ; i <= n;i++) begin
        fact = fact * i;
    end

endfunction

// Use REF for call by reference.

bit [31:0] res;
factorial(5, res);

// write  a task to count the number of clk cycles when start goes high, and stop when stop goes high
task automatic count (input bit start, input bit stop, output bit [31:0] count);
    @ (posedge clk iff start);
    count=1;
    while (!stop) begin
        @(posedge clk)
        count=count+1;
    end
endtask

//
//AIE
Can you show me how do you write a SV code and assertion check for the spec
Whenever synchronous RESET is set, READY should go low.
2 clocks after every synchronous RESET release, READY should go high.

module test (
input bit clk,
input bit reset,
output ready
);
bit [1:0] count;
always @ (posedge clk ) begin
    if (reset) begin
        ready<=0;
        count <=0;
    end
    else begin
        count+=1;
        if (count ==2'd2) begin
            ready <=1   ;
        end
    end
end
endmodule


property reset_check;
    @ (posedge clk) reset |-> (!ready);
endproperty

property ready_check; 
     @ (posedge clk) $fell (reset) |-> #2 rdy ;
endproperty

assert property (reset_check);
assert property (ready_check);

//design a traffic controller , control red-green-yellow, input for walk sign. Cycle through RED GREEN YELLOW, whenever input is walk=1, transition to RED LIGHT.

module traffic_controller(
    input clk;
    input walk;
    input rst;
    output red;
    output green;
    output yellow;
    );
    bit [1:0] state;next_state;
    always @(posedge clk)
    if (rst)begin
        state<= 2'b00;
        count <=1'b0;

    end

    else begin 


    case (state) begin

    2'b00: begin
        state<= 2'b11;
    end

    2'b01:   //RED
        begin
            count=count+1;
            if ((count == rthreshold )) begin
                    state<= 2'b11;
                    flag <=0;
             end


        end

    2'b10:    // YELLOW
        begin
                    count=count+1;
                  if (count == ythreshold) begin
                    state<= 2'b01;
                  end

        end

    2'b11:   // GREEN
        count=count+1;
        if (count == gthreshold) begin
            state<= 2'b10;
        end

    end
    endcase

    end

    always @ (posedge clk )
    begin
        if (walk && !flag) begin
            rthreshold= rthreshold +somevalue;
            flag =1; 
        end
    end
endmodule 


// write a function take a 32bit input, returns true if value is one hot

function bit onehot (input bit [31:0]in);
    return (in !=0)  && (in & (in-1) ==0);
endfunction


//AII

// array of 8 bit vars, constraint for making sure each of the array element is unique 

rand bit [7:0]arr [10];



constraint arr {
    byte data;
    for (int i =0 ; i< arr.size-1 ; i+=) 
        for (int j =1; j<size-1;j++    )
          if (i!=j)  arr[j] != arr[i];
    arr [i+1] > arr [i];
}
//AIE
calculate fifo depth for 100BYTES of data, in a fifo which has no timing consideration. 2 Diff freq 

Read freq = 50 MHZ 
WR FREQ is 150 MHZ
 [ 
    0: BYTE1 
    1: BYTE2
    2: BYTE3  
    3:
    4:
    5:
  ]

//AIE
design 2 inputs 1 en and 1 input, its intent is to detect pos edge on the input when en is 1, as soon as en is 0 out goes 0


input a
input en
out 

property x @ (posedge clk )

$rose (a) && (en) |-> out; 
endproperty


a en    out
0  0     0  ->  (out) |-> en && $rose(a) 
0  1     a
1  0      
1  1

property y @ (posedge clk )
$fell(en)|-> (out ==0);
endproperty


arr[10]

[1, 2 ,.   .,.. 9,]
val1=0;
equil_index=0


//AIE


while (lhs!=rhs) begin
    for (int i= equil_index+1; i< size; i++)
         rhs +=  arr[i] ;

    for (int i = 0 ; i=<equil_index; i++) 
        if (equil_index ==0) lhs= 0;
        else  lhs+= arr[i]
    
    if (lhs==rhs) return equil_index;
    else if (equil_index == size-1) return 0;
    else equil_index++;

end

/*

Requirements

Range constraint

All generated addresses must be within the memory map range 0x8000_0000 to 0x8000_FFFF.

Alignment constraint

The address must be 1 KB (1024-byte) aligned.
(In other words, the lower 10 bits of the address must be 0.)

Bank constraint

The 64 KB memory is divided into 4 banks, each of 16 KB (0x4000 bytes).

Bank 0: 0x8000_0000 – 0x8000_3FFF

Bank 1: 0x8000_4000 – 0x8000_7FFF

Bank 2: 0x8000_8000 – 0x8000_BFFF

Bank 3: 0x8000_C000 – 0x8000_FFFF

You must be able to randomize the address only within a specific bank when a variable rand bit [1:0] bank_sel; is set.
For example, if bank_sel == 2'b10, the address should only be from Bank 2.

*/

class packet extends from uvm_transaction;

rand bit [31:0] addr;
rand bit [1:0] bank_sel;

constraint range {

    addr inside {[32'h8000_0000: 32'h8000_FFFF]};
}

constraint alignment {

    addr % 1024 == 0;
}

constraint bank_sel{
   if (bank_sel == 2'b00) addr  inside {[8000_0000:8000_3FFF]};
   if (bank_sel == 2'b01) addr  inside {[8000_4000:8000_7FFF]};
   if (bank_sel == 2'b10) addr  inside {[8000_8000:8000_BFFF]};
   if (bank_sel == 2'b11) addr  inside {[8000_C000:8000_FFFF]};
}

endclass

/*
Specs

addr is 32-bit, must be in [0x4000_0000 : 0x4000_FFFF].

burst_len ∈ {1,2,4,8,16} (beats). Beat size is 4 bytes.

addr must be aligned to burst_len * 4.

The entire burst must not cross a 4 KB page boundary.

Optional targeting: when bank_sel (2 bits) is set, the first beat must be inside the bank window:

Bank 0: [0x4000_0000 : 0x4000_3FFF]

Bank 1: [0x4000_4000 : 0x4000_7FFF]

Bank 2: [0x4000_8000 : 0x4000_BFFF]

Bank 3: [0x4000_C000 : 0x4000_FFFF]


*/

class transaction extends uvm_sequence_item;
rand bit [31:0] addr;
rand bit [3:0] burst_len;


constraint range {
    addr inside {[32'h4000_0000 : 32'h4000_FFFF]};
}

constraint burst_len {
    burst_len inside {[4'd1, 4'd2, 4'd4, 4'd8, 4'd16]};
}

constraint aligment {

    addr % (burst_len * 4) == 0;
}

constraint burst_range {

    (addr[11:0] + (burst_len*4 -1 ))<=4095;
}
endclass


/*
Q2) Whitelist + Blacklist + Weighted Distribution

Constrain an address to allowed regions with weights, block a repeating reserved window, and enforce cacheline alignment.

Specs

addr must land in the whitelist union:
A: [0x9000_0000 : 0x9000_1FFF]
B: [0x9000_4000 : 0x9000_7FFF]
C: [0x9000_C000 : 0x9000_FFFF]

Weights: A:1, B:3, C:2 (i.e., B most likely).\\

Alignment: 64B (cacheline).

Blacklist pattern: Every 2 KB block reserves the first 256B.
That is, for addr % 2048, the range [0 : 255] is forbidden.

Optional: when is_streaming==1, consecutive randomizations should prefer monotonically increasing addr (hint: use randc/state or a soft constraint).
*/


rand bit [31:0] addr;
constraint range{
    addr dist { 
                [32'h9000_0000: 32'h9000_1FFF] := 1,
                [32'h9000_4000: 32'h9000_7FFF] := 3,
                [32'h9000_C000: 32'h9000_FFFF] := 2
                };
}

constraint alignment {
    (addr & 32'h3F) ==0;
}

constraint forbid {
    (addr % 2048) inside [32'd256:32'd2048];
    }

constraint stream{
    if is_streaming -> soft addr > prev_addr;

}
/*

Q3) Page/Offset Build + Set Index Binding

Generate an address from page_num and page_offset, bind index bits to a set_id, and support a “large-page” mode.

Specs

page_num in [0x1000 : 0x1FFF].

Two modes:

large_page==0: page size = 4 KB → page_offset in [0 : 4095].

large_page==1: page size = 2 MB → page_offset in [0 : 2*1024*1024 - 1].

Construct: addr = {page_num, page_offset} only when 4KB pages.
For 2MB pages, ensure resulting addr still falls in [0xA000_0000 : 0xA1FF_FFFF].

Cache set mapping: set_id (6 bits) must equal the index bits of addr[11:6] (i.e., 64 sets, 64B line).

Alignment: 64B lines → addr[5:0] == 0.

Prohibit wraparound across 1MB boundaries for any increment of +N*64B where N∈[0:7].
*/

rand bit [31:0] addr;
rand bit [15:0] page_num;
rand_bit [15:0]page_offset;
rand_bit [31:0]size;

constraint page_num{
    page_num inside [32'h1000: 32'h1FFFF];

}

// addr = page_num , page_offset

constraint add_gen{
    solve page_offset before addr;
    if(!large_page) {
        page_offset inside [32'd0:32'd4095];
        addr = {page_num, page_offset};
    }
    else
    {
        page_offset inside [32'd0 : 32'd2*1024*1024 -1];
        addr inside [32'hA000_0000: 32'hA1FF_FFFF];
    }

    addr [5:0] ==0;


}



constraint addr_gen {
   if (!large_page) addr = {page_num,page_offset};
   if (large_page)addr inside  {[0xA000_0000: 0xA1FF_FFFF]};
   addr [5:0]==0;
   page_num inside {[16'h1000:16'h1FFF]};

}

constraint page_offset{
    size = large_page? (2*1024*1024): 4096;
    page_offset inside {[16'd0: size-1]};
}



/*
addr must fall in a valid channel and bank range.

Must be aligned to trans_size.

When two consecutive transactions target the same bank, the second one must have a higher address.

You must be able to target a specific channel when force_ch is set.

Transactions must not cross a bank boundary (stay within 64 KB).
CH0 → [0x0000_0000 : 0x0007_FFFF]

CH1 → [0x0008_0000 : 0x000F_FFFF]
*/

rand bit [31:0] addr; 
rand bit [4:0]trans_size;
rand bit channel;
rand bit [2:0]bank_id;
rand bit force_ch;
rand bit [31:0]prev_addr;
constraint addr_range {
    if (force_ch)addr inside {[32'h0000_0000 : 32'h0007_FFFF]}; // select ch0
    else addr inside {[32'h0008_0000: 32'h000F_FFFF]}; // select CH1
}
constraint trans_size {

    trans_size inside {4,8,16,32};
    addr % trans_size ==0;
}
constraint bank_align {
    addr[15:0] + (trans_size * bank_id) <= 16'hFA00; 

}
constraint consecutive {

    if (addr [18:16] == prev_addr [18:16]) {
        addr > prev_addr;
    }
}


/*  
You’re designing a constrained-random generator for DMA transfer descriptors.

Each descriptor includes:

A source address

A destination address

A transfer size

A mode flag (is_secure) that changes which address range is used
*/

rand bit [31:0] src_addr;
rand bit [31:0] dest_addr;
rand bit [7:0]size;
rand bit is_secure;


constraint addr_range {
    src_addr[3:0] == 'b0;
    dest_addr[3:0] == 'b0;


    if (is_secure) {

        src_addr inside {[32'h5000_0000 :  32'h5000_FFFF]};
        dest_addr inside {[ 32'h5000_0000: 32'h5000_FFFF]};

    }

    else {
        src_addr inside {[ 32'h4000_0000: 32'h4000_FFFF]};
        dest_addr inside {[ 32'h4000_0000: 32'h4000_FFFF]};
    }

}

constraint size_rest{
    soft size inside {64,128};
    size inside {16,32,64,128};
    // OR i am giving both options i guess second one below is better ?
    $onehot (size);
    size [3:0] == 'b0;
}

constraint page_boundary{
    (src_addr[11:0] + size) <=  12'hFFF;
    (dest_addr[11:0] + size) <=  12'hFFF;

} 
constraint relation {
    solve src_addr before dest_addr;
    
    if (is_secure) {  
            dest_addr >= src_addr + 12'h100;
    }
   else {
        dest_addr >= src_addr;
   } 

}

constraint non_secure {
    if (!is_secure) {
        dest_addr [9:0] ==src_addr[9:0] + 12'h200;
    }
}


/*
Requirements

There are 8 descriptors, stored in an array addr_q[8].

Each addr_q[i] is a 32-bit address.

All addresses must:

Fall within [0x8000_0000 : 0x8000_0FFF] (4 KB page).

Be 64-byte aligned.

Be unique (no duplicates).

Additionally:

Addresses must be sorted ascending (addr_q[i] < addr_q[i+1]).

The distance between consecutive entries must be at least 128 B apart.

The last entry must not cross the 4 KB boundary.
*/

rand bit [31:0] addr_q [8];

constraint addr_range {

    foreach (addr_q[i]) {
        addr_q[i] inside {[32'h8000_0000 :  32'h8000_0FFF]};
        addr_q[i] [5:0] == 'b0;

        if (i>0) addr_q[i] >= (addr_q[i-1] + 8'h80);
        if (i==7)addr_q [i] <= 12'h1000; 

    }

}
/*
You are writing a constrained-random generator for a queue of packets that are to be sent over a channel.
Each packet has a unique 8-bit ID and a 16-bit payload length.
You must generate a queue of variable length (1–10 packets).
*/

rand bit [7:0] packet_q[$];
rand bit [15:0]payload_length; 
rand bit [3:0]pq_length; 
rand bit [7:0]packet_id;

constraint packetId {

    unique {packet_id};
}

constraint queue_generator {
    
    
    payload_length[2:0] =='0;

    pq_length inside {[4'd1:4'd10]};

    foreach (packet_q[i]) {
        if (i<pq_length) {
            packet_q[i].insert({packet_id,packet_length});
        }
       
    }

}


class packet;

    rand bit [3:0] num_addrs;
    rand bit [31:0]addr_q[$];

    constraint num_addr {
        num_addr inside {4,12};
    }
        
endclass


rand packet q;

rand bit [3:0] num_addrs;
rand bit [31:0] base_addr;
// 64KB =    0xFA00;
rand bit [31:0] addr;

function new ();
    q = new ("this");
endfunction




function void pre_randomize ();
    for(int)

endfunction

constraint base_addr_align {
    base_addr [11:0] = 'b0;
}

constraint addr_gen {
    solve base_addr before addr;
    addr inside [base_addr: (base_addr + 32'hFA00)-1];
}


constraint num_addr {
    num_addr inside {4,12};
}

constraint 



// COVERAGES //

/*
You’re verifying a DMA that supports bursts of 1, 2, 4, 8, and 16 beats, and each beat is 8 bytes.
The 32-bit addr input must always be 8 B-aligned.
You want coverage to ensure you’ve exercised:

All burst lengths,

All page offset regions within a 4 KB page,

And to cross the two, so you can see if large bursts near the 4 KB boundary are tested.

Write a covergroup that:

Samples on every valid transfer (i.e. iff (valid && ready)).

Creates bins for burst_len values {1,2,4,8,16}.

Creates bins for addr[11:0] such that:

low: [0:1023]

mid: [1024:2047]

high: [2048:3071]

near_boundary: [3072:4095]

Cross the two coverpoints.

Mark the combination (burst_len==16 && addr in [3072:4095]) as illegal (since that burst would cross the page boundary).
*/




bit [12:0] page_offset;
covergroup cg @(posedge clk iff (valid && ready));
    coverpoint burst_len {
        bins length = {1,2,4,8,16}; 
    }

    coverpoint page_offset;

    coverpoint addr {
        bins low = [0:1023];
        bins med = [1024 : 2047];
        bins high = [2048:3071];
        bins near_bound = [3072:4095];
    }


    cross addr, burst_len;
    cross page_offset, burst_len;


endgroup








covergroup cg iff (valid && ready)
    coverpoint addr[2:0];

    coverpoint burst_len [4:0] {
        bins q1 = {1,2,4,8,16};
    }

    

    coverpoint addr[11:0] {

        bins low [] = {[12'd0:12'd1023]};
        bins mid [] = {[12'd1024:12'd2047]};
        bins high[] = {[12'd2048:12'd2071]};
        bins nb [] = {[12'd2072:12'd4095]};


    }


    cross addr, burst_len {
        illegal_bins = burst_len intersect {16} && addr[11:0] intersect {[3072:4095]};
    };

endgroup
/*
🧠 Q2) AXI Write Transaction Coverage

You are verifying an AXI4 write channel.
Each transaction has the following sampled signals:

addr — 32-bit address

burst_len — number of beats (1 – 16)

burst_type — 2-bit value (00 = FIXED, 01 = INCR, 10 = WRAP)

size — 3-bit beat size (e.g., 3’b010 = 4 B/beat)

valid, ready — handshake

You want to create a covergroup that ensures the following are exercised:

1️⃣ All burst types (FIXED, INCR, WRAP)
2️⃣ All burst lengths {1, 4, 8, 16}
3️⃣ All data sizes {1, 2, 4, 8} bytes per beat
4️⃣ Cross coverage of burst_type × size
5️⃣ Mark the combination WRAP + 8 B/beat as illegal (not supported)
6️⃣ Only sample when valid && ready
7️⃣ Optional bonus: add a coverpoint for addr[11:0] (page offset) with bins
  low, mid, high, near_boundary (like before)
*/



covergroup cg @(posedge clk iff (valid && ready));
    btype :coverpoint burst_type {
        bins b1 = {2'b00};
        bins b2 = {2'b01};
        bins b3 = {2'b10};
    }

    blen:coverpoint burst_len {
        bins b1 = {1};
        bins b2 = {4};
        bins b3 = {8};
        bins b4 = {16};

    }

    s:coverpoint size {
        bins b1 = {1};
        bins b2 =  {2};
        bins b3 = {4};
        bins b4 ={8};

    }
    cross btype, s {
        illegal_bins comb =  binsof(btype.b3)  &&  binsof (s.b4);
    };


endgroup


covergroup cg with function sample (bit [31:0] addr, bit btype[1:0], bit [3:0] blength, bit [3:0] bpb, bit valid, bit ready );

TYPE:coverpoint btype iff (valid && ready);
LENGTH:coverpoint blength iff (valid && ready) {
    bins legal = {1,4,8,16};
}
DATA_SIZE:coverpoint bpb iff (valid && ready){
    bins legal = {1,2,4,8}
}
cross btype, bpb iff (valid && ready){
    illegal_bins = binsof(TPYE) intersect {01} && binsof(DATA_SIZE) intersect {8};

}
endgroup


