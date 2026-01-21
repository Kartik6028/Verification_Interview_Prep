class packet
    rand bit [31:0] data[8], src;

    constraint c{
        src > 8;
        src <10;
    }

    const bit [31:0] CONG = 42;
    rand bit[31:0] src;
    rand bit congest;
    rand bit [31:0];
    typedef enum  {something, someother, another} stim_e;

    randc bit [1:0] stim_e;

    constraint c_stim {
        len>0;
        len<1000;
        if (congest) {
            dest inside {[cong-10:cong+10]};
            src == cong; //( equivalence operator not assignemnt like =)
        }
        else {
            src inside {0 , [1:10], [10:1000]};

        }

    }

    constraint c_dist {
        src dist {
            0:=40,
            [1:3]:= 60
        }
        /* 0 :40/220;
           1: 60/220;
           2: 60/220;
           3: 60/220;
        */
        dest dist {
            0 :/ 40,
            [1:3] :/ 60
            }
          /*
            0 : 40/100;
            1: 20/100;
            2:  20/100;
            3:  20/100;
          */      
    }

    constraint order {
        low < med;
        med < high;
    }



    constraint c_ins {
        src inside {[low:high]}, //inclusive
        src  inside arr
    }


// SV supports two implication operators for constraints, -> and if
    constrain c_impl {
        check -> addr = 32'hFF; 
       // if check is true then addr must be true, but if check is false then addr can be true or false
       // equal to  (!check || addr)
       // there's also a fully biderectionally visible operator called <->
    }
    // .constraint_mode (0) will switch off a constraint;

    // use with keyword to add extra in-line constraint on the fly on top of existing ones


endclass

