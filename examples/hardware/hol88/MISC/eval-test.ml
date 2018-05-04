% File for testing the Lisp functions defined in hol/lisp/eval.l 
  and hol/lisp/dml-eval.l (not part of the HOL system) %

load_theory `values` ? ();;

let test t  = mk_thm([], "t = ^t")
and testc t = t;;
%old testc: and testc t = "t = ^t";;%

let th1 = BITS_RULE(test "BITS5 #00111");;
let th1' = BITS_CONV(testc "BITS5 #00111");;

let th2 = ADD_RULE(test "2+39");;
let th2' = ADD_CONV(testc "2+39");;

let th21 = DIF_RULE(test "2-39");;
let th21' = DIF_CONV(testc "2-39");;

let th31 = EQ_RULE(test "2=3");;
let th31' = EQ_CONV(testc "2=3");;

let th32 = EQ_RULE(test "15=15");;
let th32' = EQ_CONV(testc "15=15");;

let th4 = EL_RULE(test "EL 5 [1;2;3;4;5;6;7;8]");;
let th4' = EL_CONV(testc "EL 5 [1;2;3;4;5;6;7;8]");;

let th5 = WORD_RULE(test "WORD13 16");;
let th5' = WORD_CONV(testc "WORD13 16");;

let th6 = VAL_RULE(test "VAL13 #0000000000111");;
let th6' = VAL_CONV(testc "VAL13 #0000000000111");;

let th7 = V_RULE(test "V [F;F;T;F;F]");;
let th7' = V_CONV(testc "V [F;F;T;F;F]");;

let th8 = SEG_RULE(test "SEG(0,4)[1;2;3;4;5;6;7]");;
let th8' = SEG_CONV(testc "SEG(0,4)[1;2;3;4;5;6;7]");;

let th9 = AND_RULE(test "#11000 AND5 #01111");;
let th9' = AND_CONV(testc "#11000 AND5 #01111");;

let th10 = OR_RULE(test "#11000 OR5 #01111");;
let th10' = OR_CONV(testc "#11000 OR5 #01111");;

let th11 = NOT_RULE(test "NOT5 #11100");;
let th11' = NOT_CONV(testc "NOT5 #11100");;

let th121 = COND_RULE(test "T=>2|3");;
let th121' = COND_CONV(testc "T=>2|3");;

let th122 = COND_RULE(test "F=>2|3");;
let th122' = COND_CONV(testc "F=>2|3");;

let th123 = COND_RULE(test "b=>2|2");;
let th123' = COND_CONV(testc "b=>2|2");;

let th131 = U_RULE(test "FLOAT5 U5 x");;
let th131' = U_CONV(testc "FLOAT5 U5 x");;

let th132 = U_RULE(test "y U5 FLOAT5");;
let th132' = U_CONV(testc "y U5 FLOAT5");;

let th133 = U_RULE(test "y U5 y");;
let th133' = U_CONV(testc "y U5 y");;

let th14 = TRI_RULE(test "DEST_TRI13(MK_TRI13  w)");;
let th14' = TRI_CONV(testc "DEST_TRI13(MK_TRI13  w)");;


let get_rhs tm = snd(dest_equiv(concl tm));;

map (\th.(get_rhs th, type_of(get_rhs th)))
    [th1;th2;th31;th32;th4;th5;th6;th7;th8;th9;th10;th11;
     th121;th122;th131;th132;th14];;

let th15 = bool_RULE(test "~T");;
let th15' = bool_CONV(testc "~T");;

let th16 = bool_RULE(test "~F");;
let th16' = bool_CONV(testc "~F");;

let th17 = bool_RULE(test "~x");;
let th17' = bool_CONV(testc "~x");;

let th18 = bool_RULE(test "T /\ x");;
let th18' = bool_CONV(testc "T /\ x");;

let th19 = bool_RULE(test "F /\ x");;
let th19' = bool_CONV(testc "F /\ x");;

let th20 = bool_RULE(test "x /\ T");;
let th20' = bool_CONV(testc "x /\ T");;

let th21 = bool_RULE(test "x /\ F");;
let th21' = bool_CONV(testc "x /\ F");;

let th22 = bool_RULE(test "T \/ x");;
let th22' = bool_CONV(testc "T \/ x");;

let th23 = bool_RULE(test "F \/ x");;
let th23' = bool_CONV(testc "F \/ x");;

let th24 = bool_RULE(test "x \/ T");;
let th24' = bool_CONV(testc "x \/ T");;

let th25 = bool_RULE(test "x \/ F");;
let th25' = bool_CONV(testc "x \/ F");;

let th26 = bool_RULE(test "T ==> x");;
let th26' = bool_CONV(testc "T ==> x");;

let th27 = bool_RULE(test "F ==> x");;
let th27' = bool_CONV(testc "F ==> x");;

let th28 = bool_RULE(test "x ==> T");;
let th28' = bool_CONV(testc "x ==> T");;

let th29 = bool_RULE(test "x ==> F");;
let th29' = bool_CONV(testc "x ==> F");;




