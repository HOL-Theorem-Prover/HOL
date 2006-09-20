(* ---------------------------------------------------------------
Booth multiplier adapted from boothTheory by Anthony Fox

This approach simply converts Anthony's definitions
into the language accepted by hwDefine.

All definitions have the suffix "d" (for "Device")
to differentiate them from their original version
(e.g, Anthony's definition of ALU becomes ALUd).

The main function takes the input (a,rm,rs,rn)
and computes (rm * rs + (if a then rn else 0w)).
--------------------------------------------------------------- *)


(* ---------------------------------------------------------------
   Compilation
--------------------------------------------------------------- *)
(*
quietdec := true;
loadPath := ".." :: "../dff" :: !loadPath;
map load
 ["inlineCompile","fpgaCodeGenerator",
  "word32Theory","boothTheory","compile","metisLib",
  "arithmeticTheory","intLib","vsynth"];
open boothTheory vsynth compile metisLib inlineCompile;
val _ = intLib.deprecate_int();
val _ = (if_print_flag := false);
quietdec := false;
*)


(*-----------------------------------------------------------------------------
  Boilerplate needed for compilation
-----------------------------------------------------------------------------*)
open HolKernel Parse boolLib bossLib metisLib;


(* ---------------------------------------------------------------
   Open theories
--------------------------------------------------------------- *)
open word32Theory boothTheory compile metisLib intLib 
     vsynth arithmeticTheory inlineCompile
     fpgaCodeGenerator;


(*-----------------------------------------------------------------------------
  Set default parsing to natural numbers rather than integers
-----------------------------------------------------------------------------*)
val _ = intLib.deprecate_int();

(*---------------------------------------------------------------------------*)
(* END BOILERPLATE                                                           *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Start new theory "boothDev"                                               *)
(*---------------------------------------------------------------------------*)
val _ = new_theory "boothDev"; 
infixr 3 THENR;
val _ = type_abbrev("word",``:word32``);

(*---------------------------------------------------------------------------*)
(* Converts the value of HB_def into a string                                *)
(*---------------------------------------------------------------------------*)
fun HB() = let fun tm2str tm = let val saved_val = !show_types
                                   val _ = (show_types := false)
                                   val s = Parse.term_to_string tm
                                   val _ = (show_types := saved_val)
                               in s 
                               end
           in tm2str ((snd o dest_eq o snd o dest_thm) HB_def)
           end;

val _ = add_vsynth 
 [(``\(sw:bool,in1:num,in2:num). if sw then in1 else in2``,
    (fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3))),
  (``\(sw:bool,in1:word,in2:word). if sw then in1 else in2``,
    (fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3))),
  (``\(sw:bool,in1:bool,in2:bool). if sw then in1 else in2``,
    (fn [i1,i2,i3] => (i1 ^ " ? " ^ i2 ^ " : " ^ i3))),
  (``(UNCURRY ($= :num->num->bool))``,(fn[inp1,inp2] => inp1 ^ " == " ^ inp2)),
  (``(UNCURRY ($+ :num->num->num))``,(fn[inp1,inp2] => inp1 ^ " + " ^ inp2)),
  (``(UNCURRY ($+ :word->word->word))``,(fn[inp1,inp2] => inp1 ^ " + " ^ inp2)),
  (``(UNCURRY ($MOD :num->num->num))``,(fn[inp1,inp2] => inp1 ^ " % " ^ inp2)),
  (``(UNCURRY ($* :num->num->num))``,(fn[inp1,inp2] => inp1 ^ " * " ^ inp2)),
  (``(UNCURRY ($<< :word->num->word))``,(fn[inp1,inp2] => inp1 ^ " << " ^ inp2)),
  (``(UNCURRY ($- :word->word->word))``,(fn[inp1,inp2] => inp1 ^ " - " ^ inp2)),
  (``(UNCURRY ($- :num->num->num))``,(fn[inp1,inp2] => inp1 ^ " - " ^ inp2)),
  (``(UNCURRY BIT)``,(fn[inp1,inp2] => ("("^inp2^" << ("^HB()^"-" ^inp1^")) >> "^HB()))),
  (``(UNCURRY ($DIV :num->num->num))``,(fn[inp1,inp2] => inp1 ^ " / " ^ inp2)),
  (``(UNCURRY $/\)``,(fn[inp1,inp2] => inp1 ^ " && " ^ inp2)),
  (``(UNCURRY $\/)``,(fn[inp1,inp2] => inp1 ^ " || " ^ inp2)),
  (``w2n``,(fn[inp] => inp)),
  (``($~ :bool->bool)``,(fn[inp] => ("!" ^ inp))),
  (``(BITS 31 1)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+1)"))),
  (``(BITS 1 0)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-1)) >> (("^HB()^"-1)+0)"))),
  (``(BITS 31 3)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+3)"))),
  (``(BITS 31 5)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+5)"))),
  (``(BITS 31 7)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+7)"))),
  (``(BITS 31 9)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+9)"))),
  (``(BITS 31 11)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+11)"))),
  (``(BITS 31 13)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+13)"))),
  (``(BITS 31 15)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+15)"))),
  (``(BITS 31 17)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+17)"))),
  (``(BITS 31 19)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+19)"))),
  (``(BITS 31 21)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+21)"))),
  (``(BITS 31 23)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+23)"))),
  (``(BITS 31 25)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+25)"))),
  (``(BITS 31 27)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+27)"))),
  (``(BITS 31 29)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+29)"))),
  (``(BITS HB 02)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-" ^ HB()^")) >> (("^HB()^"-"^HB()^")+2)"))),
  (``(BITS 31 02)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-31)) >> (("^HB()^"-31)+2)"))),
  (``(BITS (HB-2) 0)``, 
      (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-(" ^ HB()^"-2))) >> (("^HB()^"-("^HB()^"-2))+0)"))),
  (``(BITS 29 0)``, 
       (fn[inp] => ("(" ^ inp ^ " << (" ^ HB() ^ "-29)) >> (("^HB()^"-29)+0)")))
 ];


(*****************************************************************************)
(* Turn of COMB_SYNTH_COMB messages                                          *)
(*****************************************************************************)
val _ = (if_print_flag := false);

(* ---------------------------------------------------------------
   MOD_CNTWd counts the number of shifts to be performed
   by MSHIFTd (it computes the argument count1 --- see the
   functions MSHIFTd and NEXTd).
   The constant WL is the word length.
--------------------------------------------------------------- *)

val _ = add_combinational ["MOD","WL","DIV","*","uBITS","BITS","HB","w2n","n2w",
                           "word_lsl","word_mul","word_add","word_sub",
                           "HB","BITT","BITTT"];

val (MOD_CNTWd_def,_,MOD_CNTWd_dev,MOD_CNTWd_comb,_) = hwDefine2

    `MOD_CNTWd n = n MOD (WL DIV 2)`;

<<<<<<< boothDevScript.sml
val MOD_CNTWd_cir =
 MAKE_NETLIST (REFINE (DEPTHR ATM_REFINE) MOD_CNTWd_dev);
 MY_NETLIST [] (REFINE (DEPTHR ATM_REFINE) MOD_CNTWd_dev);
=======

>>>>>>> 1.7

(* ---------------------------------------------------------------
   MSHIFTd
--------------------------------------------------------------- *)
val (MSHIFTd_def,_,MSHIFTd_dev,MSHIFTd_comb,_) = hwDefine2

    `MSHIFTd(borrow,mul,count1) = count1 * 2 +
                     if borrow /\ (mul=1) \/
                        ~borrow /\ (mul=2) then 1 else 0`;


(* ---------------------------------------------------------------
   ALUd
--------------------------------------------------------------- *)

val (ALUd_def,_,ALUd_dev,ALUd_comb,_) = hwDefine2

    `ALUd(borrow2,mul,alua,alub) =
                  if ~borrow2 /\ (mul = 0) \/
                     borrow2 /\ (mul = 3) then
                     alua
                  else if borrow2 /\ (mul = 0) \/ (mul = 1) then
                     alua + alub
                  else
                     alua - alub`;

<<<<<<< boothDevScript.sml
val ALUd_cir =
 MAKE_NETLIST (REFINE (DEPTHR ATM_REFINE) ALUd_dev);
 MY_NETLIST [] (REFINE (DEPTHR ATM_REFINE) ALUd_dev);
=======
>>>>>>> 1.7

(* ---------------------------------------------------------------
   INITd
   The initialisation function takes the input
   (a,rm,rs,rn) and returns the initial state
   (mul:num, mul2:num, borrow2:bool, mshift:num, rm:word,rd:word).
   The variable rd stores the result of the multiplication.
--------------------------------------------------------------- *)

val (INITd_def,_,INITd_dev,INITd_comb,_) = hwDefine2

    `INITd(a,rm:word,rs,rn) = (BITS 1 0 (w2n rs),
                               BITS HB 2 (w2n rs),
                               F,
                               if (BITS 1 0 (w2n rs)) = 2 then 1 else 0,
                               rm,
                               if a then rn else 0w)`;

<<<<<<< boothDevScript.sml
val INITd_cir =
 MAKE_NETLIST (REFINE (DEPTHR ATM_REFINE) INITd_dev);
 MY_NETLIST [] (REFINE (DEPTHR ATM_REFINE) INITd_dev);
=======
>>>>>>> 1.7

(* ---------------------------------------------------------------
   NEXTd computes the next state from the current one
--------------------------------------------------------------- *)
val (NEXTd_def,_,NEXTd_dev,NEXTd_comb,_) = hwDefine2
    `NEXTd(mul,mul2,borrow2,mshift,rm:word,rd) =
                   (BITS 1 0 (BITS (HB-2) 0 mul2),
                    BITS HB 2 (BITS (HB-2) 0 mul2),
                    BIT 1 mul,
                    MSHIFTd(BIT 1 mul,
                            BITS 1 0 (BITS (HB-2) 0 mul2),
                            MOD_CNTWd (mshift DIV 2 +1)),
                    rm,
                    ALUd(borrow2,mul,rd,rm << mshift))`;


(* ---------------------------------------------------------------
   APPLY_NEXTd applies the next state function t times
--------------------------------------------------------------- *)
val (APPLY_NEXTd_def,_,APPLY_NEXTd_dev,
     APPLY_NEXTd_comb,APPLY_NEXTd_tot) = hwDefine2

   `(APPLY_NEXTd(t,inp) = if t=0 then inp
                          else APPLY_NEXTd(t-1,NEXTd inp))
    measuring FST`;


(* ---------------------------------------------------------------
   STATEd computes the initial state and applies the next
   state function t times
--------------------------------------------------------------- *)
val (STATEd_def,_,STATEd_dev,STATEd_comb,_) = hwDefine2

    `STATEd(t,(a,rm,rs,rn)) = APPLY_NEXTd(t,INITd(a,rm,rs,rn))`;


(* ---------------------------------------------------------------
   DURd returns the duration or the number of transitions
   taken for the state-machine to compute the multiplication.
--------------------------------------------------------------- *)
val (DURd_def,_,DURd_dev,DURd_comb,_) = hwDefine2

    `DURd w = if      BITS 31  1 (w2n w) = 0 then  1
              else if BITS 31  3 (w2n w) = 0 then  2
              else if BITS 31  5 (w2n w) = 0 then  3
              else if BITS 31  7 (w2n w) = 0 then  4
              else if BITS 31  9 (w2n w) = 0 then  5
              else if BITS 31 11 (w2n w) = 0 then  6
              else if BITS 31 13 (w2n w) = 0 then  7
              else if BITS 31 15 (w2n w) = 0 then  8
              else if BITS 31 17 (w2n w) = 0 then  9
              else if BITS 31 19 (w2n w) = 0 then 10
              else if BITS 31 21 (w2n w) = 0 then 11
              else if BITS 31 23 (w2n w) = 0 then 12
              else if BITS 31 25 (w2n w) = 0 then 13
              else if BITS 31 27 (w2n w) = 0 then 14
              else if BITS 31 29 (w2n w) = 0 then 15
              else 16`;


(* ---------------------------------------------------------------
   PROJ_RDd projects the result of the multiplication from
   the state
--------------------------------------------------------------- *)
<<<<<<< boothDevScript.sml
val (PROJ_RDd_def,_,PROJ_RDd_dev) = hwDefine
=======
val (PROJ_RDd_def,_,PROJ_RDd_dev,PROJ_RDd_comb,_) = hwDefine2

>>>>>>> 1.7
    `PROJ_RDd(mul:num, mul2:num, borrow2:bool,
              mshift:num, rm:word32, rd:word32) = rd`;


(* ---------------------------------------------------------------
   BOOTHMULTIPLYd
   The correctness theorem for the original BOOTHMULTIPLY states
   that |- BOOTHMULTPLY a rm rs rn
           = (rm * rs + (if a then rn else 0w))
--------------------------------------------------------------- *)
val (BOOTHMULTIPLYd_def,_,BOOTHMULTIPLYd_dev,
     BOOTHMULTIPLYd_comb,_) = hwDefine2

    `BOOTHMULTIPLYd(a,rm,rs,rn) = PROJ_RDd(STATEd(DURd rs,a,rm,rs,rn))`;



(* ---------------------------------------------------------------
   MULTd is the main function.
--------------------------------------------------------------- *)
val (MULTd_def,_,MULTd_dev,MULTd_comb,_) = hwDefine2

    `MULTd(a,b) = BOOTHMULTIPLYd(F,a,b,0w)`;



(* ---------------------------------------------------------------
   Refinement
   The atomic operators are:
   w2n, BIT, BITS, =, -, DIV 2, +, MOD, * 2, /\, ~, \/, <<
--------------------------------------------------------------- *)
val MULTd_dev = save_thm("MULTd_dev",
         REFINE (DEPTHR (LIB_REFINE [BOOTHMULTIPLYd_dev])
                THENR DEPTHR (LIB_REFINE [DURd_dev,STATEd_dev,PROJ_RDd_dev])
                THENR DEPTHR (LIB_REFINE [INITd_dev,APPLY_NEXTd_dev])
                THENR DEPTHR (LIB_REFINE [NEXTd_dev])
                THENR DEPTHR (LIB_REFINE [ALUd_dev,MSHIFTd_dev,MOD_CNTWd_dev])
                THENR DEPTHR ATM_REFINE) MULTd_dev);


(* ---------------------------------------------------------------
   Proofs
--------------------------------------------------------------- *)

(* ---------------------------------------------------------------
   MOD_CNTWd = MOD_CNTW
--------------------------------------------------------------- *)
val MOD_CNTW_EQ = store_thm("MOD_CNTW_EQ",
    ``MOD_CNTWd = MOD_CNTW``,
    METIS_TAC [MOD_CNTWd_def,MOD_CNTW_def]);


(* ---------------------------------------------------------------
   MSHIFTd(a,b,c) = MSHIFT a b c
--------------------------------------------------------------- *)
val MSHIFT_EQ = store_thm("MSHIFT_EQ",
    ``!a b c. MSHIFTd(a,b,c) = (MSHIFT a b c)``,
    RW_TAC arith_ss [MSHIFTd_def,MSHIFT_def]);


(* ---------------------------------------------------------------
   ALUd(a,b,c,d) = ALU a b c d
--------------------------------------------------------------- *)
val ALU_EQ = store_thm("ALU_EQ",
    ``!a b c d. ALUd(a,b,c,d) = (ALU a b c d)``,
    RW_TAC arith_ss [ALUd_def,ALU_def]);


(* ---------------------------------------------------------------
   T2B converts a tuple into a state (type state_BOOTH)
--------------------------------------------------------------- *)
val T2B_def = Define `T2B(a,b,c,d,e,f) = BOOTH a b c d e f`;


(* ---------------------------------------------------------------
   T2B(INITd(a,b,c,d)) = INIT a b c d
--------------------------------------------------------------- *)
val INIT_EQ = store_thm("INIT_EQ",
    ``!a b c d. T2B(INITd(a,b,c,d)) = (INIT a b c d)``,
    RW_TAC arith_ss [T2B_def,INITd_def,INIT_def]
    THEN `(mul1 = w2n c) /\ (count1 = 0) /\
          (mul = BITS 1 count1 mul1) /\ 
          (mshift = (if mul = 2 then 1 else count1))`
           by RW_TAC arith_ss [] 
    THEN RW_TAC arith_ss []);


(* ---------------------------------------------------------------
   T2B(NEXTd a) = NEXT(T2B a)
--------------------------------------------------------------- *)
val NEXT_EQ = store_thm("NEXT_EQ",
    ``!a. T2B(NEXTd a) = (NEXT (T2B a))``,
    Cases_on `a`
    THEN Cases_on `r`
    THEN Cases_on `r1`
    THEN Cases_on `r`
    THEN Cases_on `r1`
    THEN RW_TAC arith_ss [NEXTd_def,NEXT_def,T2B_def]
    THEN `(mshift' = MSHIFT borrow mul' count1) /\
          (count1 = MOD_CNTW (q3 DIV 2 + 1)) /\
          (rd' = ALU q2 q r alub)` by RW_TAC arith_ss []
    THEN RW_TAC arith_ss [MSHIFT_EQ,MOD_CNTW_EQ,ALU_EQ]);



(* ---------------------------------------------------------------
   T2B(STATEd(a,b,c,d,e)) = STATE a b c d e

   This theorem makes use of some definitions and lemmas.
--------------------------------------------------------------- *)

(* ---------------------------------------------
   (fEXP f n) applies f n times to some input
--------------------------------------------- *)
val fEXP_def = Define 
  `(fEXP f 0 = (\x.x)) /\
   (fEXP f (SUC n) = ((fEXP f n) o f))`;

(* ---------------------------------------------
   fEXP_LEMMA
--------------------------------------------- *)
val fEXP_LEMMA = store_thm("fEXP_LEMMA",
    ``!f n inp. f (fEXP f n inp)
                = (fEXP f (SUC n) inp)``,
    Induct_on `n`
    THEN METIS_TAC [fEXP_def,o_THM]);

(* ---------------------------------------------
   fEXP_NEXT
--------------------------------------------- *)
val fEXP_NEXT = store_thm("fEXP_NEXT",
    ``!a. T2B(fEXP NEXTd n a) = fEXP NEXT n (T2B a)``,
    Induct_on `n`
    THENL [
          METIS_TAC[fEXP_def]
          ,
          RW_TAC arith_ss [fEXP_def]
          THEN REPEAT GEN_TAC
          THEN METIS_TAC [fEXP_def,o_THM,NEXT_EQ]
          ]);

(* ---------------------------------------------
   fEXP_APPLY_NEXTd
--------------------------------------------- *)
val fEXP_APPLY_NEXTd = store_thm("fEXP_APPLY_NEXTd",
    ``!n inp. APPLY_NEXTd (n,inp) = fEXP NEXTd n inp``,
    Induct_on `n`
    THENL [
          METIS_TAC [APPLY_NEXTd_def,fEXP_def]
          ,
          `~(SUC n = 0) /\ (SUC n - 1 = n)` 
                by RW_TAC arith_ss []
          THEN METIS_TAC [APPLY_NEXTd_def,fEXP_def,
                          o_THM,NEXT_EQ]
          ]);

(* ---------------------------------------------
   fEXP_STATE
--------------------------------------------- *)
val fEXP_STATE = store_thm("fEXP_STATE",
    ``!n b c d e. STATE n b c d e
                  = (fEXP NEXT n (INIT b c d e))``,
    Induct_on `n`
    THEN METIS_TAC [STATE_def,fEXP_def,fEXP_LEMMA]);

(* --------------------------------------------
   T2B(STATEd(a,b,c,d,e)) = STATE a b c d e
-------------------------------------------- *)
val STATE_EQ = store_thm("STATE_EQ",
    ``!a b c d e. T2B(STATEd(a,b,c,d,e)) = (STATE a b c d e)``,
    REPEAT GEN_TAC
    THEN `T2B(STATEd(a,b,c,d,e)) = (fEXP NEXT a (T2B(INITd(b,c,d,e))))`
        by METIS_TAC [STATEd_def,APPLY_NEXTd_def,fEXP_APPLY_NEXTd,fEXP_NEXT]
    THEN METIS_TAC [INIT_EQ,fEXP_STATE]);



(* ---------------------------------------------------------------
   DURd = DUR
--------------------------------------------------------------- *)
val DUR_EQ = store_thm("DUR_EQ",
    ``DUR = DURd``,
    `!w. DUR w = DURd w` by REWRITE_TAC []
    THENL [GEN_TAC
           THEN `w = n2w(w2n w)` by METIS_TAC [word32Theory.w2n_ELIM]
           THEN RW_TAC std_ss [DURd_def]
           THEN METIS_TAC [DUR_EVAL]
           ,
           METIS_TAC []
          ]);




(* ---------------------------------------------------------------
   PROJ_RDd a = PROJ_RD(T2B a)
--------------------------------------------------------------- *)
val PROJ_RD_EQ = store_thm("PROJ_RD_EQ",
    ``!a. PROJ_RDd a = PROJ_RD(T2B a)``,
    Cases_on `a` THEN
    Cases_on `r` THEN
    Cases_on `r1` THEN
    Cases_on `r` THEN
    Cases_on `r1` THEN
    RW_TAC arith_ss [PROJ_RDd_def,PROJ_RD_def,T2B_def]);

  

(* ---------------------------------------------------------------
   BOOTHMULTIPLYd(a,b,c,d) = BOOTHMULTIPLY a b c d
--------------------------------------------------------------- *)
val BOOTHMULTIPLY_EQ = store_thm("BOOTHMULTIPLY_EQ",
    ``!a b c d. BOOTHMULTIPLYd(a,b,c,d) = (BOOTHMULTIPLY a b c d)``,
    `!a b c d. STATE (DURd c) a b c d = (T2B(STATEd(DURd c,a,b,c,d)))`
          by METIS_TAC [STATE_EQ]
    THEN `!a b c d. PROJ_RD(STATE (DURd c) a b c d)
                    = (PROJ_RD(T2B(STATEd(DURd c,a,b,c,d))))`
         by METIS_TAC [STATE_EQ]
    THEN RW_TAC arith_ss [BOOTHMULTIPLYd_def,BOOTHMULTIPLY_def,DUR_EQ]
    THEN METIS_TAC [PROJ_RD_EQ]);



(* ---------------------------------------------------------------
   Define 
    |- MULT32(w1,w2) = w1 * w2 
   to avoid pretty printer problems
--------------------------------------------------------------- *)
val MULT32_def =
 Define
  `MULT32(w1,w2) = w1 * w2`;

(* ---------------------------------------------------------------
   MULTd = MULT32
--------------------------------------------------------------- *)
val MULTd_CORRECT = store_thm("MULTd_CORRECT",
    ``MULTd = MULT32``,
    `MULT32 = UNCURRY $*`
      by RW_TAC std_ss [FUN_EQ_THM,UNCURRY,MULT32_def,FORALL_PROD]
    THEN POP_ASSUM(fn th => RW_TAC std_ss [th])
    THEN `!a b. MULTd(a,b) = a*b` 
           by METIS_TAC [MULTd_def,BOOTHMULTIPLY_EQ,CORRECT,word32Theory.WORD_ADD_0]
    THEN `!a b. MULTd(a,b) = a*b` by METIS_TAC [MULTd_def, CORRECT, BOOTHMULTIPLY_EQ]
    THEN `!a b. (\p. MULTd p = UNCURRY $* p) (a,b)` by RW_TAC arith_ss []
    THEN `?P. P = (\p. MULTd p = UNCURRY $* p)` by RW_TAC arith_ss []
    THEN `!p. (\p. MULTd p = UNCURRY $* p) p` by METIS_TAC [pair_induction]
    THEN `!p. MULTd p = UNCURRY $* p` by metisLib.METIS_TAC [pair_induction]
    THEN PROVE_TAC [(PairRules.PEXT (ASSUME ``!p. MULTd p = UNCURRY $* p``))]);

(* ---------------------------------------------------------------
   Circuit ===> Dev MULT32
--------------------------------------------------------------- *)
val MULTd_dev0 = save_thm("MULTd",
        REWRITE_RULE [MULTd_CORRECT] MULTd_dev);

val MULTd_dev = inlineCompile (fst(dest_eq(concl MULTd_comb)))
                           [BOOTHMULTIPLYd_comb,
                            DURd_comb,STATEd_comb,PROJ_RDd_comb,
                            INITd_comb,APPLY_NEXTd_comb,
                            NEXTd_comb,ALUd_comb,MSHIFTd_comb,
                            MOD_CNTWd_comb, MULTd_comb]
                           [APPLY_NEXTd_tot];

(* runtime: 39.867s,    gctime: 14.104s,     systime: 0.155s.   
val MULTd_net = time MAKE_NETLIST MULTd_dev;
time (MY_NETLIST []) MULTd_dev;

 Takes rather a long time:
val MULTd_cir = time MAKE_CIRCUIT MULTd_dev;
val MULTd_cir = MAKE_CIRCUIT ((SIMP_RULE std_ss [DIVISION,WL_def,HB_def])
                               MULTd_dev);
*)

val MULTd_cir = NEW_MAKE_CIRCUIT ((SIMP_RULE std_ss [DIVISION,WL_def,HB_def])
                              MULTd_dev);

(*
val _ = PRINT_VERILOG MULTd_cir;

val _ = load "fpgaCodeGenerator";
val _ = fpgaCodeGenerator.programFPGA MULTd_cir;
*)


(* Simulation
val period  = 5;
val file_name = "MULTd_SIM";
val thm = MULTd_cir;
val stimulus =[("inp1", "5"),("inp2","7")];
val name = "MULTd_SIM";
val dump_all = true;

printToFile "MULTd_SIM.vl" (MAKE_SIMULATION name thm period stimulus dump_all);
*)


(*****************************************************************************)
(* Temporary hack to work around a system prettyprinter bug                  *)
(*****************************************************************************)
val _ = temp_overload_on(" * ", numSyntax.mult_tm);

val _ = export_theory();
