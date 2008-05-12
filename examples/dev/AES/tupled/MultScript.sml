(*---------------------------------------------------------------------------*)
(* Multipliation by a constant. Recursive, iterative, and table-lookup       *)
(* versions.                                                                 *)
(*---------------------------------------------------------------------------*)

(* For interactive work
  app load ["tablesTheory"];
  open word8Theory pairTheory;
*)

open HolKernel Parse boolLib bossLib word8Theory tablesTheory;

val _ = new_theory "Mult";

val [a,c] = CONJUNCTS XOR8_AC;

(*---------------------------------------------------------------------------*)
(*  Name some more constants                                                 *)
(*---------------------------------------------------------------------------*)

val NINE_def   = Define   `NINE = (F,F,F,F,T,F,F,T)`;
val ONE_B_def  = Define  `ONE_B = (F,F,F,T,T,F,T,T)`;
val EIGHTY_def = Define `EIGHTY = (T,F,F,F,F,F,F,F)`;
val B_HEX_def  = Define  `B_HEX = (F,F,F,F,T,F,T,T)`;
val D_HEX_def  = Define  `D_HEX = (F,F,F,F,T,T,F,T)`;
val E_HEX_def  = Define  `E_HEX = (F,F,F,F,T,T,T,F)`;


(*---------------------------------------------------------------------------
    Multiply a byte (representing a polynomial) by x. 

   xtime b = (LeftShift b) 
                # 
             (case BYTE_COMPARE b EIGHTY
               of LESS  -> ZERO 
               || other -> ONE_B)

 ---------------------------------------------------------------------------*)

val xtime_def = Define
  `xtime ((b7,b6,b5,b4,b3,b2,b1,b0) :word8)
     =
   if b7 then (b6,b5,b4,~b3,~b2,b1,~b0,T)
         else (b6,b5,b4,b3,b2,b1,b0,F)`;

val xtime_distrib = Q.store_thm
("xtime_distrib",
 `!a b. xtime (a # b) = (xtime a) # (xtime b)`,
 SIMP_TAC std_ss [FORALL_BYTE_VARS,XOR8_def] 
   THEN RW_TAC std_ss [xtime_def, XOR8_def, XOR_def] 
   THEN DECIDE_TAC);

(*---------------------------------------------------------------------------*)
(* Multiplication by a constant                                              *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "**" (Infixl 675);

val (ConstMult_def,ConstMult_ind) = 
 Defn.tprove
  (Hol_defn "ConstMult"
     `b1 ** b2 =
        if b1 = ZERO then ZERO else 
        if (b1 & ONE) = ONE 
           then b2 # (RightShift b1 ** xtime b2)
           else      (RightShift b1 ** xtime b2)`,
   WF_REL_TAC `measure (BYTE_TO_NUM o FST)` THEN 
   NTAC 10 PairRules.PSTRIP_TAC             THEN
   SIMP_TAC arith_ss [FORALL_BYTE_VARS]     THEN 
   RW_TAC arith_ss [ZERO_def,RightShift_def,BYTE_TO_NUM_def] THEN 
   RW_TAC arith_ss [B2N_def]);

val _ = save_thm("ConstMult_def",ConstMult_def);
val _ = save_thm("ConstMult_ind",ConstMult_ind);
val _ = computeLib.add_persistent_funs [("ConstMult_def",ConstMult_def)];

val ConstMultDistrib = Q.store_thm
("ConstMultDistrib",
 `!x y z. x ** (y # z) = (x ** y) # (x ** z)`,
 recInduct ConstMult_ind
   THEN REPEAT STRIP_TAC
   THEN ONCE_REWRITE_TAC [ConstMult_def]
   THEN RW_TAC std_ss [XOR8_ZERO,xtime_distrib,AC a c]);

(*---------------------------------------------------------------------------*)
(* Iterative version                                                         *)
(*---------------------------------------------------------------------------*)

val defn = Hol_defn 
  "IterConstMult"
  `IterConstMult (b1,b2,acc) =
     if b1 = ZERO then (b1,b2,acc)
     else IterConstMult (RightShift b1, xtime b2,
                         if (b1 & ONE) = ONE 
                          then (b2 # acc) else acc)`;

val (IterConstMult_def,IterConstMult_ind) = 
 Defn.tprove
  (defn,
   WF_REL_TAC `measure (BYTE_TO_NUM o FST)` THEN 
   NTAC 10 PairRules.PSTRIP_TAC             THEN
   SIMP_TAC arith_ss [FORALL_BYTE_VARS]     THEN 
   RW_TAC arith_ss [ZERO_def,RightShift_def,BYTE_TO_NUM_def] THEN 
   RW_TAC arith_ss [B2N_def]);

val _ = save_thm("IterConstMult_def",IterConstMult_def);
val _ = save_thm("IterConstMult_ind",IterConstMult_ind);
val _ = computeLib.add_persistent_funs [("IterConstMult_def",IterConstMult_def)];

(*---------------------------------------------------------------------------*)
(* Equivalence between recursive and iterative forms.                        *)
(*---------------------------------------------------------------------------*)

val ConstMultEq = Q.store_thm
("ConstMultEq",
 `!b1 b2 acc. (b1 ** b2) # acc = SND(SND(IterConstMult (b1,b2,acc)))`,
 recInduct IterConstMult_ind THEN RW_TAC std_ss []
   THEN ONCE_REWRITE_TAC [ConstMult_def,IterConstMult_def]
   THEN RW_TAC std_ss [XOR8_ZERO,AC a c]
   THEN FULL_SIMP_TAC std_ss [AC a c]);


(*---------------------------------------------------------------------------*)
(* Specialized version, with partially evaluated multiplication. Uses tables *)
(* from tablesTheory.                                                        *)
(*---------------------------------------------------------------------------*) 

val TableConstMult_def = 
 Define
  `tcm x = if x = TWO then GF256_by_2
            else if x = THREE then GF256_by_3
            else if x = NINE then GF256_by_9
            else if x = B_HEX then GF256_by_11
            else if x = D_HEX then GF256_by_13
            else if x = E_HEX then GF256_by_14
            else ARB`;

val tcm_thm = Q.store_thm
 ("tcm_thm",
 `(tcm TWO   = GF256_by_2)  /\
  (tcm THREE = GF256_by_3) /\
  (tcm NINE  = GF256_by_9)  /\
  (tcm B_HEX = GF256_by_11) /\
  (tcm D_HEX = GF256_by_13) /\
  (tcm E_HEX = GF256_by_14)`,
 EVAL_TAC);

(*---------------------------------------------------------------------------*)
(* Directly looking up answers in specialized tables is equivalent to        *)
(* the multiplication algorithm each time. And should be much faster!        *)
(*---------------------------------------------------------------------------*)

val MultEquiv = Count.apply Q.store_thm
 ("MultEquiv",
  `!b. (tcm TWO b   = TWO ** b) /\
       (tcm THREE b = THREE ** b)/\
       (tcm NINE b  = NINE ** b)/\
       (tcm B_HEX b = B_HEX ** b)/\
       (tcm D_HEX b = D_HEX ** b)/\
       (tcm E_HEX b = E_HEX ** b)`,
 SIMP_TAC std_ss [FORALL_BYTE_BITS] THEN EVAL_TAC);

(*---------------------------------------------------------------------------*)
(* Exponentiation                                                            *)
(*---------------------------------------------------------------------------*)

val PolyExp_def = 
 Define
   `PolyExp x n = if n=0 then ONE else x ** PolyExp x (n-1)`;


val _ = export_theory();
