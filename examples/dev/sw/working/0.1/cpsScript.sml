(*===========================================================================*)
(* Applying CPS to semantics-based ASTs for a simple WHILE language          *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib relationTheory;

val _ = new_theory "cps";

(*---------------------------------------------------------------------------*)
(* Combinator-based pseudo-ASTs for simple programs                          *)
(*---------------------------------------------------------------------------*)

val Seq_def =
  Define 
   `Seq (f1:'a->'b) (f2:'b->'c) = \x. f2(f1 x)`;

val Par_def =
 Define 
   `Par f1 f2 = \x. (f1 x, f2 x)`;

val Ite_def =
 Define 
   `Ite f1 f2 f3 = \x. if f1 x then f2 x else f3 x`;

val Rec_def = 
 TotalDefn.DefineSchema 
   `Rec (x:'a) = if f1 x then f2 x else Rec (f3 x)`;

val Rec_ind = fetch "-" "Rec_ind";


(*---------------------------------------------------------------------------*)
(* CPS definitions. The invocation "CPS f" wraps a function in a CPS, in     *)
(* analogy with DEV for hardware. CPS-ified functions are intended to be     *)
(* representatives for lower-level implementations.                          *)
(*---------------------------------------------------------------------------*)

val CPS_def = 
  Define 
   `CPS f = \k arg. k (f arg)`;

val CPS_ID = store_thm
("CPS_ID",
 ``CPS (\x.x)  = \k x. k x``, 
 SIMP_TAC std_ss [CPS_def]);

val CPS_CONST = store_thm
("CPS_CONST",
 ``CPS (\x.c)  = \k x. k c``, 
 SIMP_TAC std_ss [CPS_def]);

val UNCPS = store_thm
("UNCPS",
 ``CPS f k = \arg. let z = f arg in k z``,
 METIS_TAC [CPS_def]);

(*---------------------------------------------------------------------------*)
(* Passing the identity function to a CPS function is the inverse of         *)
(* CPSing the function                                                       *)
(*---------------------------------------------------------------------------*)

val CPS_INV = Q.store_thm 
("CPS_INV",
 `(!f g. (f = CPS g) ==> (f = (CPS (\arg. f (\x.x) arg)))) /\
  (!f. f arg = (CPS f) (\x.x) arg)`,
 RW_TAC std_ss [CPS_def] THEN METIS_TAC []);


(*---------------------------------------------------------------------------*)
(* Wrapping a function in a CPS interface that takes 2 continuations.        *)
(* Used in the test expression of an if-then-else                            *)
(*---------------------------------------------------------------------------*)

val CPS2_def = 
  Define
   `CPS2 f = \k1 k2 arg. if f arg then k1 T else k2 F`;

val CPS2_INV = Q.store_thm 
("CPS2_INV",
 `(!f. (?f'. f = CPS2 f') ==> (f = (CPS2 (\arg. f (\x.x) (\x.x) arg)))) /\
  (!f. f arg = (CPS2 f) (\x.x) (\x.x) arg)`,
 RW_TAC std_ss [CPS2_def] THEN METIS_TAC []);


(*---------------------------------------------------------------------------*)
(* CPSing sequential composition                                             *)
(*---------------------------------------------------------------------------*)

val CPS_SEQ_def = 
  Define
   `CPS_SEQ f g = \k arg. f (\ret. g k ret) arg`;

val CPS_SEQ_INTRO = Q.store_thm
("CPS_SEQ_INTRO",
 `!f g. CPS (Seq f g) = CPS_SEQ (CPS f) (CPS g)`,
 RW_TAC std_ss [CPS_def, Seq_def, CPS_SEQ_def, FUN_EQ_THM]);


(*---------------------------------------------------------------------------*)
(* CSPing parallel composition                                               *)
(*---------------------------------------------------------------------------*)

val CPS_PAR_def = 
  Define
   `CPS_PAR f g = \k arg. f (\ret2. g (\ret. k (ret2, ret)) arg) arg`;

val CPS_PAR_INTRO = Q.store_thm
("CPS_PAR_INTRO",
 `!f g. CPS (Par f g) = CPS_PAR (CPS f) (CPS g)`,
 RW_TAC std_ss [CPS_def, Par_def, CPS_PAR_def, FUN_EQ_THM])


(*---------------------------------------------------------------------------*)
(* CPSing if-then-else                                                       *)
(*---------------------------------------------------------------------------*)
(*
val CPS_ITE_def = 
  Define
   `CPS_ITE e f g = \k arg. let k2 = k in e (\ret. f k2 arg) (\ret. g k2 arg) arg`;

val CPS_ITE_INTRO = Q.store_thm
("CPS_ITE_INTRO",
 `!e f g.  CPS (Ite e f g) = CPS_ITE (CPS2 e) (CPS f) (CPS g)`,
 RW_TAC std_ss [CPS_def, CPS2_def, Ite_def, 
                CPS_ITE_def, FUN_EQ_THM, COND_RAND, LET_THM])

val CPS_TEST_def = 
  Define
   `CPS_TEST f = \k1 k2 arg. f (\ret. if ret then k1 ret else k2 ret) arg`;

val CPS2_INTRO = Q.store_thm
("CPS2_INTRO",
 `!f. CPS2 f = CPS_TEST (CPS f)`,
 RW_TAC std_ss [CPS_def, CPS2_def, CPS_TEST_def, FUN_EQ_THM]);
*)

val CPS_ITE_def = 
  Define
   `CPS_ITE e f g = \k arg. e (\ret. let k2 = k in if ret then f k2 arg else g k2 arg) arg`;

val CPS_ITE_INTRO = Q.store_thm
("CPS_ITE_INTRO",
 `!e f g.  CPS (Ite e f g) = CPS_ITE (CPS e) (CPS f) (CPS g)`,
 RW_TAC std_ss [CPS_def, Ite_def, CPS_ITE_def, FUN_EQ_THM, COND_RAND, LET_THM])


(*
(*---------------------------------------------------------------------------*)
(* Recursion. We want                                                        *)
(*                                                                           *)
(* CPS_REC e f g = \arg k. e arg (\ret. f arg k)                             *)
(*                               (\ret. g arg (\ret. CPS_REC e f g ret k))   *)
(*                                                                           *)
(* The termination conditions synthesized by TFL are un-provable.            *)
(*                                                                           *)
(*    Termination conditions :                                               *)
(*      0. !arg k ret. R (ret,k) (arg,k)                                     *)
(*      1. WF R : defn                                                       *)
(*                                                                           *)
(*    If e is a CPS2 term and g is CPS, then ret is the result of            *)
(*    applying g to arg.  We only need to do this if e is false.             *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* The types become heavy in the following, so we introduce some abbrevs     *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev ("cps_fun",  ``:('b -> 'c) -> ('a -> 'c)``)
val _ = type_abbrev ("cps2_fun", ``:(bool->'b) -> (bool->'b) -> 'a -> 'b``);

(*---------------------------------------------------------------------------*)
(* We'll make a series of definitions, purely for sanity's sake.             *)
(*---------------------------------------------------------------------------*)

val CPS_REC_fn_def = Define
`CPS_REC_fn (e: ('a,'b) cps2_fun)
            (f: ('a,'a,'b) cps_fun)
            (g: ('a,'a,'b) cps_fun) =
     \CPS_REC. \(k, arg). e (\ret. f k arg)
                            (\ret. g (\ret. CPS_REC (k, ret)) arg)
                            arg`;

val CPS_REC_TCS_def = Define
`CPS_REC_TCS (R: (('a->'b) # 'a) -> (('a->'b) # 'a) -> bool) 
             (e: ('a,'b) cps2_fun)
             (g: ('a,'a,'b) cps_fun) =
   WF R /\
   (?e' g'. (e = CPS2 e') /\ (g = CPS g') /\
            !k arg. ~(e' arg) ==> R (k,g' arg) (k,arg))`;

val CPS_REC_PRIM_def = 
 Define
   `CPS_REC_PRIM e f g = WFREC (@R. CPS_REC_TCS R e g) (CPS_REC_fn e f g)`;

val CPS_REC_PRIM_THM =
(UNDISCH_ALL o
 SIMP_RULE std_ss [GSYM AND_IMP_INTRO, CPS_REC_TCS_def, CPS_REC_fn_def] o
 SPEC_ALL)
(Q.prove 
(`!R e f g arg k.
  CPS_REC_TCS R e g 
    ==>
  (CPS_REC_PRIM e f g (arg, k) = 
   CPS_REC_fn e f g (CPS_REC_PRIM e f g) (arg, k))`,
 RW_TAC std_ss [Once CPS_REC_PRIM_def] 
  THEN `CPS_REC_TCS (@R. CPS_REC_TCS R e g) e g` by METIS_TAC [SELECT_THM] 
  THEN POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [Once CPS_REC_TCS_def]) 
  THEN RW_TAC std_ss [WFREC_THM, GSYM CPS_REC_PRIM_def] 
  THEN RW_TAC std_ss [Once CPS_REC_fn_def] 
  THEN FULL_SIMP_TAC std_ss [CPS_def, CPS2_def] 
  THEN RW_TAC std_ss [RESTRICT_LEMMA] 
  THEN RW_TAC std_ss [CPS_REC_fn_def])
);

val CPS_REC_def = 
 Define 
   `CPS_REC e f g k arg = CPS_REC_PRIM e f g (k,arg)`;

(*---------------------------------------------------------------------------*)
(* The laborious model-building above finally yields                         *)
(*                                                                           *)
(*     [?e' g'. (e = CPS2 e') /\ (g = CPS g') /\                             *)
(*        !arg k. ~e' arg ==> R (g' arg,k) (arg,k),                          *)
(*      WF R                                                                 *)
(*     ]                                                                     *)
(*    |-                                                                     *)
(*       CPS_REC e f g arg k =                                               *)
(*       e arg (\ret. f arg k)                                               *)
(*             (\ret. g arg (\ret. CPS_REC e f g ret k))                     *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)
 
val CPS_REC_THM = SIMP_RULE std_ss [GSYM CPS_REC_def] CPS_REC_PRIM_THM;

val _ = save_thm("CPS_REC_THM",CPS_REC_THM);


(*---------------------------------------------------------------------------*)
(* We want to connect CPS_REC with while-loops, and need to make their       *)
(* respective termination conditions relate to each other.                   *)
(*---------------------------------------------------------------------------*)

val TC_RELATION = Q.prove
(`(!x:'a. ~e x ==> R (g x) x) /\ WF R ==>
    CPS_REC_TCS (\(x1, y1) (x2, y2). R y1 y2) (CPS2 e) (CPS g)`,
 RW_TAC std_ss [CPS_REC_TCS_def,CPS2_def,CPS_def]
  THENL
  [WEAKEN_TAC is_forall
     THEN IMP_RES_TAC
           (Q.ISPEC `SND:('a->'b)#'a->'a`
           (Q.ID_SPEC
              (INST_TYPE [alpha |-> Type `:('a->'b)#'a`,
                          beta |-> alpha] WF_inv_image)))
     THEN FULL_SIMP_TAC std_ss [pairTheory.LAMBDA_PROD,inv_image_def],
   Q.EXISTS_TAC `e` THEN Q.EXISTS_TAC `g` THEN METIS_TAC[]]);

val lemma = 
  (REWRITE_RULE [GSYM CPS_REC_TCS_def, AND_IMP_INTRO] o DISCH_ALL) CPS_REC_THM;

(*---------------------------------------------------------------------------*)
(* How to CPS While-loops                                                    *)
(*                                                                           *)
(* Note that f has type :'a -> 'a, instead of :'a -> 'b.                     *)
(*---------------------------------------------------------------------------*)

val CPS_REC_INTRO = Q.store_thm
("CPS_REC_INTRO",
 `!e f g. 
    (?R. WF R /\ !x. ~e x ==> R (g x) x)
     ==>
    (CPS (Rec e f g) = CPS_REC (CPS2 e) (CPS f) (CPS g))`,
 REPEAT STRIP_TAC 
  THEN REWRITE_TAC [Once CPS_def] 
  THEN RW_TAC std_ss [Rec_def, FUN_EQ_THM] 
  THEN Q.ID_SPEC_TAC `arg` 
  THEN IMP_RES_TAC (DISCH_ALL Rec_ind) 
  THEN POP_ASSUM HO_MATCH_MP_TAC 
  THEN RW_TAC std_ss [] 
  THEN IMP_RES_TAC (INST_TYPE [beta |-> alpha] (DISCH_ALL Rec_def))
  THEN POP_ASSUM (fn x => ONCE_REWRITE_TAC [x]) 
  THEN IMP_RES_TAC TC_RELATION 
  THEN IMP_RES_TAC lemma
  THEN POP_ASSUM (fn x => ONCE_REWRITE_TAC [x]) 
  THEN RW_TAC std_ss [] 
  THEN FULL_SIMP_TAC std_ss [CPS_def, CPS2_def]);
*)

val CPS_REC_def = Define
`CPS_REC e f g = \k arg. k (Rec (e (\x.x)) (f (\x.x)) (g (\x.x)) arg)` 

val CPS_REC_INTRO = Q.store_thm
("CPS_REC_INTRO",
 `!e f g. CPS (Rec e f g) = CPS_REC (CPS e) (CPS f) (CPS g)`,
 RW_TAC std_ss [CPS_def, CPS_REC_def] THEN
 METIS_TAC [])

(*---------------------------------------------------------------------------*)
(* Support for translation into combinator form.                             *)
(*---------------------------------------------------------------------------*)

val Rec_INTRO = store_thm
("Rec_INTRO",
 ``!f f1 f2 f3.
     (!x:'a. f x = if f1(x) then f2(x) else f(f3 x)) 
     ==> (?R. WF R /\ (!x. ~f1 x ==> R (f3 x) x))
     ==> (f:'a->'b = Rec f1 f2 f3)``,
 REPEAT (GEN_TAC ORELSE STRIP_TAC)
  THEN ONCE_REWRITE_TAC [FUN_EQ_THM]
  THEN HO_MATCH_MP_TAC Rec_ind 
  THEN GEN_TAC THEN STRIP_TAC
  THEN IMP_RES_TAC (DISCH_ALL Rec_def)
  THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC[th])
  THEN METIS_TAC[]);
   
(*---------------------------------------------------------------------------*)
(* Misc. lemmas                                                              *)
(*---------------------------------------------------------------------------*)

val MY_LET_RAND = 
 save_thm
  ("MY_LET_RAND",
    METIS_PROVE []  
     ``!f M N. (let x = M in f (N x)) = f (let x = M in N x)``);

val UNLET = 
 save_thm
  ("UNLET",
   METIS_PROVE [] ``!f M. (let f2 = f in f2 M) = f M``);


val _ = export_theory();
