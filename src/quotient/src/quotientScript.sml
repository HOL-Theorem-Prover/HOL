open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* Version 2.1.                                                          *)
(* Date: February 28, 2005                                               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient";

open prim_recTheory;
open combinTheory;
open pred_setTheory;
open bossLib;
open res_quanTheory;
open res_quanLib;
open dep_rewrite;


val REWRITE_THM = fn th => REWRITE_TAC[th];
val ONCE_REWRITE_THM = fn th => ONCE_REWRITE_TAC[th];
val REWRITE_ALL_THM = fn th => RULE_ASSUM_TAC (REWRITE_RULE[th])
                               THEN REWRITE_TAC[th];

val POP_TAC = POP_ASSUM (fn th => ALL_TAC);


(* =================================================================== *)
(* To form a ABS / REP function or a equivalence relation REL from     *)
(* the corresponding functions/relations of the constituent subtypes   *)
(* of the main type, use the following table of operators:             *)
(*                                                                     *)
(*      Type Operator     Constructor   Abstraction      Equivalence   *)
(*                                                                     *)
(*  Identity                  I x           I                $=        *)
(*  Product  (ty1 # ty2)     (a,b)    (abs1 ## abs2)     (R1 ### R2)   *)
(*  Sum      (ty1 + ty2)    (INL x)   (abs1 ++ abs2)     (R1 +++ R2)   *)
(*  List      (ty list)    (CONS h t)    (MAP abs)       (LIST_REL R)  *)
(*  Option    (ty option)  (SOME x)  (OPTION_MAP abs)   (OPTION_REL R) *)
(*  Function (ty1 -> ty2)  (\x. f x)  (rep1 --> abs2)  (rep1 =-> abs2) *)
(*  (Strong respect)                                     (R1 ===> R2)  *)
(*                                                                     *)
(* =================================================================== *)



val QUOTIENT_def =
    Define
      `QUOTIENT R abs rep =
        (!a:'b. abs (rep a) = a) /\
        (!a. R (rep a) (rep a)) /\
        (!(r:'a) (s:'a). R r s = R r r /\ R s s /\ (abs r = abs s))`;

val QUOTIENT_ABS_REP = store_thm
   ("QUOTIENT_ABS_REP",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==> (!a. abs (rep a) = a)`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
   );

val QUOTIENT_REP_REFL = store_thm
   ("QUOTIENT_REP_REFL",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==>
            (!a. R (rep a) (rep a))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
   );

val QUOTIENT_REL = store_thm
   ("QUOTIENT_REL",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==>
            (!r s. R r s = R r r /\ R s s /\ (abs r = abs s))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
   );

val QUOTIENT_REL_ABS = store_thm
   ("QUOTIENT_REL_ABS",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==>
            (!r s. R r s ==> (abs r = abs s))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
   );

val QUOTIENT_REL_ABS_EQ = store_thm
   ("QUOTIENT_REL_ABS_EQ",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==>
            (!r s. R r r ==> R s s ==>
                   (R r s = (abs r = abs s)))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN POP_ASSUM (fn th => REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[th])
    THEN ASM_REWRITE_TAC[]
   );

val QUOTIENT_REL_REP = store_thm
   ("QUOTIENT_REL_REP",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==>
            (!a b. R (rep a) (rep b) = (a = b))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM ONCE_REWRITE_THM
    THEN ASM_REWRITE_TAC[]
   );


val QUOTIENT_REP_ABS = store_thm
   ("QUOTIENT_REP_ABS",
    (--`!R (abs:'a->'b) rep. QUOTIENT R abs rep ==>
            (!r. R r r ==> R (rep (abs r)) r)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );




val IDENTITY_EQUIV = store_thm
   ("IDENTITY_EQUIV",
    (--`!x y:'a. (x = y) = ($= x = $= y)`--),
    REPEAT GEN_TAC
    THEN EQ_TAC
    THEN DISCH_THEN REWRITE_THM
   );

val IDENTITY_QUOTIENT = store_thm
   ("IDENTITY_QUOTIENT",
    (--`QUOTIENT $= (I:'a->'a) I`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REWRITE_TAC[I_THM]
   );



val EQUIV_REFL_SYM_TRANS = store_thm
   ("EQUIV_REFL_SYM_TRANS",
    (--`!R.
         (!x y:'a. R x y = (R x = R y))
         =
         (!x. R x x) /\
         (!x y. R x y ==> R y x) /\
         (!x y z. R x y /\ R y z ==> R x z)`--),
    GEN_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THENL (* 4 subgoals *)
      [ 
        PURE_ASM_REWRITE_TAC[]
        THEN REFL_TAC,

        PURE_ASM_REWRITE_TAC[]
        THEN MATCH_ACCEPT_TAC EQ_SYM,

        PURE_ASM_REWRITE_TAC[]
        THEN MATCH_ACCEPT_TAC EQ_TRANS,

        CONV_TAC (RAND_CONV FUN_EQ_CONV)
        THEN EQ_TAC
        THEN DISCH_TAC
        THENL
          [ GEN_TAC
            THEN EQ_TAC
            THEN DISCH_TAC
            THEN RES_TAC
            THEN RES_TAC,

            PURE_ASM_REWRITE_TAC[]
          ]
      ]
   );


val QUOTIENT_SYM = store_thm
   ("QUOTIENT_SYM",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x y. R x y ==> R y x`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
    THEN PROVE_TAC[]
   );

val QUOTIENT_TRANS = store_thm
   ("QUOTIENT_TRANS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x y z. R x y /\ R y z ==> R x z`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
    THEN PROVE_TAC[]
   );




(* FUNCTIONS: *)

(* for ABS / REP of functions,
   use (rep --> abs) for ABS, and (abs --> rep) for REP. *)

val FUN_MAP =
    new_infixr_definition
    ("FUN_MAP",
     (--`$--> (f:'a->'c) (g:'b->'d) = \h x. g (h (f x))`--),
     450);

val FUN_MAP_THM = store_thm
   ("FUN_MAP_THM",
    (--`!(f:'a -> 'c) (g:'b -> 'd) h x.
         (f --> g) h x = g (h (f x))`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[FUN_MAP]
    THEN BETA_TAC
    THEN REFL_TAC
   );

val FUN_MAP_I = store_thm
   ("FUN_MAP_I",
    (--`((I:'a->'a) --> (I:'b->'b)) = I`--),
    PURE_ONCE_REWRITE_TAC[FUN_MAP]
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN BETA_TAC
    THEN REWRITE_TAC[I_THM,ETA_AX]
   );

val IN_FUN = store_thm
   ("IN_FUN",
    (--`!(f:'a -> 'b) (g:bool -> bool) s x.
        x IN ((f --> g) s) = g ((f x) IN s)`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[IN_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[FUN_MAP_THM]
   );




(* The strong version of FUN_REL: *)

val FUN_REL =
    new_infixr_definition
    ("FUN_REL",
     (--`$===> (R1:'a->'a->bool) (R2:'b->'b->bool) f g =
           !x y. R1 x y ==> R2 (f x) (g y)`--),
     450);


val FUN_REL_EQ = store_thm
   ("FUN_REL_EQ",
    (--`(($= :'a -> 'a -> bool) ===> ($= :'b -> 'b -> bool)) = $=`--),
    CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[FUN_REL]
    THEN CONV_TAC (RAND_CONV FUN_EQ_CONV)
    THEN PROVE_TAC[]
   );

val FUN_QUOTIENT = store_thm
   ("FUN_QUOTIENT",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         QUOTIENT (R1 ===> R2) (rep1 --> abs2) (abs1 --> rep2)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT CONJ_TAC
    THENL (* 3 subgoals *)
      [ IMP_RES_TAC QUOTIENT_ABS_REP
        THEN GEN_TAC
        THEN CONV_TAC FUN_EQ_CONV
        THEN GEN_TAC
        THEN ASM_REWRITE_TAC[FUN_MAP_THM],

        REWRITE_TAC[FUN_REL]
        THEN REWRITE_TAC[FUN_MAP_THM]
        THEN REPEAT GEN_TAC
        THEN IMP_RES_THEN (fn th =>
                    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) QUOTIENT_REL
        THEN STRIP_TAC
        THEN IMP_RES_TAC QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[],

        REPEAT GEN_TAC
           THEN REWRITE_TAC[FUN_REL]
        THEN CONV_TAC (RAND_CONV (RAND_CONV (RAND_CONV FUN_EQ_CONV)))
        THEN REWRITE_TAC[FUN_REL,FUN_MAP_THM]
        THEN EQ_TAC
        THENL
          [ REPEAT STRIP_TAC
            THENL (* 3 subgoals *)
              [ PROVE_TAC[QUOTIENT_REL],

                PROVE_TAC[QUOTIENT_REL],

                IMP_RES_TAC QUOTIENT_REL_ABS
                THEN FIRST_ASSUM MATCH_MP_TAC
                THEN FIRST_ASSUM MATCH_MP_TAC
                THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
              ],

            STRIP_TAC
            THEN REPEAT GEN_TAC
            THEN DISCH_TAC
            THEN FIRST_ASSUM MP_TAC
            THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
            THEN STRIP_TAC
            THEN REPEAT CONJ_TAC
            THENL (* 3 subgoals *)
              [ FIRST_ASSUM MATCH_MP_TAC
                THEN FIRST_ASSUM ACCEPT_TAC,

                FIRST_ASSUM MATCH_MP_TAC
                THEN FIRST_ASSUM ACCEPT_TAC,

                IMP_RES_TAC QUOTIENT_REP_ABS
                THEN RES_TAC
                THEN IMP_RES_THEN (IMP_RES_THEN (ONCE_REWRITE_THM o GSYM))
                              QUOTIENT_REL_ABS
                THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
                THEN ASM_REWRITE_TAC[]
              ]
          ]
      ]
   );

(* NOTE: R1 ===> R2 is NOT an equivalence relation, but
                    does satisfy a quotient theorem. *)


(* Definition of respectfulness for restricted quantification. *)

val respects_def =
    Define
      `respects = W : ('a -> 'a -> 'b) -> 'a -> 'b`;

(* Tests:

``!f::respects(R1 ===> R2). f 1 = 2``;
``!P::respects($= ===> $=). !n:num. P n``;

*)


val RESPECTS = store_thm
   ("RESPECTS",
    (--`!(R:'a->'a->bool) x.
         respects R x = R x x`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[respects_def,W_THM]
   );

val IN_RESPECTS = store_thm
   ("IN_RESPECTS",
    (--`!(R:'a->'a->bool) x.
         x IN respects R = R x x`--),
    REWRITE_TAC[SPECIFICATION,RESPECTS]
   );

val RESPECTS_THM = store_thm
   ("RESPECTS_THM",
    (--`!R1 R2 (f:'a->'b).
         respects(R1 ===> R2) (f:'a->'b) = !x y. R1 x y ==> R2 (f x) (f y)`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[respects_def,W_THM,FUN_REL]
   );

val RESPECTS_MP = store_thm
   ("RESPECTS_MP",
    (--`!R1 R2 (f:'a->'b) x y.
         respects(R1 ===> R2) f /\ R1 x y
         ==> R2 (f x) (f y)`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[RESPECTS_THM]
    THEN STRIP_TAC
    THEN RES_TAC
   );


val RESPECTS_REP_ABS = store_thm
   ("RESPECTS_REP_ABS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !(R2:'b->'b->bool).
         !f x.
          respects(R1 ===> R2) f /\ R1 x x
          ==> R2 (f (rep1 (abs1 x))) (f x)`--),
    REPEAT STRIP_TAC
    THEN DEP_REWRITE_TAC [RESPECTS_MP]
    THEN EXISTS_TAC ``R1:'a -> 'a -> bool``
    THEN IMP_RES_TAC QUOTIENT_REP_ABS
    THEN ASM_REWRITE_TAC[]
   );

val RESPECTS_o = store_thm
   ("RESPECTS_o",
    (--`!(R1:'a->'a->bool) (R2:'b->'b->bool) (R3:'c->'c->bool).
         !f g.
          respects(R2 ===> R3) f /\ respects(R1 ===> R2) g
          ==> respects(R1 ===> R3) (f o g)`--),
    REWRITE_TAC[RESPECTS_THM]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[o_THM]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );


(*
val EXISTS_EQUIV_DEF =
    Definition.new_definition
    ("EXISTS_EQUIV_DEF", Term `?!! R = \P:'a->bool.
                                       $? P /\ !x y. P x /\ P y ==> R x y`);

val _ = add_const "?!!";

val EXISTS_EQUIV = store_thm
   ("EXISTS_EQUIV",
    (--`!R P.
         ?!! R P = ($? P /\ !x y:'a. P x /\ P y ==> (R x y))`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[EXISTS_EQUIV_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[]
   );

val EXISTS_UNIQUE_EQUIV = store_thm
   ("EXISTS_UNIQUE_EQUIV",
    (--`$?! = ?!! ($= : 'a->'a->bool)`--),
    REWRITE_TAC[EXISTS_UNIQUE_DEF,EXISTS_EQUIV_DEF]
   );

*)

(*
val _ = (add_binder ("?!!", std_binder_precedence); add_const "?!")
*)

val EXISTS_EQUIV_DEF =
    new_binder_definition("?!!", --`?!!(P:'a->bool) = $?! P`--);

val RES_EXISTS_EQUIV_DEF =
 Definition.new_definition
   ("RES_EXISTS_EQUIV_DEF",
    Term `RES_EXISTS_EQUIV =
          \R P. (?(x : 'a) :: respects R. P x) /\
                (!x y :: respects R. P x /\ P y ==> R x y)`);

val _ = add_const "RES_EXISTS_EQUIV";

val _ = associate_restriction ("?!!",  "RES_EXISTS_EQUIV");

(* Tests:
``RES_EXISTS_EQUIV R (\x. x = 5)``;
``?!!x :: R. x = 5``;
*)

val RES_EXISTS_EQUIV = store_thm
   ("RES_EXISTS_EQUIV",
    (--`!R m.
         RES_EXISTS_EQUIV R m =
         (?(x : 'a) :: respects R. m x) /\
         (!x y :: respects R. m x /\ m y ==> (R x y))`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[RES_EXISTS_EQUIV_DEF]
    THEN BETA_TAC
    THEN REFL_TAC
   );

(*
val RES_EXISTS_UNIQUE_EQUIV_REL = store_thm
   ("RES_EXISTS_UNIQUE_EQUIV_REL",
    (--`!R (m:'a -> bool).
         (!x. x IN respects R ==> R x x) /\
         RES_EXISTS_UNIQUE (respects R) m ==>
         RES_EXISTS_EQUIV R m`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[res_quanTheory.RES_EXISTS_UNIQUE,RES_EXISTS_EQUIV]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN STRIP_TAC
    THEN res_quanLib.RESQ_RES_TAC
    THEN RES_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC[]
   );
*)

(*
val RES_EXISTS_UNIQUE_EQUIV_REL = store_thm
   ("RES_EXISTS_UNIQUE_EQUIV_REL",
    (--`!R m.
         RES_EXISTS_UNIQUE (respects R) m ==>
         RES_EXISTS_EQUIV (respects R) R m`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[res_quanTheory.RES_EXISTS_UNIQUE,RES_EXISTS_EQUIV]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN STRIP_TAC
    THEN res_quanLib.RESQ_RES_TAC
    THEN RES_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_ALL_TAC[SPECIFICATION,RESPECTS]
    THEN FIRST_ASSUM ACCEPT_TAC
   );
*)

(* Not needed.

val RES_EXISTS_UNIQUE_EQUIV = store_thm
   ("RES_EXISTS_UNIQUE_EQUIV",
    (--`!p.
         RES_EXISTS_UNIQUE p =
         RES_EXISTS_EQUIV p ($= :'a->'a->bool)`--),
    GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[res_quanTheory.RES_EXISTS_UNIQUE,RES_EXISTS_EQUIV]
   );
*)

(* These don't work becuase of the extra parameter.
``RES_EXISTS_EQUIV
           (ALPHA) (* (\t. ?y u. t = Lam1 y u) *)
           (\t. ?y. t = Lam1 y (Var1 y))
           (ALPHA)``;
``(?!!t :: (\t. ?y u. t = Lam1 y u). ?y. t = Lam1 y (Var1 y))`` handle e => Raise e;
``(?!!t :: (\t. ?y u. t = Lam1 y u). ?y. t = Lam1 y (Var1 y)) (ALPHA)``;

``(?!! (t :: (\t. ?y u. t = Lam1 y u) ALPHA). ?y. t = Lam1 y (Var1 y)))``;

``RES_EXISTS_EQUIV (ALPHA ===> ($= :bool->bool->bool))
           (\x. ?y. x = Lam1 y (Var1 y))``;
*)



val FUN_REL_EQ_REL = store_thm
   ("FUN_REL_EQ_REL",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f g.
         (R1 ===> R2) f g =
         (respects(R1 ===> R2) f /\ respects(R1 ===> R2) g /\
          ((rep1 --> abs2) f = (rep1 --> abs2) g))`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[respects_def,W_THM]
    THEN MATCH_MP_TAC QUOTIENT_REL
    THEN EXISTS_TAC ``(abs1:'a -> 'c) --> (rep2:'d -> 'b)``
    THEN DEP_REWRITE_TAC [FUN_QUOTIENT]
    THEN ASM_REWRITE_TAC[]
   );


val FUN_REL_MP = store_thm
   ("FUN_REL_MP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
        !f g x y.
         (R1 ===> R2) f g /\ (R1 x y)
         ==> (R2 (f x) (g y))`--),
    REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
   );

val FUN_REL_IMP = store_thm
   ("FUN_REL_IMP",
    (--`!(R1:'a->'a->bool) (R2:'b->'b->bool) f g x y.
         (R1 ===> R2) f g /\ (R1 x y)
         ==> (R2 (f x) (g y))`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN RES_TAC
   );


val FUN_REL_EQUALS = store_thm
   ("FUN_REL_EQUALS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f g. respects(R1 ===> R2) f /\ respects(R1 ===> R2) g
         ==> (((rep1 --> abs2) f = (rep1 --> abs2) g) =
              (!x y. R1 x y ==> R2 (f x) (g y)))`--),
    REPEAT GEN_TAC THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN POP_ASSUM ((fn th => DISCH_THEN (ASSUME_TAC o (MATCH_MP th)))
                    o MATCH_MP FUN_QUOTIENT)
    THEN REWRITE_TAC[respects_def,W_THM]
    THEN REWRITE_TAC[GSYM FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_REL_ABS_EQ
    THEN FIRST_ASSUM (ACCEPT_TAC o SYM)
   );


val FUN_REL_IMP = store_thm
   ("FUN_REL_IMP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f g. respects(R1 ===> R2) f /\ respects(R1 ===> R2) g /\
               ((rep1 --> abs2) f = (rep1 --> abs2) g)
               ==> !x y. R1 x y ==> R2 (f x) (g y)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC FUN_REL_EQUALS
   );


(* ============================ *)
(* Main development of SET_REL: *)
(* ============================ *)

(* for set rep or abs, DON'T use (abs --> I) or (rep --> I).  *)
(* No, for set rep or abs, use SET_MAP abs or SET_MAP rep.  *)

val SET_REL_def =
    Define
      `SET_REL (R:'a->'a->bool) = (R ===> ($= :bool->bool->bool))`;

(*
val SET_REL_def =
    Define
      `SET_REL (R:'a->'a->bool) s t = (R ===> ($= :bool->bool->bool)) s t /\
                                      (!x. x IN s \/ x IN t ==> respects R x)`;
*)

val SET_REL = store_thm
   ("SET_REL",
    (--`!(R:'a->'a->bool).
         SET_REL R s t =
           (!x y. R x y ==> ((x IN s) = (y IN t)))`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL_def,FUN_REL,SPECIFICATION]
   );

val SET_MAP_def =
    Define
      `SET_MAP (f:'a->'b) = (f --> (I:bool->bool))`;

val SET_MAP_COMPOSE = store_thm
   ("SET_MAP_COMPOSE",
    (--`!(f:'a->'b) s.
         SET_MAP f s = s o f`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_MAP_def,FUN_MAP_THM,I_THM,o_THM,
                     EXTENSION,SPECIFICATION]
   );

val IN_SET_MAP = store_thm
   ("IN_SET_MAP",
    (--`!(f:'a->'b) s x.
         x IN SET_MAP f s = f x IN s`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_MAP_COMPOSE,SPECIFICATION,o_THM]
   );

val SET_MAP_SET_MAP = store_thm
   ("SET_MAP_SET_MAP",
    (--`!(f:'a->'b) (g:'b->'c) s.
         SET_MAP f (SET_MAP g s) = SET_MAP (g o f) s`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_MAP_COMPOSE,o_ASSOC]
   );

val SET_QUOTIENT = store_thm
   ("SET_QUOTIENT",
    (--`!R (abs:'a->'c) rep. QUOTIENT R abs rep ==>
         QUOTIENT (SET_REL R) (SET_MAP rep) (SET_MAP abs)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[SET_REL_def,SET_MAP_def]
    THEN IMP_RES_THEN MATCH_MP_TAC FUN_QUOTIENT
    THEN REWRITE_TAC[IDENTITY_QUOTIENT]
   );


val SET_REL_MP = store_thm
   ("SET_REL_MP",
    (--`!(R:'a -> 'a -> bool) s t x y.
         (SET_REL R) s t ==> R x y ==> (x IN s = y IN t)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC SET_REL
   );


(* One possible development of SET_REL, based on set rep/abs by IMAGE:
Unfortunately this definition makes it impossible to prove the respectfulness
theorems for such operators as IN.

val SET_REL_def =
    Define
      `SET_REL (R:'a->'a->bool) s t =
                     (!x. x IN s ==> ?y. y IN t /\ R x y) /\
                     (!y. y IN t ==> ?x. x IN s /\ R x y)`;


val SET_EQUIV = store_thm
   ("SET_EQUIV",
    (--`!R :'a->'a->bool.
         (!x y. R x y = (R x = R y)) ==>
         (!x y. SET_REL R x y = (SET_REL R x = SET_REL R y))`--),
    GEN_TAC
    THEN REWRITE_TAC[EQUIV_REFL_SYM_TRANS]
    THEN STRIP_TAC
    THEN REWRITE_TAC[SET_REL_def,EXTENSION,IN_IMAGE]
    THEN REPEAT STRIP_TAC (* 6 subgoals *)
    THENL
      [ EXISTS_TAC ``x':'a``
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``y:'a``
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN EXISTS_TAC ``x'':'a``
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN EXISTS_TAC ``y'':'a``
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC ``y'':'a``
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC ``x''':'a``
        THEN ASM_REWRITE_TAC[]
      ]
    THEN PROVE_TAC[] (* could replace the THENL 6 cases above *)
   );


val SET_QUOTIENT = store_thm
   ("SET_QUOTIENT",
    (--`!R (abs:'a->'b) rep.
         (!a. abs (rep a) = a) /\
         (!r r'. R r r' = (abs r = abs r')) ==>
         (!a. IMAGE abs (IMAGE rep a) = a) /\
         (!r r'. SET_REL R r r' = (IMAGE abs r = IMAGE abs r'))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONJ_TAC
    THEN REWRITE_TAC[SET_REL_def,EXTENSION,IN_IMAGE]
    THEN PROVE_TAC[]
   );

*)



(* Here are some definitional and well-formedness theorems
   for some standard polymorphic operators.
*)


(* The most standard and common polymorphic operator of all
   is clearly simple equality (=).  Unfortunately, it does
   not lift unchanged.
*)

val EQUALS_PRS = store_thm
   ("EQUALS_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x y. (x = y) = R (rep x) (rep y)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_REL_REP
    THEN ASM_REWRITE_TAC[]
   );

val EQUALS_RSP = store_thm
   ("EQUALS_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x1 x2 y1 y2.
          R x1 x2 /\ R y1 y2 ==>
          (R x1 y1 = R x2 y2)`--),
    REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN IMP_RES_TAC QUOTIENT_SYM
    THEN IMP_RES_TAC QUOTIENT_TRANS
   );



(* Abstractions: LAMBDA, RES_ABSTRACT *)

              (* (\x. f x) = ^(\x. v(f ^x)) *)
val LAMBDA_PRS = store_thm
   ("LAMBDA_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. (\x. f x) = (rep1 --> abs2) (\x. rep2 (f (abs1 x)))`--),
    REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN BETA_TAC
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val LAMBDA_PRS1 = store_thm
   ("LAMBDA_PRS1",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. (\x. f x) = (rep1 --> abs2) (\x. (abs1 --> rep2) f x)`--),
    REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN BETA_TAC
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val LAMBDA_RSP = store_thm
   ("LAMBDA_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2.
          (R1 ===> R2) f1 f2 ==>
          (R1 ===> R2) (\x. f1 x) (\y. f2 y)`--),
    REWRITE_TAC[ETA_AX]
   );

val ABSTRACT_PRS = store_thm
   ("ABSTRACT_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. f = (rep1 --> abs2)
                      (RES_ABSTRACT (respects R1)
                                 ((abs1 --> rep2) f))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
    THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val RES_ABSTRACT_RSP = store_thm
   ("RES_ABSTRACT_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2.
          (R1 ===> R2) f1 f2 ==>
          (R1 ===> R2) (RES_ABSTRACT (respects R1) f1)
                       (RES_ABSTRACT (respects R1) f2)
       `--),
    ONCE_REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
    THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
    THEN POP_ASSUM REWRITE_THM
    THEN POP_ASSUM MP_TAC
    THEN IMP_RES_THEN (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th])))
                  QUOTIENT_REL
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val LET_RES_ABSTRACT = store_thm
   ("LET_RES_ABSTRACT",
    (--`!r (lam:'a->'b) v.
         v IN r ==> (LET (RES_ABSTRACT r lam) v = LET lam v)`--),
    REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[LET_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
   );



val LAMBDA_REP_ABS_RSP = store_thm
   ("LAMBDA_REP_ABS_RSP",
    (--`!REL1 (abs1:'a -> 'c) rep1 REL2 (abs2:'b -> 'd) rep2 f1 f2.
         ((!r r'. REL1 r r' ==> REL1 r (rep1 (abs1 r'))) /\
          (!r r'. REL2 r r' ==> REL2 r (rep2 (abs2 r')))) /\
          (REL1 ===> REL2) f1 f2 ==>
          (REL1 ===> REL2) f1 ((abs1 --> rep2) ((rep1 --> abs2) f2))`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[FUN_MAP]
    THEN BETA_TAC
    THEN BETA_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val REP_ABS_RSP = store_thm
   ("REP_ABS_RSP",
    (--`!REL (abs:'a -> 'b) rep. QUOTIENT REL abs rep ==>
         (!x1 x2.
           REL x1 x2 ==>
           REL x1 (rep (abs x2)))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN ASM_REWRITE_TAC[]
   );


(* ----------------------------------------------------- *)
(* Quantifiers: FORALL, EXISTS, EXISTS_UNIQUE,           *)
(*              RES_FORALL, RES_EXISTS, RES_EXISTS_EQUIV *)
(* ----------------------------------------------------- *)

val FORALL_PRS = store_thm
   ("FORALL_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !f. $! f = RES_FORALL (respects R) ((abs --> I) f)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[FORALL_DEF,RES_FORALL]
    THEN BETA_TAC
    THEN CONV_TAC (LAND_CONV FUN_EQ_CONV
                   THENC RAND_CONV FUN_EQ_CONV)
    THEN BETA_TAC
    THEN REWRITE_TAC[FUN_MAP_THM,I_THM]
    THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
    THEN EQ_TAC
    THENL
      [ DISCH_THEN REWRITE_THM,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC (--`(rep:'b->'a) x`--))
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
      ]
   );

val RES_FORALL_RSP = store_thm
   ("RES_FORALL_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !f g.
          (R ===> $=) f g ==>
          (RES_FORALL (respects R) f = RES_FORALL (respects R) g)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN REWRITE_TAC[RES_FORALL]
    THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
   );


val RES_FORALL_PRS = store_thm
   ("RES_FORALL_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !P f. RES_FORALL P f = RES_FORALL ((abs --> I) P) ((abs --> I) f)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[RES_FORALL]
    THEN REWRITE_TAC[SPECIFICATION,FUN_MAP_THM,I_THM]
    THEN EQ_TAC
    THENL
      [ DISCH_THEN REWRITE_THM,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC (--`(rep:'b->'a) x`--))
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
      ]
   );


val EXISTS_PRS = store_thm
   ("EXISTS_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !f. $? f = RES_EXISTS (respects R) ((abs --> I) f)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[boolTheory.EXISTS_DEF,RES_EXISTS]
    THEN BETA_TAC
    THEN REWRITE_TAC[FUN_MAP_THM,I_THM]
    THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN MATCH_MP_TAC (BETA_RULE
                    (SPEC ``\x:'a. R x x /\ f ((abs x):'b)`` SELECT_AX))
        THEN EXISTS_TAC (--`(rep:'b->'a) ($@ f)`--)
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
        THEN FIRST_ASSUM ACCEPT_TAC,

        STRIP_TAC
        THEN MATCH_MP_TAC SELECT_AX
        THEN EXISTS_TAC (--`(abs:'a->'b) (@x. R x x /\ f (abs x))`--)
        THEN FIRST_ASSUM ACCEPT_TAC
      ]
   );

val RES_EXISTS_RSP = store_thm
   ("RES_EXISTS_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !f g.
          (R ===> $=) f g ==>
          (RES_EXISTS (respects R) f = RES_EXISTS (respects R) g)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN REWRITE_TAC[RES_EXISTS]
    THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC ``x:'a``
    THEN ASM_REWRITE_TAC[]
   );


val RES_EXISTS_PRS = store_thm
   ("RES_EXISTS_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !P f. RES_EXISTS P f = RES_EXISTS ((abs --> I) P) ((abs --> I) f)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[RES_EXISTS]
    THEN REWRITE_TAC[SPECIFICATION,FUN_MAP_THM,I_THM]
    THEN EQ_TAC
    THENL
      [ STRIP_TAC
        THEN EXISTS_TAC (--`(rep:'b->'a) x`--)
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[],

        STRIP_TAC
        THEN EXISTS_TAC (--`(abs:'a->'b) x`--)
        THEN ASM_REWRITE_TAC[]
      ]
   );


val EXISTS_UNIQUE_PRS = store_thm
   ("EXISTS_UNIQUE_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !f. $?! f = RES_EXISTS_EQUIV R ((abs --> I) f)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC[boolTheory.EXISTS_UNIQUE_DEF,RES_EXISTS_EQUIV]
    THEN BETA_TAC
    THEN MK_COMB_TAC
    THENL
      [ AP_TERM_TAC
        THEN IMP_RES_TAC EXISTS_PRS
        THEN ASM_REWRITE_TAC[]
        THEN CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
        THEN REFL_TAC,

        REWRITE_TAC[FUN_MAP_THM,I_THM]
        THEN REWRITE_TAC[RES_FORALL]
        THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
        THEN BETA_TAC
        THEN EQ_TAC
        THENL
          [ REPEAT STRIP_TAC
            THEN IMP_RES_TAC QUOTIENT_REL_ABS_EQ
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN RES_TAC,

            REPEAT STRIP_TAC
            THEN FIRST_ASSUM (MP_TAC o SPEC (--`(rep:'b->'a) x`--))
            THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
            THEN DISCH_THEN (MP_TAC o SPEC (--`(rep:'b->'a) y`--))
            THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
            THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
            THEN DISCH_TAC
            THEN RES_TAC
            THEN POP_ASSUM MP_TAC
            THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
            THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
            THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
          ]
      ]
   );

val RES_EXISTS_EQUIV_RSP = store_thm
   ("RES_EXISTS_EQUIV_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !f g.
          (R ===> $=) f g ==>
          (RES_EXISTS_EQUIV R f =
           RES_EXISTS_EQUIV R g)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN REWRITE_TAC[RES_EXISTS_EQUIV]
    THEN MK_COMB_TAC
    THENL
      [ AP_TERM_TAC
        THEN REWRITE_TAC[ETA_AX]
        THEN IMP_RES_THEN (fn th => DEP_REWRITE_TAC[th]) RES_EXISTS_RSP
        THEN ASM_REWRITE_TAC[FUN_REL],

        REWRITE_TAC[RES_FORALL]
        THEN REWRITE_TAC[SPECIFICATION,respects_def,W_THM]
        THEN BETA_TAC
        THEN EQ_TAC
        THENL
          [ REPEAT STRIP_TAC
            THEN RES_TAC
            THEN RES_TAC,

            REPEAT STRIP_TAC
            THEN RES_TAC
            THEN RES_TAC
          ]
      ]
   );


(*
val RES_EXISTS_UNIQUE_PRS = store_thm
   ("RES_EXISTS_UNIQUE_PRS",
    (--`!REL (abs:'a -> 'b) rep.
         (!a. abs (rep a) = a) /\ (!r r'. REL r r' = (abs r = abs r'))
         ==>
         !P f. RES_EXISTS_UNIQUE P f =
               RES_EXISTS_EQUIV ((abs --> I) P) REL ((abs --> I) f)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[RES_EXISTS_UNIQUE_DEF,RES_EXISTS_EQUIV]
    THEN BETA_TAC
    THEN MK_COMB_TAC
    THENL
      [ AP_TERM_TAC
        THEN IMP_RES_TAC RES_EXISTS_PRS
        THEN ASM_REWRITE_TAC[FUN_MAP,I_THM,ETA_AX],

        CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
        THEN REWRITE_TAC[SPECIFICATION,FUN_MAP_THM,I_THM]
        THEN EQ_TAC
        THENL
          [ REPEAT STRIP_TAC
            THEN RES_TAC
            THEN RES_TAC,

            CONV_TAC (LAND_CONV (DEPTH_CONV RIGHT_IMP_FORALL_CONV))
            THEN REWRITE_TAC[AND_IMP_INTRO]
            THEN REPEAT STRIP_TAC
            THEN FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (--`x:'b`--))
            THEN FIRST_ASSUM (SUBST1_TAC o SYM o SPEC (--`y:'b`--))
            THEN FIRST_ASSUM (REWRITE_THM o SYM o SPEC_ALL)
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );

*)

(* I don't think the select operator is respectful of equivalence.
RES_SELECT is not defined in all cases,
and even in those its value may not be well-behaved.

val RES_SELECT_FUN_PRS = store_thm
   ("RES_SELECT_FUN_PRS",
    (--`!REL1 (abs1:'a -> 'c) rep1 REL2 (abs2:'b -> 'd) rep2.
         (!a. abs1 (rep1 a) = a) /\ (!r r'. REL1 r r' = (abs1 r = abs1 r'))
         ==>
         (!a. abs2 (rep2 a) = a) /\ (!r r'. REL2 r r' = (abs2 r = abs2 r'))
         ==>
         !f. $@ f = (rep1 --> abs2)
                        (RES_SELECT (respects(REL1,REL2))
                                 (((rep1 --> abs2) --> I) f))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN REWRITE_TAC[res_quanTheory.RES_SELECT]
    THEN REWRITE_TAC[SPECIFICATION,respects_def]
    THEN BETA_TAC
    THEN ASM_REWRITE_TAC[FUN_MAP_THM,I_THM]
    THEN CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN DEP_REWRITE_TAC[FUN_REL_ABS_REP]
    THEN ASM_REWRITE_TAC[]
    THEN PROVE_TAC[]
   );

val RES_SELECT_FUN_RSP = store_thm
   ("RES_SELECT_FUN_RSP",
    (--`!REL1 (abs1:'a -> 'd) rep1 REL2 (abs2:'b -> 'e) rep2
         REL3 (abs3:'c -> 'f) rep3.
         (!a. abs1 (rep1 a) = a) /\ (!r r'. REL1 r r' = (abs1 r = abs1 r'))
         ==>
         (!a. abs2 (rep2 a) = a) /\ (!r r'. REL2 r r' = (abs2 r = abs2 r'))
         ==>
         (!a. abs3 (rep3 a) = a) /\ (!r r'. REL3 r r' = (abs3 r = abs3 r'))
         ==>
         !f1 f2.
          ((REL1 ===> REL2) ===> REL3) f1 f2 ==>
          ((REL1 ===> REL2) ===> REL3) (RES_SELECT (respects(REL1,REL2)) f1)
                                       (RES_SELECT (respects(REL1,REL2)) f2)
       `--),
    REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_SELECT]
    THEN REWRITE_TAC[SPECIFICATION,respects_def]
    THEN BETA_TAC
    THEN POP_ASSUM REWRITE_THM
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN PROVE_TAC[]
   );

*)


(* bool theory: COND, LET *)

val COND_PRS = store_thm
   ("COND_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !a b c. COND a b c = abs (COND a (rep b) (rep c))`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[GSYM COND_RAND]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val COND_RSP = store_thm
   ("COND_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !a1 a2 b1 b2 c1 c2.
          (a1 = a2) /\ R b1 b2 /\ R c1 c2
           ==> R (COND a1 b1 c1) (COND a2 b2 c2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]
   );


val LET_PRS = store_thm
   ("LET_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f x. LET f x = abs2 (LET ((abs1-->rep2) f) (rep1 x))`--),
    REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[LET_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[FUN_MAP]
    THEN BETA_TAC
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val LET_RSP = store_thm
   ("LET_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f g x y.
          (R1 ===> R2) f g /\ R1 x y ==>
          R2 (LET f x) (LET g y)`--),
    REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[LET_DEF]
    THEN BETA_TAC
    THEN IMP_RES_TAC FUN_REL_MP
   );



(* FUNCTION APPLICATION *)

val APPLY_PRS = store_thm
   ("APPLY_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f x. f x = abs2 (((abs1-->rep2) f) (rep1 x))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val APPLY_RSP = store_thm
   ("APPLY_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f g x y.
          (R1 ===> R2) f g /\ R1 x y ==>
          R2 (f x) (g y)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC FUN_REL_MP
   );


(* combin theory: I, K, o, C, W *)


val I_PRS = store_thm
   ("I_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !e. I e = abs (I (rep e))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[I_THM]
   );

val I_RSP = store_thm
   ("I_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !e1 e2.
          R e1 e2 ==>
          R (I e1) (I e2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[I_THM]
   );

val K_PRS = store_thm
   ("K_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !x y. K x y = abs1 (K (rep1 x) (rep2 y))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[K_THM]
   );

val K_RSP = store_thm
   ("K_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !x1 x2 y1 y2.
          R1 x1 x2 /\ R2 y1 y2 ==>
          R1 (K x1 y1) (K x2 y2)`--),
    REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[K_THM]
   );

val o_PRS = store_thm
   ("o_PRS",
    (--`!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f g. f o g =
               (rep1-->abs3) ( ((abs2-->rep3) f) o ((abs1-->rep2) g) )`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[o_THM]
    THEN REWRITE_TAC[FUN_MAP_THM,o_THM]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val o_RSP = store_thm
   ("o_RSP",
    (--`!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f1 f2 g1 g2.
          (R2 ===> R3) f1 f2 /\ (R1 ===> R2) g1 g2 ==>
          (R1 ===> R3) (f1 o g1) (f2 o g2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[o_THM]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val C_PRS = store_thm
   ("C_PRS",
    (--`!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f x y. combin$C f x y =
                 abs3 (combin$C ((abs1-->abs2-->rep3) f) (rep2 x) (rep1 y))
       `--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[C_THM]
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val C_RSP = store_thm
   ("C_RSP",
    (--`!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f1 f2 x1 x2 y1 y2.
          (R1 ===> R2 ===> R3) f1 f2 /\ R2 x1 x2 /\ R1 y1 y2 ==>
          R3 (combin$C f1 x1 y1) (combin$C f2 x2 y2)`--),
    REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[C_THM]
    THEN RES_TAC
   );

val W_PRS = store_thm
   ("W_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f x. W f x = abs2 (W ((abs1-->abs1-->rep2) f) (rep1 x))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[W_THM]
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val W_RSP = store_thm
   ("W_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2 x1 x2.
          (R1 ===> R1 ===> R2) f1 f2 /\ R1 x1 x2 ==>
          R2 (W f1 x1) (W f2 x2)`--),
    REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[W_THM]
    THEN RES_TAC
   );



(* pred_set theory: IN, EMPTY, UNIV, INTER, UNION, SUBSET, PSUBSET, IMAGE *)

val IN_PRS = store_thm
   ("IN_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x s. x IN s =
               rep x IN SET_MAP abs s`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[IN_SET_MAP]
   );

val IN_RSP = store_thm
   ("IN_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x1 x2 s1 s2.
          R x1 x2 /\ (SET_REL R) s1 s2 ==>
          (x1 IN s1 = x2 IN s2)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC SET_REL_MP
   );


(* GSPEC does not lift directly; because its definition

GSPECIFICATION   |- !f v. v IN GSPEC f = ?x. (v,T) = f x : thm

involves = between v:'b and FST(f x):'b, rather than R2 v (FST(f x)),
it does not respect the equivalence relation on 'b.
But a similar operator exists which we can try to lift to GSPEC.

val GSPEC_PRS = store_thm
   ("GSPEC_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. GSPEC f =
               SET_MAP rep2 (GSPEC ((abs1 --> (rep2 ## I)) f))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[GSPECIFICATION,IN_SET_MAP]
    THEN REWRITE_TAC[FUN_MAP_THM,PAIR_MAP]
    THEN REWRITE_TAC[PAIR_EQ,I_THM]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC ``rep1 (x':'c) :'a``
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM),

        EXISTS_TAC ``abs1 (x':'a) :'c``
        THEN CONV_TAC (RAND_CONV (REWR_CONV (GSYM PAIR)))
        THEN REWRITE_TAC[PAIR_EQ]
        THEN POP_ASSUM REWRITE_THM
        THEN POP_ASSUM (MP_TAC o AP_TERM ``abs2:'b->'d``)
        THEN ASM_REWRITE_TAC[]
      ]
   );

val GSPECR_def =
    Define
      `GSPECR R (f:'a -> ('b # bool)) (v:'b) =
                     ?x. (R ### $=) (v,T) (f x)`;


val GSPECIFICATION_R = store_thm
   ("GSPECIFICATION_R",
    (--`!R f v:'b. v IN GSPECR R f = ?x:'a. (R ### $=) (v,T) (f x)`--),
    REWRITE_TAC[GSPECR_def,SPECIFICATION]
   );

val GSPECR_PRS = store_thm
   ("GSPECR_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. GSPEC f =
               SET_MAP rep2 (GSPECR R2 ((abs1 --> (rep2 ## I)) f))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[GSPECIFICATION,GSPECIFICATION_R,IN_SET_MAP]
    THEN REWRITE_TAC[FUN_MAP_THM,I_THM,PAIR_MAP]
    THEN REWRITE_TAC[PAIR_REL_THM,PAIR_EQ]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC ``rep1 (x':'c) :'a``
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM)
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``abs1 (x':'a) :'c``
        THEN CONV_TAC (RAND_CONV (REWR_CONV (GSYM PAIR)))
        THEN REWRITE_TAC[PAIR_EQ]
        THEN POP_ASSUM REWRITE_THM
        THEN POP_ASSUM MP_TAC
        THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
        THEN ASM_REWRITE_TAC[]
      ]
   );

This proof fails for the new quotient relations; not reflexive!
val GSPECR_RSP = store_thm
   ("GSPECR_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2.
          (R1 ===> (R2 ### $=)) f1 f2 ==>
          SET_REL R2 (GSPECR R2 f1) (GSPECR R2 f2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN DISCH_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN X_GEN_TAC ``z:'b``
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[GSPECIFICATION_R]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM,PAIR_EQ]
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN EXISTS_TAC ``(rep1:'c->'a) ((abs1:'a->'c) x)``
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN FIRST_ASSUM (ASSUME_TAC o SPEC ``(abs1:'a->'c) x``)
    THEN RES_TAC
    THEN POP_TAC
    THEN POP_TAC
    THEN POP_ASSUM (REWRITE_THM o SYM)
    THEN IMP_RES_TAC QUOTIENT_SYM
    THEN IMP_RES_TAC QUOTIENT_TRANS
   );

Can't prove this, so can't lift GSPEC.

val GSPEC_RSP = store_thm
   ("GSPEC_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1 R2 (abs2:'b -> 'd) rep2.
         (!a. abs1 (rep1 a) = a) /\ (!r r'. R1 r r' = (abs1 r = abs1 r'))
         ==>
         (!a. abs2 (rep2 a) = a) /\ (!r r'. R2 r r' = (abs2 r = abs2 r'))
         ==>
         !f1 f2.
          (R1 ===> (R2 ### $=)) f1 f2 ==>
          SET_REL R2 (GSPEC f1) (GSPEC f2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN DISCH_TAC
    THEN REWRITE_TAC[SET_REL_EQ]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[GSPECIFICATION]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_EQ]
    THEN ???
   );

No, the GSPEC / GSPECR experiment has not succeeded.
*)


val EMPTY_PRS = store_thm
   ("EMPTY_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (EMPTY = SET_MAP abs EMPTY)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[NOT_IN_EMPTY,IN_SET_MAP]
   );

val EMPTY_RSP = store_thm
   ("EMPTY_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         SET_REL R EMPTY EMPTY`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[NOT_IN_EMPTY]
   );

val UNIV_PRS = store_thm
   ("UNIV_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (UNIV = SET_MAP abs UNIV)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_SET_MAP,IN_UNIV]
   );

val UNIV_RSP = store_thm
   ("UNIV_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         SET_REL R UNIV UNIV`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[IN_UNIV]
   );


val UNION_PRS = store_thm
   ("UNION_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s UNION t =
               SET_MAP rep (SET_MAP abs s UNION SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN PURE_REWRITE_TAC[IN_SET_MAP,IN_UNION]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val UNION_RSP = store_thm
   ("UNION_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          SET_REL R (s1 UNION t1) (s2 UNION t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[IN_UNION]
    THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] SET_REL_MP)
    THEN ASM_REWRITE_TAC[]
   );


val INTER_PRS = store_thm
   ("INTER_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s INTER t =
               SET_MAP rep (SET_MAP abs s INTER SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN PURE_REWRITE_TAC[IN_SET_MAP,IN_INTER]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val INTER_RSP = store_thm
   ("INTER_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          SET_REL R (s1 INTER t1) (s2 INTER t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[IN_INTER]
    THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] SET_REL_MP)
    THEN ASM_REWRITE_TAC[]
   );

(*
val EQ_EMPTY_PRS = store_thm
   ("EQ_EMPTY_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s.
             (s = {}) = (SET_MAP abs s = {})`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY]
    THEN REWRITE_TAC[IN_SET_MAP]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[]
      ]
   );

val EQ_EMPTY_RSP = store_thm
   ("EQ_EMPTY_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2. SET_REL R s1 s2 ==>
             ((s1 = {}) = (s2 = {}))`--),
    REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[]
      ]
   );
*)

(* DISJOINT does not lift.

val DISJOINTR_def =
    Define
      `DISJOINTR R (s:'a -> bool) t = SET_REL R (s INTER t) {}`;

NO.
val SET_REL_EXTENSION = store_thm
   ("SET_REL_EXTENSION",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. SET_REL R s t = (!x :: respects R. x IN s = x IN t)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN REPEAT GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[]
      ]
   );

val DISJOINT_PRS = store_thm
   ("DISJOINT_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t.
             DISJOINT s t = DISJOINTR R (SET_MAP abs s) (SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[DISJOINT_DEF,DISJOINTR_def]
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY,IN_INTER]
    THEN REWRITE_TAC[SET_REL_EXTENSION,NOT_IN_EMPTY,IN_INTER]
    THEN REWRITE_TAC[IN_SET_MAP]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[]
      ]
   );

val DISJOINT_RSP = store_thm
   ("DISJOINT_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          (DISJOINT s1 t1 = DISJOINT s2 t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[DISJOINT_DEF]
    THEN AP_THM_TAC
    THEN AP_TERM_TAC
    THEN MP_TAC (SPEC_ALL INTER_RSP)
    THEN ASM_REWRITE_TAC[]
    THEN 
    THEN 
    THEN 
    THEN IMP_RES_THEN MATCH_MP_TAC INTER_RSP
    THEN 
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY,IN_INTER]
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN POP_ASSUM (MP_TAC o SPEC ``x:'a``)
    THEN IMP_RES_TAC QUOTIENT_REFL
    THEN POP_ASSUM (ASSUME_TAC o SPEC ``x:'a``)
    THEN IMP_RES_TAC SET_REL_MP
    THEN ASM_REWRITE_TAC[]
   );
*)



val SUBSETR_def =
    Define
      `SUBSETR P s t = !x:'a::P. x IN s ==> x IN t`;

val SUBSET_PRS = store_thm
   ("SUBSET_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s SUBSET t =
               SUBSETR (respects R) (SET_MAP abs s) (SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SUBSET_DEF,SUBSETR_def]
    THEN PURE_REWRITE_TAC[IN_SET_MAP]
    THEN CONV_TAC (RAND_CONV RES_FORALL_CONV)
    THEN PURE_REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THENL
      [ DISCH_TAC
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC,

        POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN IMP_RES_TAC QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[]
      ]
   );

val SUBSETR_RSP = store_thm
   ("SUBSETR_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          (SUBSETR (respects R) s1 t1 = SUBSETR (respects R) s2 t2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN STRIP_TAC
    THEN PURE_REWRITE_TAC[SUBSETR_def]
    THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
    THEN PURE_REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN RES_TAC
   );


val PSUBSETR_def =
    Define
      `PSUBSETR R (s:'a->bool) t =
       SUBSETR (respects R) s t /\ ~(SET_REL R s t)`;

val PSUBSET_PRS = store_thm
   ("PSUBSET_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s PSUBSET t = PSUBSETR R (SET_MAP abs s) (SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[PSUBSET_DEF,PSUBSETR_def]
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN PURE_ONCE_REWRITE_TAC[SET_REL]
    THEN PURE_REWRITE_TAC[IN_SET_MAP]
    THEN IMP_RES_THEN REWRITE_THM SUBSET_PRS
    THEN AP_TERM_TAC
    THEN AP_TERM_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC QUOTIENT_REL_ABS
        THEN ASM_REWRITE_TAC[],

        IMP_RES_THEN (ASSUME_TAC o SPEC ``x:'b``) QUOTIENT_REP_REFL
        THEN RES_THEN MP_TAC
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
      ]
   );

val PSUBSETR_RSP = store_thm
   ("PSUBSETR_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          (PSUBSETR R s1 t1 = PSUBSETR R s2 t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[PSUBSETR_def]
    THEN MP_TAC (SPEC_ALL SUBSETR_RSP)
    THEN ASM_REWRITE_TAC[]
    THEN DISCH_THEN (MP_TAC o SPEC_ALL)
    THEN ASM_REWRITE_TAC[]
    THEN DISCH_THEN REWRITE_THM
    THEN AP_TERM_TAC
    THEN AP_TERM_TAC
    THEN IMP_RES_TAC SET_QUOTIENT
    THEN POP_ASSUM (MATCH_MP_TAC o (MATCH_MP EQUALS_RSP))
    THEN ASM_REWRITE_TAC[]
   );


(* IMAGER (rep1,abs2) f s =
   SET_MAP abs2 (IMAGE ((rep1 --> abs2) f) (SET_MAP rep1 s))

   SET_MAP abs2 {(rep1 --> abs2) f x | x IN SET_MAP rep1 s}

   SET_MAP abs2 {(rep1 --> abs2) f x | rep1 x IN s}

   SET_MAP abs2 {abs2 (f (rep1 x)) | rep1 x IN s}

   SET_MAP abs2 {abs2 (f z) | R1 z z /\ z IN s}

   SET_MAP abs2 {abs2 (f z) | R1 z z /\ z IN s}

   {y | ?x. abs2 y = abs2 (f x) /\ R1 x x /\ x IN s}

   {y | ?x. R2 y (f x) /\ R1 x x /\ x IN s}

?  {y | ?x. R2 y (f (rep1 x)) /\ rep1 x IN s}

?  {y | ?x x'. R2 y (f x) /\ R1 x x' /\ x' IN s}

  *)

(*
val IMAGER_def =
    Define
      `IMAGER R1 R2 (f:'a->'b) s =
       {y:'b | ?x :: respects R1. R2 y (f x) /\ x IN s}`;
*)

val IMAGER_def =
    Define
      `IMAGER R1 R2 (f:'a->'b) s =
       {y:'b | ?x :: respects R1. R2 y (f x) /\ x IN s}`;

val IN_IMAGER = store_thm
   ("IN_IMAGER",
    (--`!R1 R2 y (f:'a -> 'b) s.
          y IN IMAGER R1 R2 f s =
                 ?x :: respects R1. R2 y (f x) /\ x IN s`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[IMAGER_def]
    THEN CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV)
    THEN REWRITE_TAC[]
   );

val IMAGE_PRS = store_thm
   ("IMAGE_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f s. IMAGE f s =
               SET_MAP rep2 (IMAGER R1 R2 ((abs1-->rep2) f) (SET_MAP abs1 s))
       `--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN PURE_REWRITE_TAC[IN_SET_MAP,IN_IMAGE,IN_IMAGER]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV)
    THEN REWRITE_TAC[IN_RESPECTS,FUN_MAP_THM]
    THEN EQ_TAC
    THENL
       [ STRIP_TAC
         THEN EXISTS_TAC (--`(rep1:'c->'a) x'`--)
         THEN IMP_RES_TAC QUOTIENT_REP_REFL
         THEN ASM_REWRITE_TAC[],

         STRIP_TAC
         THEN EXISTS_TAC (--`(abs1:'a->'c) x'`--)
         THEN POP_ASSUM (fn th => REWRITE_TAC[th])
         THEN IMP_RES_TAC QUOTIENT_REL_ABS
         THEN POP_TAC
         THEN POP_ASSUM MP_TAC
         THEN ASM_REWRITE_TAC[]
       ]
   );

val IMAGER_RSP = store_thm
   ("IMAGER_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2 s1 s2.
          (R1 ===> R2) f1 f2 /\ SET_REL R1 s1 s2 ==>
          SET_REL R2 (IMAGER R1 R2 f1 s1) (IMAGER R1 R2 f2 s2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_IMAGER]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN EXISTS_TAC (--`x':'a`--)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC QUOTIENT_SYM
    THEN IMP_RES_TAC QUOTIENT_TRANS
   );

(*
val IMAGE_RSP = store_thm
   ("IMAGE_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2 s1 s2.
          (R1 ===> R2) f1 f2 /\ SET_REL R1 s1 s2 ==>
          SET_REL R2 (IMAGE f1 s1) (IMAGE f2 s2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL,SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_IMAGE]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
       [ EXISTS_TAC (--`x':'a`--)
         THEN CONJ_TAC
         THENL
           [ ASM_REWRITE_TAC[]
             THEN FIRST_ASSUM MATCH_MP_TAC
             THEN ASM_REWRITE_TAC[],

             POP_ASSUM MP_TAC
             THEN ASM_REWRITE_TAC[]
           ],

         EXISTS_TAC (--`x':'a`--)
         THEN CONJ_TAC
         THENL
           [ ASM_REWRITE_TAC[]
             THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
             THEN FIRST_ASSUM MATCH_MP_TAC
             THEN ASM_REWRITE_TAC[],

             POP_ASSUM MP_TAC
             THEN ASM_REWRITE_TAC[]
           ]
       ]
   );
*)




(* ----------------------------------------- *)
(* theorems for regularized version of goals *)
(* ----------------------------------------- *)


val EQ_IMPLIES = store_thm
   ("EQ_IMPLIES",
    (--`!P Q.
          (P = Q) ==>
          (P ==> Q)`--),
    REPEAT GEN_TAC
    THEN DISCH_THEN REWRITE_THM
   );

val EQUALS_IMPLIES = store_thm
   ("EQUALS_IMPLIES",
    (--`!P P' Q Q':'a.
          (P = Q) /\ (P' = Q') ==>
          ((P = P') ==> (Q = Q'))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val CONJ_IMPLIES = store_thm
   ("CONJ_IMPLIES",
    (--`!P P' Q Q'.
          (P ==> Q) /\ (P' ==> Q') ==>
          (P /\ P' ==> Q /\ Q')`--),
    REPEAT STRIP_TAC
    THEN RES_TAC
   );

val DISJ_IMPLIES = store_thm
   ("DISJ_IMPLIES",
    (--`!P P' Q Q'.
          (P ==> Q) /\ (P' ==> Q') ==>
          (P \/ P' ==> Q \/ Q')`--),
    REPEAT STRIP_TAC
    THENL [ DISJ1_TAC, DISJ2_TAC ]
    THEN RES_TAC
   );

val IMP_IMPLIES = store_thm
   ("IMP_IMPLIES",
    (--`!P P' Q Q'.
          (Q ==> P) /\ (P' ==> Q') ==>
          ((P ==> P') ==> (Q ==> Q'))`--),
    REPEAT STRIP_TAC
    THEN RES_TAC
    THEN RES_TAC
    THEN RES_TAC
   );

val NOT_IMPLIES = store_thm
   ("NOT_IMPLIES",
    (--`!P Q.
          (Q ==> P) ==>
          (~P ==> ~Q)`--),
    REPEAT STRIP_TAC
    THEN RES_TAC
    THEN RES_TAC
   );

val EQUALS_EQUIV_IMPLIES = store_thm
   ("EQUALS_EQUIV_IMPLIES",
    (--`!R:'a -> 'a -> bool.
          (!x y. R x y = (R x = R y)) ==>
          R a1 a2 /\ R b1 b2 ==>
          ((a1 = b1) ==> R a2 b2)`--),
    REPEAT STRIP_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN IMP_RES_TAC EQUIV_REFL_SYM_TRANS
   );

(*
val EQUALS_EQUIV_IMPLIES1 = store_thm
   ("EQUALS_EQUIV_IMPLIES1",
    (--`!R:'a -> 'a -> bool.
          (!x y. R x y = (R x = R y)) ==>
          (R a1 b1 ==> R a2 b2) ==>
          ((a1 = b1) ==> R a2 b2)`--),
    REPEAT STRIP_TAC
    THEN POP_ASSUM REWRITE_ALL_THM
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );
*)

val ABSTRACT_RES_ABSTRACT = store_thm
   ("ABSTRACT_RES_ABSTRACT",
    (--`!(R1:'a -> 'a -> bool) (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !(R2:'b -> 'b -> bool) f g.
          (R1 ===> R2) f g ==>
          (R1 ===> R2) f (RES_ABSTRACT (respects R1) g)`--),
    REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
    THEN RES_THEN REWRITE_THM
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
    THEN POP_ASSUM MP_TAC
    THEN IMP_RES_THEN (CONV_TAC o LAND_CONV o REWR_CONV) QUOTIENT_REL
    THEN STRIP_TAC
   );

val RES_ABSTRACT_ABSTRACT = store_thm
   ("RES_ABSTRACT_ABSTRACT",
    (--`!(R1:'a -> 'a -> bool) (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !(R2:'b -> 'b -> bool) f g.
          (R1 ===> R2) f g ==>
          (R1 ===> R2) (RES_ABSTRACT (respects R1) f) g`--),
    REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
    THEN RES_THEN REWRITE_THM
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
    THEN POP_ASSUM MP_TAC
    THEN IMP_RES_THEN (CONV_TAC o LAND_CONV o REWR_CONV) QUOTIENT_REL
    THEN STRIP_TAC
   );

val EQUIV_RES_ABSTRACT_LEFT = store_thm
   ("EQUIV_RES_ABSTRACT_LEFT",
    (--`!R1 R2 (f1:'a -> 'b) (f2:'a -> 'b) x1 x2.
          R2 (f1 x1) (f2 x2) /\ R1 x1 x1 ==>
          R2 (RES_ABSTRACT (respects R1) f1 x1) (f2 x2)`--),
    REPEAT STRIP_TAC
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
    THEN ASM_REWRITE_TAC[]
   );

val EQUIV_RES_ABSTRACT_RIGHT = store_thm
   ("EQUIV_RES_ABSTRACT_RIGHT",
    (--`!R1 R2 (f1:'a -> 'b) (f2:'a -> 'b) x1 x2.
          R2 (f1 x1) (f2 x2) /\ R1 x2 x2 ==>
          R2 (f1 x1) (RES_ABSTRACT (respects R1) f2 x2)`--),
    REPEAT STRIP_TAC
    THEN DEP_REWRITE_TAC[res_quanTheory.RES_ABSTRACT]
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
    THEN ASM_REWRITE_TAC[]
   );

val EQUIV_RES_FORALL = store_thm
   ("EQUIV_RES_FORALL",
    (--`!E (P:'a -> bool).
          (!x y. E x y = (E x = E y)) ==>
          (RES_FORALL (respects E) P = ($! P))`--),
    REPEAT STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN CONV_TAC (LAND_CONV res_quanLib.RES_FORALL_CONV)
    THEN ASM_REWRITE_TAC[SPECIFICATION,RESPECTS]
   );

val EQUIV_RES_EXISTS = store_thm
   ("EQUIV_RES_EXISTS",
    (--`!E (P:'a -> bool).
          (!x y. E x y = (E x = E y)) ==>
          (RES_EXISTS (respects E) P = ($? P))`--),
    REPEAT STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN CONV_TAC (LAND_CONV res_quanLib.RES_EXISTS_CONV)
    THEN ASM_REWRITE_TAC[SPECIFICATION,RESPECTS]
   );

val EQUIV_RES_EXISTS_UNIQUE = store_thm
   ("EQUIV_RES_EXISTS_UNIQUE",
    (--`!E (P:'a -> bool).
          (!x y. E x y = (E x = E y)) ==>
          (RES_EXISTS_UNIQUE (respects E) P = ($?! P))`--),
    REPEAT STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX))))
    THEN CONV_TAC (LAND_CONV res_quanLib.RES_EXISTS_UNIQUE_CONV)
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_FORALL_CONV)
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_CONV)
    THEN ASM_REWRITE_TAC[EXISTS_UNIQUE_THM,SPECIFICATION,RESPECTS]
   );

val FORALL_REGULAR = store_thm
   ("FORALL_REGULAR",
    (--`!P Q.
          (!x:'a. P x ==> Q x) ==>
          ($! P ==> $! Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (ASSUME_TAC o SPEC_ALL)
    THEN RES_TAC
   );

val EXISTS_REGULAR = store_thm
   ("EXISTS_REGULAR",
    (--`!P Q.
          (!x:'a. P x ==> Q x) ==>
          ($? P ==> $? Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC (--`x:'a`--)
    THEN POP_ASSUM ACCEPT_TAC
   );

val RES_FORALL_REGULAR = store_thm
   ("RES_FORALL_REGULAR",
    (--`!P Q R.
          (!x:'a. R x ==> P x ==> Q x) ==>
          (RES_FORALL R P ==> RES_FORALL R Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_FORALL_CONV)
    THEN REWRITE_TAC[SPECIFICATION]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
   );

val RES_EXISTS_REGULAR = store_thm
   ("RES_EXISTS_REGULAR",
    (--`!P Q R.
          (!x:'a. R x ==> P x ==> Q x) ==>
          (RES_EXISTS R P ==> RES_EXISTS R Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_CONV)
    THEN REWRITE_TAC[SPECIFICATION]
    THEN STRIP_TAC
    THEN RES_TAC
    THEN EXISTS_TAC (--`x:'a`--)
    THEN ASM_REWRITE_TAC[]
   );

val LEFT_RES_FORALL_REGULAR = store_thm
   ("LEFT_RES_FORALL_REGULAR",
    (--`!P R Q.
          (!x:'a. R x /\ (Q x ==> P x)) ==>
          (RES_FORALL R Q ==> $! P)`--),
    REPEAT GEN_TAC
    THEN CONV_TAC (LAND_CONV FORALL_AND_CONV)
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (LAND_CONV res_quanLib.RES_FORALL_CONV)
    THEN REWRITE_TAC[SPECIFICATION]
    THEN STRIP_TAC
    THEN GEN_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val RIGHT_RES_FORALL_REGULAR = store_thm
   ("RIGHT_RES_FORALL_REGULAR",
    (--`!P R Q.
          (!x:'a. R x ==> P x ==> Q x) ==>
          ($! P ==> RES_FORALL R Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN STRIP_TAC
    THEN CONV_TAC res_quanLib.RES_FORALL_CONV
    THEN REWRITE_TAC[SPECIFICATION]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val LEFT_RES_EXISTS_REGULAR = store_thm
   ("LEFT_RES_EXISTS_REGULAR",
    (--`!P R Q.
          (!x:'a. R x ==> Q x ==> P x) ==>
          (RES_EXISTS R Q ==> $? P)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (LAND_CONV res_quanLib.RES_EXISTS_CONV)
    THEN REWRITE_TAC[SPECIFICATION]
    THEN STRIP_TAC
    THEN EXISTS_TAC (--`x:'a`--)
    THEN RES_TAC
   );

val RIGHT_RES_EXISTS_REGULAR = store_thm
   ("RIGHT_RES_EXISTS_REGULAR",
    (--`!P R Q.
          (!x:'a. R x /\ (P x ==> Q x)) ==>
          ($? P ==> RES_EXISTS R Q)`--),
    REPEAT GEN_TAC
    THEN DISCH_THEN (STRIP_ASSUME_TAC o CONV_RULE FORALL_AND_CONV)
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN STRIP_TAC
    THEN CONV_TAC res_quanLib.RES_EXISTS_CONV
    THEN REWRITE_TAC[SPECIFICATION]
    THEN RES_TAC
    THEN EXISTS_TAC (--`x:'a`--)
    THEN ASM_REWRITE_TAC[]
   );

val EXISTS_UNIQUE_REGULAR = store_thm
   ("EXISTS_UNIQUE_REGULAR",
    (--`!P E Q.
          (!x:'a. P x ==> respects E x /\ Q x) /\
          (!x y. respects E x /\ Q x /\ respects E y /\ Q y ==> E x y) ==>
          ($?! P ==> RES_EXISTS_EQUIV E Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (LAND_CONV EXISTS_UNIQUE_CONV)
    THEN REWRITE_TAC[RES_EXISTS_EQUIV]
    THEN BETA_TAC
    THEN CONV_TAC (RAND_CONV (DEPTH_CONV res_quanLib.RES_EXISTS_CONV))
    THEN CONV_TAC (RAND_CONV (DEPTH_CONV res_quanLib.RES_FORALL_CONV))
    THEN REWRITE_TAC[SPECIFICATION]
    THEN PROVE_TAC[]
   );

(*
val RES_EXISTS_UNIQUE_RESPECTS_REGULAR = store_thm
   ("RES_EXISTS_UNIQUE_RESPECTS_REGULAR",
    (--`!R (P:'a -> bool).
          (RES_EXISTS_UNIQUE (respects R) P ==>
           RES_EXISTS_EQUIV (respects R) R P)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC RES_EXISTS_UNIQUE_EQUIV_REL
    THEN POP_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
   );
*)

val RES_EXISTS_UNIQUE_RESPECTS_REGULAR = store_thm
   ("RES_EXISTS_UNIQUE_RESPECTS_REGULAR",
    (--`!R (P:'a -> bool).
         RES_EXISTS_UNIQUE (respects R) P ==>
         RES_EXISTS_EQUIV R P`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[res_quanTheory.RES_EXISTS_UNIQUE,RES_EXISTS_EQUIV]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN REPEAT res_quanLib.RESQ_GEN_TAC
    THEN STRIP_TAC
    THEN res_quanLib.RESQ_RES_TAC
    THEN RES_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC[GSYM IN_RESPECTS]
   );

val RES_EXISTS_UNIQUE_REGULAR = store_thm
   ("RES_EXISTS_UNIQUE_REGULAR",
    (--`!P R E Q.
          (!x:'a. P x ==> Q x) /\
          (!x y. respects R x /\ Q x /\ respects R y /\ Q y ==> R x y) ==>
          (RES_EXISTS_UNIQUE (respects R) P ==> RES_EXISTS_EQUIV R Q)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])))
    THEN CONV_TAC (LAND_CONV res_quanLib.RES_EXISTS_UNIQUE_CONV)
    THEN REWRITE_TAC[RES_EXISTS_EQUIV]
    THEN BETA_TAC
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_CONV)
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_FORALL_CONV)
    THEN REWRITE_TAC[SPECIFICATION]
    THEN PROVE_TAC[]
   );

val RES_EXISTS_UNIQUE_REGULAR_SAME = store_thm
   ("RES_EXISTS_UNIQUE_REGULAR_SAME",
    (--`!R (P:'a -> bool) Q.
          (R ===> $=) P Q ==>
          (RES_EXISTS_UNIQUE (respects R) P ==>
           RES_EXISTS_EQUIV R Q)`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN REWRITE_TAC[res_quanTheory.RES_EXISTS_UNIQUE,RES_EXISTS_EQUIV]
    THEN MATCH_MP_TAC CONJ_IMPLIES
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_EXISTS_CONV)
    THEN CONV_TAC (DEPTH_CONV res_quanLib.RES_FORALL_CONV)
    THEN REWRITE_TAC[SPECIFICATION,RESPECTS]
    THEN CONJ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC (--`x:'a`--)
        THEN ASM_REWRITE_TAC[]
        THEN RES_TAC,

        POP_ASSUM (fn th => GEN_TAC THEN DISCH_TAC
                            THEN FIRST_ASSUM (MP_TAC o MATCH_MP th))
        THEN DISCH_THEN (fn th =>
                          GEN_TAC THEN DISCH_TAC
                            THEN FIRST_ASSUM (MP_TAC o MATCH_MP th))
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
        THEN DISCH_TAC
        THEN STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );



val _ = export_theory();

val _ = print_theory_to_file "-" "quotient.lst";
                                                                                
val _ = html_theory "quotient";

