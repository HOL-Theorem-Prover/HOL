(*==========================================================================*)
(*     FILE NAME:        mk_operator.sml                                    *)
(*                                                                          *)
(*     DESCRIPTION:      Creates the theory "operator" containing some      *)
(*                       basic algebraic operator definitions and related   *)
(*                       theorems about them.                               *)
(*                                                                          *)
(*     AUTHOR:           P. Curzon (Feb 25 1994)                            *)
(*                       (HOL88 Version by W. Wong)                         *)
(*                                                                          *)
(*     PARENTS:          BASIC-HOL.th                                       *)
(*     WRITES FILES:     operator.{holsig,thms}                             *)
(*                                                                          *)
(*                       University of Cambridge                            *)
(*                       Hardware Verification Group                        *)
(*                       Computer Laboratory                                *)
(*                       New Museums Site                                   *)
(*                       Pembroke Street                                    *)
(*                       Cambridge  CB2 3QG                                 *)
(*                       England                                            *)
(*                                                                          *)
(*     REVISION HISTORY: October'94 - name changed from "fun" to "operator" *)
(*                       (KLS)                                              *)
(*==========================================================================*)

structure operatorScript =
struct
local open boolTheory in end;

open HolKernel Parse boolTheory Drule Tactical Rewrite;
infix THEN THENL;

type thm = Thm.thm;

(* ======================================================================== *)
(*  Definitions and theorems of basic algebraic operators                   *)
(* ======================================================================== *)

val _ = new_theory "operator";

val ASSOC_DEF = new_definition("ASSOC_DEF",
(--`
    ASSOC (f:'a->'a->'a) = 
             (!x y z. f x (f y z) = f (f x y) z)
`--));

val COMM_DEF = new_definition("COMM_DEF",
(--`
    COMM (f:'a->'a->'b) = 
             (!x y. f x y = f y x)
`--));

val FCOMM_DEF = new_definition("FCOMM_DEF",
(--`
    FCOMM (f:'a->'b->'a) (g:'c->'a->'a) = 
             (!x y z.  g x (f y z) = f (g x y) z)
`--));

val RIGHT_ID_DEF = new_definition("RIGHT_ID_DEF",
(--`
    RIGHT_ID (f:'a->'b->'a) e = 
             (!x. f x e = x)
`--));

val LEFT_ID_DEF = new_definition("LEFT_ID_DEF",
(--`
    LEFT_ID (f:'a->'b->'b) e = 
             (!x. f e x = x)
`--));

val MONOID_DEF = new_definition("MONOID_DEF",
(--`
    MONOID (f:'a->'a->'a) e = 
             ASSOC f /\
             RIGHT_ID f e /\
             LEFT_ID f e
`--));

(* ======================================================================== *)
(*  Theorems about operators                                                *)
(* ======================================================================== *)

val ASSOC_CONJ = store_thm ("ASSOC_CONJ",
(--`ASSOC $/\`--),

REWRITE_TAC[ASSOC_DEF,CONJ_ASSOC]
);

val ASSOC_SYM = save_thm ("ASSOC_SYM",
Conv.CONV_RULE (Conv.STRIP_QUANT_CONV (Conv.RHS_CONV (Conv.STRIP_QUANT_CONV Conv.SYM_CONV))) ASSOC_DEF);


val ASSOC_DISJ = store_thm ("ASSOC_DISJ",
(--`ASSOC $\/`--),

REWRITE_TAC[ASSOC_DEF,DISJ_ASSOC]
);

val FCOMM_ASSOC = store_thm ("FCOMM_ASSOC",
(--`!f: 'a->'a->'a. FCOMM f f = ASSOC f`--),

REWRITE_TAC[ASSOC_DEF,FCOMM_DEF]
);

val MONOID_CONJ_T = store_thm ("MONOID_CONJ_T",
(--`MONOID $/\ T`--),

REWRITE_TAC[MONOID_DEF,CONJ_ASSOC,
            LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF]
);

val MONOID_DISJ_F = store_thm ("MONOID_DISJ_F",
(--`MONOID $\/ F`--),

REWRITE_TAC[MONOID_DEF,DISJ_ASSOC,
            LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF]
);


val _ = export_theory();

end
