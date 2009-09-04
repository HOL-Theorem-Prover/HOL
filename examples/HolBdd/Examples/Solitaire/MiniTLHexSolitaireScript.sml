
(*****************************************************************************)
(* This file first defines a small transistion system                        *)
(* (HexSolitaire, which I had lying around).                                 *)
(*                                                                           *)
(* Next two versions of a mini temporal logic are defined.                   *)
(*                                                                           *)
(* Finally there are some rudimentary model checking examples.               *)
(*****************************************************************************)

(*****************************************************************************)
(* Simplified game of Solitaire                                              *)
(*****************************************************************************)

(*****************************************************************************)
(* State variables                                                           *)
(*                                                                           *)
(*               01  02  03                                                  *)
(*             04  05  06  07                                                *)
(*           08  09  10  11  12                                              *)
(*             13  14  15  16                                                *)
(*               17  18  19                                                  *)
(*                                                                           *)
(*****************************************************************************)

(* Comment out for compilation
load "HolBddLib";
load "PrimitiveBddRules";
load "ListPair";
load "stringLib";
*)

(* Needed for compilation *)
open HolKernel Parse boolLib;
infixr 3 -->;
infix 9 by;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

open bossLib;
open HolBddLib;
open bdd;
open stringLib;
open pairSyntax;
open pairTools;
open pairTheory;

val _ = new_theory "MiniTLHexSolitaire";

val _ = Globals.priming := SOME "";

(*****************************************************************************)
(* List of board positions                                                   *)
(*****************************************************************************)

val vl = [01,02,03,04,05,06,07,08,09,10,11,12,13,14,15,16,17,18,19];

(*****************************************************************************)
(* Make an unprimed varibale for a board position                            *)
(*****************************************************************************)

fun mk_v n =
 if n<10 then mk_var("v0"^(int_to_string n),bool)
         else mk_var("v"^(int_to_string n),bool);

(*****************************************************************************)
(* Make a primed varibale for a board position                               *)
(*****************************************************************************)

fun mk_v' n =
 if n<10 then mk_var("v0"^(int_to_string n)^"'",bool)
         else mk_var("v"^(int_to_string n)^"'",bool);

(*****************************************************************************)
(* Make state vector and primed state vector                                 *)
(*****************************************************************************)

val s  = list_mk_pair (map mk_v vl)
and s' = list_mk_pair (map mk_v' vl);

(*****************************************************************************)
(* Funtion to shuffle unprimed and primed state variables                    *)
(*****************************************************************************)

fun shuffle (l1,l2) =
 ListPair.foldr (fn(x1,x2,l) => x1 :: x2 :: l) [] (l1,l2);

(*****************************************************************************)
(* Varmap (i.e. variable ordering) for later use                             *)
(*****************************************************************************)

val hexsolitaire_varmap =
 extendVarmap
  (map
    (fn s => mk_var(s,bool))
    (shuffle(map (fst o dest_var o mk_v) vl, map (fst o dest_var o mk_v') vl)))
  empty;

(*****************************************************************************)
(* Make a transition relation term for a single move in which n1 jumps       *)
(* over (and so removes) n2 into n3                                          *)
(*****************************************************************************)

fun make_move (n1,n2,n3) =
 let val (_,unchanged) = List.partition (fn n => mem n [n1,n2,n3]) vl
 in
 list_mk_conj
  ([mk_v n1,mk_v n2,mk_neg(mk_v n3),
    mk_neg(mk_v' n1),mk_neg(mk_v' n2),mk_v' n3]
   @
   (map (fn n => mk_eq(mk_v' n,mk_v n)) unchanged))
 end;

(*****************************************************************************)
(* List of posible moves                                                     *)
(*****************************************************************************)

val moves =
 [(01,02,03),(01,05,10),(01,04,08),
  (02,06,11),(02,05,09),
  (03,07,12),(03,06,10),(03,02,01),
  (04,05,06),(04,09,14),
  (05,06,07),(05,10,15),(05,09,13),
  (06,11,16),(06,10,14),(06,05,04),
  (07,11,15),(07,06,05),
  (08,04,01),(08,09,10),(08,13,17),
  (09,05,02),(09,10,11),(09,14,18),
  (10,09,08),(10,05,01),(10,06,03),(10,11,12),(10,15,19),(10,14,17),
  (11,10,09),(11,06,02),(11,15,18),
  (12,11,10),(12,07,03),(12,16,19),
  (13,09,05),(13,14,15),
  (14,09,04),(14,10,06),(14,15,16),
  (15,14,13),(15,10,05),(15,11,07),
  (16,15,14),(16,11,06),
  (17,13,08),(17,14,10),(17,18,19),
  (18,14,09),(18,15,11),
  (19,18,17),(19,15,10),(19,16,12)];

(*****************************************************************************)
(* Make the disjunction of all possible moves (i.e. the transition relation) *)
(*****************************************************************************)

val HexSolitaireTrans_def =
  bossLib.Define `HexSolitaireTrans(^s,^s') =
   ^(list_mk_disj(map make_move moves))`;

(*****************************************************************************)
(* Final goal state: only positions 10 and 18 filled                         *)
(*****************************************************************************)

val HexSolitaireFinal_def =
 bossLib.Define
  `HexSolitaireFinal ^s =
     ^(list_mk_conj
        (map (fn n => if (n=10 orelse n=18)
                       then mk_v n
                       else mk_neg(mk_v n)) vl))`;

(*****************************************************************************)
(* Compute term_bdd of set of states reachable from initial state            *)
(*                                                                           *)
(*  (T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T)                                  *)
(*                                                                           *)
(* First compute iteration theorems by_th0 and by_thsuc                      *)
(*                                                                           *)
(* Then iterate to a fixed point                                             *)
(*                                                                           *)
(* Finally, use ReachBy_fixedpoint to compute ReachTb, the term_bdd of       *)
(*                                                                           *)
(*  ``Reachable HexSolitaireTrans                                            *)
(*     (Eq (T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T))                          *)
(*     (v01,v02,v03,v04,v05,v06,v07,v08,v09,v10,v11,                         *)
(*      v12,v13,v14,v15,v16,v17,v18,v19)``                                   *)
(*                                                                           *)
(*****************************************************************************)

val (by_th0,by_thsuc) =
 time
  (REWRITE_RULE[Eq_def,pairTheory.PAIR_EQ] ## REWRITE_RULE[HexSolitaireTrans_def])
  (MkIterThms
    MachineTransitionTheory.ReachBy_rec
    (lhs(concl(SPEC_ALL HexSolitaireTrans_def)))
    (lhs(concl(ISPECL[``(T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T)``,s]Eq_def))));

val (FinalTb,FinalTb') =
 computeFixedpoint
  (fn n => fn tb => print ".")
  hexsolitaire_varmap
  (by_th0,by_thsuc);

val ReachTb =
 BddEqMp
  (SYM
    (AP_THM
     (MATCH_MP
       ReachBy_fixedpoint
       (EXT
         (PGEN
           (mk_var("s",type_of s))
           s
           (BddThmOracle(BddOp(Biimp,FinalTb,FinalTb'))))))
     s))
  FinalTb;

(*****************************************************************************)
(* A Mini Temporal Logic                                                     *)
(*****************************************************************************)

val _ =
 Hol_datatype
  `wff = ATOM     of ('state -> bool)
       | NOT      of wff
       | AND      of wff => wff
       | OR       of wff => wff
       | SOMETIME of wff
       | ALWAYS   of wff`;

val Eval_def =
 Define
  `(Eval (ATOM p)     R s = p s)                                        /\
   (Eval (NOT f)      R s = ~(Eval f R s))                              /\
   (Eval (AND f1 f2)  R s = Eval f1 R s /\ Eval f2 R s)                 /\
   (Eval (OR f1 f2)   R s = Eval f1 R s \/ Eval f2 R s)                 /\
   (Eval (SOMETIME f) R s = ?s'. Reachable R (Eq s) s' /\  Eval f R s') /\
   (Eval (ALWAYS f)   R s = !s'. Reachable R (Eq s) s' ==> Eval f R s')`;

(*****************************************************************************)
(* Compute the term_bdd of                                                   *)
(*                                                                           *)
(* ``Eval                                                                    *)
(*    ^wff                                                                   *)
(*    HexSolitaireTrans                                                      *)
(*    (T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T)``                              *)
(*****************************************************************************)

fun Check wff =
 let val th = simpLib.SIMP_CONV
               std_ss
               [Eval_def,EXISTS_PROD,FORALL_PROD,HexSolitaireFinal_def]
               ``Eval
                  ^wff
                  HexSolitaireTrans
                  (T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T)``
      val (t1,t2) = dest_eq(concl th)
      val tb = GenTermToTermBdd (BddApRestrict ReachTb) hexsolitaire_varmap t2
  in
   BddEqMp (SYM th) tb
  end;

(*****************************************************************************)
(* Some examples                                                             *)
(*****************************************************************************)

val EvalTb = Check ``(SOMETIME (ATOM HexSolitaireFinal))``;

val wff1 =
 ``\(v01,v02,v03,v04,v05,v06,v07,v08,v09,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19).
    ~v01 /\ ~v02 /\ ~v03 /\ ~v04 /\ ~v05 /\ ~v06 /\ ~v07 /\ ~v08 /\
    ~v09 /\ v10 /\ ~v11 /\ ~v12 /\ ~v13 /\ ~v14 /\ ~v15 /\ ~v16 /\ ~v17 /\ v18 /\ ~v19``;

val EvalTb1 = Check ``(SOMETIME (ATOM ^wff1))``;

val wff2 =
 ``\(v01,v02,v03,v04,v05,v06,v07,v08,v09,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19).
    v01 /\ v02 /\ v03 /\ ~v04 /\ ~v05 /\ ~v06 /\ ~v07 /\ ~v08 /\
    ~v09 /\ ~v10 /\ ~v11 /\ ~v12 /\ ~v13 /\ ~v14 /\ ~v15 /\ ~v16 /\ ~v17 /\ ~v18 /\ ~v19``;

val EvalTb2 = Check ``(SOMETIME (ATOM ^wff2))``;

val wff3 =
 ``\(v01,v02,v03,v04,v05,v06,v07,v08,v09,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19).
    ~v01 /\ ~v02 /\ ~v03 /\ ~v04 /\ ~v05 /\ ~v06 /\ ~v07 /\ ~v08 /\
    ~v09 /\ v10 /\ ~v11 /\ ~v12 /\ ~v13 /\ ~v14 /\ ~v15 /\ ~v16 /\ ~v17 /\ ~v18 /\ ~v19``;

val EvalTb3 = Check ``(SOMETIME (ATOM ^wff3))``;

(*****************************************************************************)
(* Convert to a HOL theorem                                                  *)
(*****************************************************************************)

val ModelCheckTh = BddThmOracle EvalTb;

val ModelCheckTh1 = BddThmOracle EvalTb1;

val ModelCheckTh2 = BddThmOracle EvalTb2;

(*
val ModelCheckTh3 = BddThmOracle EvalTb3;
*)


(*****************************************************************************)
(* A version of the Mini Temporal Logic with Kripke structures               *)
(*****************************************************************************)

val _ =
 Hol_datatype
  `awff = aATOM     of string
        | aNOT      of awff
        | aAND      of awff => awff
        | aOR       of awff => awff
        | aSOMETIME of awff
        | aALWAYS   of awff`;

val aEval_def =
 Define
  `(aEval (aATOM a)     (R,L) s = L a s)                                           /\
   (aEval (aNOT f)      (R,L) s = ~(aEval f (R,L) s))                              /\
   (aEval (aAND f1 f2)  (R,L) s = aEval f1 (R,L) s /\ aEval f2 (R,L) s)            /\
   (aEval (aOR f1 f2)   (R,L) s = aEval f1 (R,L) s \/ aEval f2 (R,L) s)            /\
   (aEval (aSOMETIME f) (R,L) s = ?s'. Reachable R (Eq s) s' /\  aEval f (R,L) s') /\
   (aEval (aALWAYS f)   (R,L) s = !s'. Reachable R (Eq s) s' ==> aEval f (R,L) s')`;

(*****************************************************************************)
(* Compute the term_bdd of                                                   *)
(*                                                                           *)
(* ``aEval                                                                   *)
(*    ass                                                                    *)
(*    ^awff                                                                  *)
(*    (HexSolitaireTrans,^L)                                                 *)
(*    (T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T)``                              *)
(*                                                                           *)
(* where ass is a list of assumptions that is used in simplification         *)
(*****************************************************************************)

fun aCheck ass L awff =
 let val th = simpLib.SIMP_CONV
               std_ss
               ([aEval_def,EXISTS_PROD,FORALL_PROD,HexSolitaireFinal_def]
                @ List.map ASSUME ass)
               ``aEval
                  ^awff
                  (HexSolitaireTrans,^L)
                  (T,T,T,T,T,T,T,T,T,F,T,T,T,T,T,T,T,T,T)``
      val (t1,t2) = dest_eq(concl th)
      val tb = GenTermToTermBdd (BddApRestrict ReachTb) hexsolitaire_varmap t2
  in
   BddEqMp (SYM th) tb
  end;

(*****************************************************************************)
(* Some examples to illustrate using assumptions                             *)
(*****************************************************************************)

val aEvalTb =
 aCheck
 []
 ``\a s. if a="HexSolitaireFinal" then HexSolitaireFinal s else F``
 ``(aSOMETIME (aATOM "HexSolitaireFinal"))``;

val aModelCheckTh = BddThmOracle aEvalTb;

val _ = set_fixity "aAND" (Infixl 500);

(*****************************************************************************)
(* v01,...,v19 free in finalwff                                              *)
(*****************************************************************************)

val finalwff =
 ``aNOT(aATOM v01) aAND aNOT(aATOM v02) aAND aNOT(aATOM v03) aAND
   aNOT(aATOM v04) aAND aNOT(aATOM v05) aAND aNOT(aATOM v06) aAND
   aNOT(aATOM v07) aAND aNOT(aATOM v08) aAND aNOT(aATOM v09) aAND
   aATOM v10 aAND
   aNOT(aATOM v11) aAND aNOT(aATOM v12) aAND aNOT(aATOM v13) aAND
   aNOT(aATOM v14) aAND aNOT(aATOM v15) aAND aNOT(aATOM v16) aAND
   aNOT(aATOM v17) aAND
   aATOM v18 aAND
   aNOT(aATOM v19)``;

(*****************************************************************************)
(* Assume vi equals string "vi" (0 <= i <= 19)                               *)
(*****************************************************************************)

val var_ass =
 [``v01 = "v01"``,``v02 = "v02"``,``v03 = "v03"``,``v04 = "v04"``,
  ``v05 = "v05"``,``v06 = "v06"``,``v07 = "v07"``,``v08 = "v08"``,
  ``v09 = "v09"``,``v10 = "v10"``,``v11 = "v11"``,``v12 = "v12"``,
  ``v13 = "v13"``,``v14 = "v14"``,``v15 = "v15"``,``v16 = "v16"``,
  ``v17 = "v17"``,``v18 = "v18"``,``v19 = "v19"``];

(*****************************************************************************)
(* Assume L maps "vi" to selector on ith component of state (0 <= i <= 19)   *)
(*****************************************************************************)

val L_ass =
 [``!v01 v02 v03 v04 v05 v06 v07 v08 v09 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19.
    (L"v01" ^s = v01)/\(L"v02" ^s = v02)/\(L"v03" ^s = v03)/\(L"v04" ^s = v04)/\
    (L"v05" ^s = v05)/\(L"v06" ^s = v06)/\(L"v07" ^s = v07)/\(L"v08" ^s = v08)/\
    (L"v09" ^s = v09)/\(L"v10" ^s = v10)/\(L"v11" ^s = v11)/\(L"v12" ^s = v12)/\
    (L"v13" ^s = v13)/\(L"v14" ^s = v14)/\(L"v15" ^s = v15)/\(L"v16" ^s = v16)/\
    (L"v17" ^s = v17)/\(L"v18" ^s = v18)/\(L"v19" ^s = v19)``];

(*****************************************************************************)
(* Create a variable ``L`` with appropriate type                             *)
(*****************************************************************************)

val L = ``L:string->^(ty_antiq(type_of s))->bool``;

(*****************************************************************************)
(* Example with assumptions about L and vi                                   *)
(*****************************************************************************)

val aEvalTb2 =
 aCheck
 (L_ass @  var_ass)
 L
 ``(aSOMETIME ^finalwff)``;

val aModelCheckTh2 = BddThmOracle aEvalTb2;

val _ = export_theory();
