(*****************************************************************************)
(* Game of Solitaire (example from Bill Roscoe, but suggested by Tony Hoare) *)
(*****************************************************************************)

(*****************************************************************************)
(* State variable numbering:                                                 *)
(*                                                                           *)
(*              ----------------                                             *)
(*              | 07 | 14 | 21 |                                             *)
(*              ----------------                                             *)
(*              | 08 | 15 | 22 |                                             *)
(*    ------------------------------------                                   *)
(*    | 01 | 04 | 09 | 16 | 23 | 28 | 31 |                                   *)
(*    ------------------------------------                                   *)
(*    | 02 | 05 | 10 | 17 | 24 | 29 | 32 |                                   *)
(*    ------------------------------------                                   *)
(*    | 03 | 06 | 11 | 18 | 25 | 30 | 33 |                                   *)
(*    ------------------------------------                                   *)
(*              | 12 | 19 | 26 |                                             *)
(*              ----------------                                             *)
(*              | 13 | 20 | 27 |                                             *)
(*              ----------------                                             *)
(*                                                                           *)
(*****************************************************************************)

(*
load "HolBddLib";
load "PrimitiveBddRules";
load "ListPair";
*)

open HolKernel Parse boolLib;
infixr 3 -->;
infix 9 by;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;


open HolBddLib;
open pairSyntax;
open bossLib;

val _ = (Globals.priming := SOME "");

val _ = new_theory "Solitaire";

val var_list as
    [v01,v02,v03,v04,v05,v06,v07,v08,v09,v10,
     v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,
     v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,
     v31,v32,v33] =
    ["v01","v02","v03","v04","v05",
     "v06","v07","v08","v09","v10",
     "v11","v12","v13","v14","v15",
     "v16","v17","v18","v19","v20",
     "v21","v22","v23","v24","v25",
     "v26","v27","v28","v29","v30",
     "v31","v32","v33"];

val var_list' as
    [v01',v02',v03',v04',v05',v06',v07',v08',v09',v10',
     v11',v12',v13',v14',v15',v16',v17',v18',v19',v20',
     v21',v22',v23',v24',v25',v26',v27',v28',v29',v30',
     v31',v32',v33'] =
    map (fn v => v^"'") var_list;

(*****************************************************************************)
(* Make boolean variables (unprimed and primed)                              *)
(*****************************************************************************)

fun mk_bool_var s = mk_var(s,bool)
and mk_primed_bool_var s = mk_bool_var(s^"'");

(*****************************************************************************)
(* Good variable order is V01 < v01' < v02 < v02' ...                        *)
(* Function shuffle below used to create it                                  *)
(*****************************************************************************)

fun shuffle (l1,l2) =
 ListPair.foldr (fn(x1,x2,l) => x1 :: x2 :: l) [] (l1,l2);

val solitaire_varmap =
 extendVarmap (map mk_bool_var (shuffle(var_list,var_list'))) empty;

(*****************************************************************************)
(* State vectors                                                             *)
(*****************************************************************************)

val st  = list_mk_pair (map mk_bool_var var_list)
and st' = list_mk_pair (map mk_bool_var var_list');

(*****************************************************************************)
(* Initial state                                                             *)
(*****************************************************************************)

val SolitaireInit_def =
 Define
   `SolitaireInit ^st =
     ^(list_mk_conj(map (fn v => if v="v17" then mk_neg(mk_bool_var v)
                                            else mk_bool_var v) var_list))`;

(*****************************************************************************)
(* Final goal state                                                          *)
(*****************************************************************************)

val SolitaireFinal_def =
 Define
   `SolitaireFinal ^st =
     ^(list_mk_conj
        (map (fn v => if v="v17" then mk_bool_var v
                                 else mk_neg(mk_bool_var v)) var_list))`;

(*****************************************************************************)
(* Function to create a formula to represent a move in which a counter at v1 *)
(* jumps over and takes one at v2 and lands at v3, which must have been      *)
(* unoccupied.                                                               *)
(*****************************************************************************)

fun make_move_trans (v1,v2,v3) =
 let val (_,unchanged) = List.partition (fn v => mem v [v1,v2,v3]) var_list
 in
 list_mk_conj
  ([mk_bool_var v1, mk_bool_var v2, mk_neg(mk_bool_var v3),
    mk_neg(mk_primed_bool_var v1), mk_neg(mk_primed_bool_var v2), mk_primed_bool_var v3]
   @
   (map (fn v => mk_eq(mk_primed_bool_var v,mk_bool_var v)) unchanged))
 end;

(*****************************************************************************)
(* List of all possible moves                                                *)
(*****************************************************************************)

val moves =
 [(v01,v04,v09), (v01,v02,v03),
  (v02,v05,v10),
  (v03,v02,v01), (v03,v06,v11),
  (v04,v05,v06), (v04,v09,v16),
  (v05,v10,v17),
  (v06,v05,v04), (v06,v11,v18),
  (v07,v08,v09), (v07,v14,v21),
  (v08,v09,v10), (v08,v15,v22),
  (v09,v08,v07), (v09,v10,v11), (v09,v04,v01), (v09,v16,v23),
  (v10,v09,v08), (v10,v11,v12), (v10,v05,v02), (v10,v17,v24),
  (v11,v10,v09), (v11,v12,v13), (v11,v06,v03), (v11,v18,v25),
  (v12,v11,v10), (v12,v19,v26),
  (v13,v12,v11), (v13,v20,v27),
  (v14,v15,v16),
  (v15,v16,v17),
  (v16,v15,v14), (v16,v17,v18), (v16,v09,v04), (v16,v23,v28),
  (v17,v16,v15), (v17,v18,v19), (v17,v10,v05), (v17,v24,v29),
  (v18,v17,v16), (v18,v19,v20), (v18,v11,v06), (v18,v25,v30),
  (v19,v18,v17),
  (v20,v19,v18),
  (v21,v22,v23), (v21,v14,v07),
  (v22,v23,v24), (v22,v15,v08),
  (v23,v22,v21), (v23,v24,v25), (v23,v16,v09), (v23,v28,v31),
  (v24,v23,v22), (v24,v25,v26), (v24,v17,v10), (v24,v29,v32),
  (v25,v24,v23), (v25,v26,v27), (v25,v18,v11), (v25,v30,v33),
  (v26,v25,v24), (v26,v19,v12),
  (v27,v26,v25), (v27,v20,v13),
  (v28,v29,v30), (v28,v23,v16),
  (v29,v24,v17),
  (v30,v29,v28), (v30,v25,v18),
  (v31,v32,v33), (v31,v28,v23),
  (v32,v29,v24),
  (v33,v32,v31), (v33,v30,v25)];

(*****************************************************************************)
(* Define transition relation as disjunction of all moves                    *)
(*****************************************************************************)

val SolitaireTrans_def =
 Define
  `SolitaireTrans(^st,^st') = ^(list_mk_disj(map make_move_trans moves))`;

val (initth,transthl,finalth) =
 time
  (findTrace solitaire_varmap SolitaireTrans_def SolitaireInit_def)
  SolitaireFinal_def;

(*
val trace_list = ref[];

fun report n tb =
 (trace_list := append (!trace_list) [tb]; print "Iteration: "; print (Int.toString n);
  print " Node size: "; print(Int.toString(bdd.nodecount(getBdd tb))); print "\n");

val (in_th0,in_thsuc) =
 time
  (REWRITE_RULE[SolitaireInit_def] ## REWRITE_RULE[SolitaireTrans_def])
  (MkIterThms
    MachineTransitionTheory.ReachBy_rec
    (lhs(concl(SPEC_ALL SolitaireTrans_def)))
    (lhs(concl(SPEC_ALL SolitaireInit_def))));

val (tb,tb') = time (computeFixedpoint report solitaire_varmap) (in_th0,in_thsuc);

val (in_th0,in_thsuc) =
 time
  (REWRITE_RULE[SolitaireInit_def] ##
   simpLib.SIMP_RULE boolSimps.bool_ss [SolitaireTrans_def,LEFT_AND_OVER_OR,EXISTS_OR_THM])
  (MkIterThms
    MachineTransitionTheory.ReachBy_rec
    (lhs(concl(SPEC_ALL SolitaireTrans_def)))
    (lhs(concl(SPEC_ALL SolitaireInit_def))));

val (tb1,tb1') = time (computeFixedpoint report solitaire_varmap) (in_th0,in_thsuc);
*)

(*****************************************************************************)
(* Print out a picture of a Solitaire board from a tuple                     *)
(*                                                                           *)
(*   (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,    *)
(*   (c21,c22,c23,c24,c25,c26,c27,c28,c29,c30,c31,c32,c3)                    *)
(*                                                                           *)
(* where cij is T or F                                                       *)
(*                                                                           *)
(* and the printing is                                                       *)
(*                                                                           *)
(*      XXX                                                                  *)
(*      XXX                                                                  *)
(*    XXXXXXX                                                                *)
(*    XXXXXXX                                                                *)
(*    XXXXXXX                                                                *)
(*      XXX                                                                  *)
(*      XXX                                                                  *)
(*****************************************************************************)

fun PrintState tm =
 let val cl    = strip_pair tm
     fun p n   = if el n cl = ``T`` then print "1" else print "0"
     fun sp () = print "   "
     fun nl () = print"\n"
 in
  (print"  ";p 07;p 14;p 21;nl();
   print"  ";p 08;p 15;p 22;nl();
   p 01;p 04;p 09;p 16;p 23;p 28;p 31;nl();
   p 02;p 05;p 10;p 17;p 24;p 29;p 32;nl();
   p 03;p 06;p 11;p 18;p 25;p 30;p 33;nl();
   print"  ";p 12;p 19;p 26;nl();
   print"  ";p 13;p 20;p 22;nl();nl())
 end;

(*****************************************************************************)
(* Print out a trace as found by findTrace                                   *)
(*****************************************************************************)

val _ =
 List.map
  PrintState
  (List.map (fst o dest_pair o rand o concl) transthl @ [rand(concl finalth)]);

val _ = export_theory();


(* Reachable state with/without disjunctive partitioning

fun computeSimpReachable vm Rth Bth =
 let val (by_th0,by_thsuc) =
          (REWRITE_RULE[Bth,pairTheory.PAIR_EQ] ## REWRITE_RULE[Rth])
           (MkIterThms
             MachineTransitionTheory.ReachBy_rec
             (lhs(concl(SPEC_ALL Rth)))
             (lhs(concl(SPEC_ALL Bth))))
     val _ = print "Starting disjunctive partitioning ...\n"
     val by_thsuc_simp = time MakeSimpRecThm by_thsuc
     val _ = print "disjunctive partitioning complete.\n"
     val _ = print "Computing reachable states ...\n"
 in
  time (computeFixedpoint (fn n=>fn tb=>print".") vm) (by_th0,by_thsuc_simp)
 end;

val SimpReachable =
 computeSimpReachable solitaire_varmap SolitaireTrans_def SolitaireInit_def;

(*
Starting disjunctive partitioning ...
runtime: 1112.520s,    gctime: 512.900s,     systime: 1.750s.
disjunctive partitioning complete.
Computing reachable states ...

*)

fun computeReachable vm Rth Bth =
 let val (by_th0,by_thsuc) =
          (REWRITE_RULE[Bth,pairTheory.PAIR_EQ] ## REWRITE_RULE[Rth])
           (MkIterThms
             MachineTransitionTheory.ReachBy_rec
             (lhs(concl(SPEC_ALL Rth)))
             (lhs(concl(SPEC_ALL Bth))))
 in
  time (computeFixedpoint (fn n=>fn tb=>print".") vm) (by_th0,by_thsuc)
 end;

val Reachable =
 computeSimpReachable solitaire_varmap SolitaireTrans_def SolitaireInit_def;

*)
