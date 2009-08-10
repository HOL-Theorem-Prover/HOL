
(*****************************************************************************)
(* Puzzle from http://www.lego.com/matanui                                   *)
(*****************************************************************************)

(*****************************************************************************)
(* Nine boolean state variables                                              *)
(*                                                                           *)
(*    0 --- 1 --- 2                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    3 --- 4 --- 5                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    6 --- 7 --- 8                                                          *)
(*                                                                           *)
(* A transition consists of complementing a variable and all its             *)
(* immediate neighbours.                                                     *)
(*                                                                           *)
(* Problem is whether one can get from                                       *)
(*                                                                           *)
(*                                                                           *)
(*    F --- T --- F                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    T --- F --- T                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    F --- T --- F                                                          *)
(*                                                                           *)
(* to                                                                        *)
(*                                                                           *)
(*                                                                           *)
(*    F --- F --- F                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    F --- F --- F                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    F --- F --- F                                                          *)
(*                                                                           *)
(*****************************************************************************)

(* Comment out for compilation
load "HolBddLib";
load "PrimitiveBddRules";
load "ListPair";
*)

(* Needed for compilation *)
open HolKernel Parse boolLib;
infixr 3 -->;
infix 9 by;
infix ++;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
(**)

open bossLib;
open HolBddLib;
open bdd;
open pairSyntax;
open pairTools;
open pairTheory;

val _ = new_theory "KatiPuzzle";

val _ = Globals.priming := SOME "";

(*****************************************************************************)
(* Varmap (i.e. variable ordering) for later use                             *)
(*****************************************************************************)

val basic_varmap =
 extendVarmap
  (map
    (fn s => mk_var(s,bool))
    ["v0","v1","v2","v3","v4","v5","v6","v7","v8",
     "v0'","v1'","v2'","v3'","v4'","v5'","v6'","v7'","v8'",
     "c0","c1","c2","c3",
     "c0'","c1'","c2'","c3'"])
  empty;

(*****************************************************************************)
(* Initial state                                                             *)
(*****************************************************************************)

val Init_def =
 Define
  `Init(v0,v1,v2,v3,v4,v5,v6,v7,v8,c0:bool,c1:bool,c2:bool,c3:bool) =
    ~v0 /\ v1 /\ ~v2 /\ v3 /\ ~v4 /\ v5 /\ ~v6 /\ v7 /\ ~v8`;

(*****************************************************************************)
(* Transition relation                                                       *)
(*****************************************************************************)

val Trans_def =
 Define
  `Trans((v0,v1,v2,v3,v4,v5,v6,v7,v8,c0:bool,c1:bool,c2:bool,c3:bool),
         (v0',v1',v2',v3',v4',v5',v6',v7',v8',c0',c1',c2',c3')) =
    ((v0'=~v0)/\(v1'=~v1)/\(v2'=v2)/\(v3'=~v3)/\(v4'=v4)/\    (* toggle 0 *)
     (v5'=v5)/\(v6'=v6)/\(v7'=v7)/\(v8'=v8) /\ ~c3' /\ ~c2' /\ ~c1' /\~c0')
    \/
    ((v0'=~v0)/\(v1'=~v1)/\(v2'=~v2)/\(v3'=v3)/\(v4'=~v4)/\   (* toggle 1 *)
     (v5'=v5)/\(v6'=v6)/\(v7'=v7)/\(v8'=v8) /\ ~c3' /\ ~c2' /\ ~c1' /\ c0')
    \/
    ((v0'=v0)/\(v1'=~v1)/\(v2'=~v2)/\(v3'=v3)/\(v4'=v4)/\     (* toggle 2 *)
     (v5'=~v5)/\(v6'=v6)/\(v7'=v7)/\(v8'=v8) /\ ~c3' /\ ~c2' /\ c1' /\ ~c0')
    \/
    ((v0'=~v0)/\(v1'=v1)/\(v2'=v2)/\(v3'=~v3)/\(v4'=~v4)/\    (* toggle 3 *)
     (v5'=v5)/\(v6'=~v6)/\(v7'=v7)/\(v8'=v8) /\ ~c3' /\ ~c2' /\ c1' /\ c0')
    \/
    ((v0'=v0)/\(v1'=~v1)/\(v2'=v2)/\(v3'=~v3)/\(v4'=~v4)/\    (* toggle 4 *)
     (v5'=~v5)/\(v6'=v6)/\(v7'=~v7)/\(v8'=v8) /\ ~c3' /\ c2' /\ ~c1' /\ ~c0')
    \/
    ((v0'=v0)/\(v1'=v1)/\(v2'=~v2)/\(v3'=v3)/\(v4'=~v4)/\     (* toggle 5 *)
     (v5'=~v5)/\(v6'=v6)/\(v7'=v7)/\(v8'=~v8) /\ ~c3' /\ c2' /\ ~c1' /\ c0')
    \/
    ((v0'=v0)/\(v1'=v1)/\(v2'=v2)/\(v3'=~v3)/\(v4'=v4)/\      (* toggle 6 *)
     (v5'=v5)/\(v6'=~v6)/\(v7'=~v7)/\(v8'=v8) /\ ~c3' /\ c2' /\ c1' /\ ~c0')
    \/
    ((v0'=v0)/\(v1'=v1)/\(v2'=v2)/\(v3'=v3)/\(v4'=~v4)/\      (* toggle 7 *)
     (v5'=v5)/\(v6'=~v6)/\(v7'=~v7)/\(v8'=~v8) /\ ~c3' /\ c2' /\ c1' /\ c0')
    \/
    ((v0'=v0)/\(v1'=v1)/\(v2'=v2)/\(v3'=v3)/\(v4'=v4)/\       (* toggle 8 *)
     (v5'=~v5)/\(v6'=v6)/\(v7'=~v7)/\(v8'=~v8) /\ c3' /\ ~c2' /\ ~c1' /\ ~c0')`;

(*****************************************************************************)
(* Final state                                                               *)
(*****************************************************************************)

val Final_def =
 Define
  `Final(v0,v1,v2,v3,v4,v5,v6,v7,v8,c0:bool,c1:bool,c2:bool,c3:bool) =
    ~v0 /\ ~v1 /\ ~v2 /\ ~v3 /\ ~v4 /\ ~v5 /\ ~v6 /\ ~v7 /\ ~v8`;

val (_,thl,thfin) = findTrace basic_varmap Trans_def Init_def Final_def;

(******************************************************************************
Stuff commented out here superceded by findTrace

val s =
 ``(v0:bool,v1:bool,v2:bool,v3:bool,v4:bool,v5:bool,v6:bool,v7:bool,v8:bool,
    c0:bool,c1:bool,c2:bool,c3:bool)``;

val (by_th0,by_thsuc) =
 time
  (REWRITE_RULE[Eq_def,pairTheory.PAIR_EQ] ## REWRITE_RULE[Trans_def])
  (MkIterThms
    MachineTransitionTheory.ReachBy_rec
    (lhs(concl(SPEC_ALL Trans_def)))
    (lhs(concl(ISPECL[``(F,T,F,T,F,T,F,T,F,F,F,F,F)``,s]Eq_def))));

val (FinalTb,FinalTb') =
 computeFixedpoint
  (fn n => fn tb => print ".")
  basic_varmap
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

val Trace =
 computeTrace
  (fn n => fn tb => print".")
  basic_varmap
  Final_def
  (by_th0,by_thsuc);

val Solution = traceBack basic_varmap Trace Final_def Trans_def;
******************************************************************************)

(*****************************************************************************)
(* Print out a picture of a puzzle state from a tuple                        *)
(*                                                                           *)
(*   (v0,v1,v2,v3,v4,v5,v6,v7,v8,c0,c1,c2,c3)                                *)
(*                                                                           *)
(* where vi is T or F, and if n is V[c3,c2,c1,c0] the printing is            *)
(*                                                                           *)
(* n                                                                         *)
(*    0 --- 1 --- 2                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    3 --- 4 --- 5                                                          *)
(*    |     |     |                                                          *)
(*    |     |     |                                                          *)
(*    6 --- 7 --- 8                                                          *)
(*                                                                           *)
(* (number is omitted if flag is false)                                      *)
(*****************************************************************************)

fun PrintState flag tm =
 let val cl    = strip_pair tm
     fun s n   = el (n+1) cl
     fun p n   = print_term(s n)
     fun sp () = print " --- "
     fun nl () = print"\n"
     fun bv b = if b=T then 1 else 0
     fun pb(c3,c2,c1,c0) = print_term(intToTerm(8*(bv c3) + 4*(bv c2) + 2*(bv c1) + (bv c0)))
 in
  (nl();
   (if flag then (print"  "; pb(s 12, s 11, s 10, s 9) ; nl()) else ());
   print"      "    ;p 0 ;sp();p 1 ;sp();p 2 ;nl();
   print"      |     |     |"; nl();
   print"      "    ;p 3 ;sp();p 4 ;sp();p 5 ;nl();
   print"      |     |     |"; nl();
   print"      "    ;p 6 ;sp();p 7 ;sp();p 8 ;nl(); nl(); nl())
 end;

(*****************************************************************************)
(* Print out a trace as found by traceBack                                   *)
(*****************************************************************************)

fun PrintTrace cl =
 (print "\nThe number shows the position toggled to get to the following state\n\n";
  PrintState false (hd cl);
  map (PrintState true) (tl cl));

val _ = PrintTrace
         (List.map (fst o dest_pair o rand o concl) thl @ [rand(concl thfin)])

(* Solution found

The number shows the position toggled to get to the following state


      F --- T --- F
      |     |     |
      T --- F --- T
      |     |     |
      F --- T --- F



  1
      T --- F --- T
      |     |     |
      T --- T --- T
      |     |     |
      F --- T --- F



  3
      F --- F --- T
      |     |     |
      F --- F --- T
      |     |     |
      T --- T --- F



  5
      F --- F --- F
      |     |     |
      F --- T --- F
      |     |     |
      T --- T --- T



  7
      F --- F --- F
      |     |     |
      F --- F --- F
      |     |     |
      F --- F --- F

*)


val _ = export_theory();
