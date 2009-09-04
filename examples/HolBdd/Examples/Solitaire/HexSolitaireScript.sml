

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

(* Nice ASCII picture (rotated 90 degrees from one above)

    X
  X   X
X   X   X
  X   X
X   X   X
  X   X
X   X   X
  X   X
    X

                             ____
                            /    \
                       ____/  12  \____
                      /    \      /    \
                 ____/  07  \____/  16  \____
                /    \      /    \      /    \
               /  03  \____/  11  \____/  19  \
               \      /    \      /    \      /
                \____/  06  \____/  15  \____/
                /    \      /    \      /    \
               /  02  \____/  10  \____/  18  \
               \      /    \      /    \      /
                \____/  05  \____/  14  \____/
                /    \      /    \      /    \
               /  01  \____/  09  \____/  17  \
               \      /    \      /    \      /
                \____/  04  \____/  13  \____/
                     \      /    \      /
                      \____/  08  \____/
                           \      /
                            \____/

*)


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
open bdd;
open pairSyntax;
open bossLib;

val _ = new_theory "HexSolitaire";

val _ = Globals.priming := SOME "";

val vl = [01,02,03,04,05,06,07,08,09,10,11,12,13,14,15,16,17,18,19];

fun mk_v n =
 if n<10 then mk_var("v0"^(int_to_string n),bool)
         else mk_var("v"^(int_to_string n),bool);

fun mk_v' n =
 if n<10 then mk_var("v0"^(int_to_string n)^"'",bool)
         else mk_var("v"^(int_to_string n)^"'",bool);

val s  = list_mk_pair (map mk_v vl)
and s' = list_mk_pair (map mk_v' vl);

fun shuffle (l1,l2) =
 ListPair.foldr (fn(x1,x2,l) => x1 :: x2 :: l) [] (l1,l2);

fun mk_bool_var s = mk_var(s,bool);

val hexsolitaire_varmap =
 extendVarmap
  (map mk_bool_var (shuffle(map (fst o dest_var o mk_v) vl, map (fst o dest_var o mk_v') vl)))
  empty;

val HexSolitaireInit_def =
 bossLib.Define
  `HexSolitaireInit ^s =
     ^(list_mk_conj
        (map (fn n => if n=10 then mk_neg(mk_v n) else mk_v n) vl))`;

fun make_move (n1,n2,n3) =
 let val (_,unchanged) = List.partition (fn n => mem n [n1,n2,n3]) vl
 in
 list_mk_conj
  ([mk_v n1,mk_v n2,mk_neg(mk_v n3),
    mk_neg(mk_v' n1),mk_neg(mk_v' n2),mk_v' n3]
   @
   (map (fn n => mk_eq(mk_v' n,mk_v n)) unchanged))
 end;

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

val HexSolitaireTrans_def =
  bossLib.Define `HexSolitaireTrans(^s,^s') =
   ^(list_mk_disj(map make_move moves))`;

(*****************************************************************************)
(* Final goal state                                                          *)
(*****************************************************************************)

val HexSolitaireFinish_def =
 bossLib.Define
  `HexSolitaireFinish ^s =
     ^(list_mk_conj
        (map (fn n => if (n=10 orelse n=18)
                       then mk_v n
                       else mk_neg(mk_v n)) vl))`;

(* This has no solution
val HexSolitaireFinish_def =
 bossLib.Define
  `HexSolitaireFinish ^s =
     ^(list_mk_conj
        (map (fn n => if (n=10)
                       then mk_v n
                       else mk_neg(mk_v n)) vl))`;
*)

val (initth,transthl,finalth) =
 findTrace
  hexsolitaire_varmap
  HexSolitaireTrans_def
  HexSolitaireInit_def
  HexSolitaireFinish_def;

(*****************************************************************************)
(* Print out a picture of a HexSolitaire board from a tuple                  *)
(*                                                                           *)
(*   (c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19)    *)
(*                                                                           *)
(* where cij is T or F                                                       *)
(*                                                                           *)
(* and the printing is                                                       *)
(*                                                                           *)
(*               X   X   X                                                   *)
(*             X   X   X   X                                                 *)
(*           X   X   X   X   X                                               *)
(*             X   X   X   X                                                 *)
(*               X   X   X                                                   *)
(*****************************************************************************)

fun PrintState tm =
 let val cl    = strip_pair tm
     fun p n   = print_term(el n cl)
     fun sp () = print "   "
     fun nl () = print"\n"
 in
  (print"      ";p 1 ;sp();p 2 ;sp();p 3 ;nl();
   print"    "  ;p 4 ;sp();p 5 ;sp();p 6 ;sp();p 7 ;nl();
   print"  "    ;p 8 ;sp();p 9 ;sp();p 10;sp();p 11;sp();p 12;nl();
   print"    "  ;p 13;sp();p 14;sp();p 15;sp();p 16;nl();
   print"      ";p 17;sp();p 18;sp();p 19;nl();nl())
 end;

(*****************************************************************************)
(* Print out a trace as found by findTrace                                   *)
(*****************************************************************************)

val _ =
 List.map
  PrintState
  (List.map (fst o dest_pair o rand o concl) transthl @ [rand(concl finalth)]);

val _ = export_theory();
