(* An alternative approach to creating finite sets as a quotient of lists.  *)
(* This takes the extensionality principle as the definition of equivalence.*)
(* Composed and contributed by Michael Norrish.                             *)
(* June 24, 2005.                                                           *)

open HolKernel Parse boolLib bossLib BasicProvers listTheory quotientLib

val _ = new_theory "ext_finite_set";

fun Store_Thm(n,t,tac) = store_thm(n,t,tac) before
                         export_rewrites [n]

val leq_def = Define`leq x y = !e:'a. MEM e x = MEM e y`

val leq_refl = Store_Thm(
  "leq_refl",
  ``!x :'a list. leq x x``,
  SRW_TAC [] [leq_def]);

val leq_sym = Store_Thm(
  "leq_sym",
  ``!x y :'a list. leq x y ==> leq y x``,
  SRW_TAC [] [leq_def]);

val leq_trans = Store_Thm(
  "leq_trans",
  ``!x y z :'a list. leq x y /\ leq y z ==> leq x z``,
  SRW_TAC [] [leq_def]);

(* functions on representatives *)

(* insertion is represented by :: *)
val NOT_NIL_EQUIV_CONS = store_thm(
  "NOT_NIL_EQUIV_CONS",
  ``~(leq [] ((a:'a)::A))``,
  SRW_TAC [boolSimps.DNF_ss] [leq_def]);

val NIL_RSP = store_thm(
  "NIL_RSP",
  ``leq ([]:'a list) []``,
  SRW_TAC [] [leq_def]);

val CONS_RSP = store_thm(
  "CONS_RSP",
  ``!x:'a A B. leq A B ==> leq (x::A) (x::B)``,
  SRW_TAC [] [leq_def]);

(* membership is represented by MEM *)
val MEM_RSP = store_thm(
  "MEM_RSP",
  ``!X Y x:'a. leq X Y ==> (MEM x X = MEM x Y)``,
  SRW_TAC [] [leq_def]);

val NO_MEM_NIL = Store_Thm(
  "NO_MEM_NIL",
  ``!A. (!a:'a. ~(MEM a A)) = (A = [])``,
  Induct_on `A` THEN SRW_TAC [] [] THEN PROVE_TAC []);

val NONE_MEM_NIL = store_thm(
  "NONE_MEM_NIL",
  ``!A. (!a:'a. ~(MEM a A)) = (leq A [])``,
  SRW_TAC [] [leq_def]);

val MEM_CONS = store_thm(
  "MEM_CONS",
  ``!A (a:'a). MEM a A ==> leq (a :: A) A``,
  SRW_TAC [] [leq_def] THEN PROVE_TAC []);

val CONS_LEFT_COMM = prove(
  ``!A x y:'a. leq (x::y::A) (y::x::A)``,
  SRW_TAC [] [leq_def] THEN PROVE_TAC []);

val CONS_LEFT_IDEM = prove(
  ``!A x:'a. leq (x::x::A) (x::A)``,
  SRW_TAC [] [leq_def] THEN PROVE_TAC []);

val finite_set1_strong_cases = store_thm(
  "finite_set1_strong_cases",
  ``!X. (X = []) \/ ?(a:'a) Y. ~MEM a Y /\ leq X (a::Y)``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [leq_def] THEN
  METIS_TAC [MEM]);

(* Delete1 *)
val Delete1_def = Define
   `($Delete1 [] x = [])  /\
    ($Delete1 ((a:'a) :: A) x = if a = x then $Delete1 A x
                                     else a :: ($Delete1 A x))`;
val _ = export_rewrites ["Delete1_def"]

val _ = add_infix ("Delete1", 500, HOLgrammars.LEFT);

Theorem MEM_Delete1:
  !A (a:'a) x. MEM x (A Delete1 a) <=> MEM x A /\ ~(x = a)
Proof
  Induct THEN SRW_TAC[][] THEN PROVE_TAC []
QED

val MEM_Delete1_IDENT = Store_Thm(
  "MEM_Delete1_IDENT",
  ``!A (a:'a). ~(MEM a (A Delete1 a))``,
  Induct_on `A` THEN SRW_TAC [][]);

val NOT_MEM_Delete1_IDENT = store_thm(
  "NOT_MEM_Delete1_IDENT",
  ``!A (b:'a). ~MEM b A ==> (A Delete1 b = A)``,
  Induct_on `A` THEN SRW_TAC [][]);

val Delete1_RSP = store_thm(
  "Delete1_RSP",
  ``!A B (a:'a). leq A B ==> (leq (A Delete1 a) (B Delete1 a))``,
  SRW_TAC [] [leq_def,MEM_Delete1]);

val CONS_Delete1 = store_thm(
  "CONS_Delete1",
  ``!A (a:'a). leq (a :: (A Delete1 a)) (if MEM a A then A else a::A)``,
  SRW_TAC [] [leq_def, MEM_Delete1] THEN PROVE_TAC []);

val MEM_CONS_Delete1 = store_thm
   ("MEM_CONS_Delete1",
    ``!A (a:'a). MEM a A ==> leq (a :: (A Delete1 a)) A``,
    PROVE_TAC [CONS_Delete1]
   );

val finite_set1_Delete1_cases1 = store_thm
   ("finite_set1_Delete1_cases1",
    ``!X. (X = []) \/ ?a:'a. leq X (a :: (X Delete1 a))``,
    Cases THEN SRW_TAC [][leq_def, MEM_Delete1] THEN METIS_TAC []);

val finite_set1_Delete1_cases = store_thm
   ("finite_set1_Delete1_cases",
    ``!X. (X = []) \/
            ?a:'a. MEM a X /\ leq X (a :: (X Delete1 a))``,
    PROVE_TAC[finite_set1_Delete1_cases1,MEM,MEM_RSP]
   );

(* Card1 *)

val Card1_def = Define
   `(Card1 ([]) = 0)  /\
    (Card1 ((a:'a) :: A) = if MEM a A then Card1 A else SUC (Card1 A))`;
val _ = export_rewrites ["Card1_def"]

val NOT_MEM_Card1 = store_thm
   ("NOT_MEM_Card1",
    ``!A:'a list a. ~(MEM a A) ==>
             (Card1 (a :: A) = SUC (Card1 A))``,
    RW_TAC std_ss [Card1_def]
   );

val Card1_SUC = store_thm (
  "Card1_SUC",
  ``!A n. (Card1 A = SUC n) ==>
          ?(a:'a) B. ~(MEM a B) /\ leq A (a :: B)``,
  Induct THEN SRW_TAC [][] THENL [
    PROVE_TAC [MEM_CONS, leq_trans, leq_sym],
    PROVE_TAC [leq_refl]
  ]);

val MEM_Card1_NOT_0 = store_thm(
  "MEM_Card1_NOT_0",
  ``!A a. MEM (a:'a) A ==> ~(Card1 A = 0)``,
  Induct_on `A` THEN SRW_TAC [][] THEN PROVE_TAC []);

val Card1_CONS_GT_0 = store_thm (
  "Card1_CONS_GT_0",
  ``!A (a:'a). 0 < Card1 (a :: A)``,
  METIS_TAC [MEM, arithmeticTheory.NOT_ZERO_LT_ZERO,
             MEM_Card1_NOT_0]);

val Card1_Delete1 = store_thm(
  "Card1_Delete1",
  ``!A (a:'a).
      Card1 (A Delete1 a) = if MEM a A then Card1 A - 1 else Card1 A``,
  Induct_on `A` THEN SRW_TAC [][MEM_Delete1] THEN SRW_TAC [][] THEN
  PROVE_TAC [MEM_Card1_NOT_0, DECIDE ``~(x = 0) ==> (SUC (x - 1) = x)``]);

val Card1_RSP = store_thm (
  "Card1_RSP",
  ``!A B:'a list. leq A B ==> (Card1 A = Card1 B)``,
  SIMP_TAC (srw_ss()) [leq_def] THEN Induct THEN SRW_TAC [][] THENL [
    PROVE_TAC [],
    `MEM h B /\ ~(Card1 B = 0)` by PROVE_TAC [MEM_Card1_NOT_0] THEN
    Q_TAC SUFF_TAC `Card1 A = Card1 (B Delete1 h)`
          THEN1 SRW_TAC [numSimps.ARITH_ss][Card1_Delete1] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][MEM_Delete1] THEN
    PROVE_TAC []
  ]);

val Card1_0 = store_thm(
  "Card1_0",
  ``!A:'a list. (Card1 A = 0) = (A = [])``,
  Induct_on `A` THEN SRW_TAC [][] THEN PROVE_TAC [NO_MEM_NIL]);

(* list2set *)
val list2set_thm = prove(
  ``(LIST_TO_SET ([]:'a list) = {}) /\
    (!h:'a t. LIST_TO_SET (h::t) = h INSERT LIST_TO_SET t)``,
  SRW_TAC [][pred_setTheory.EXTENSION]);

val list2set_RSP = store_thm(
  "list2set_RSP",
  ``!A B:'a list. leq A B ==> (LIST_TO_SET A = LIST_TO_SET B)``,
  SRW_TAC [][leq_def, pred_setTheory.EXTENSION]);

(* fold *)

val Fold1_def = Define`
  (Fold1 f (z:'b) [] = z) /\
  (Fold1 f z ((a:'a)::A) =
     if (!u v w. f u (f v w) = f v (f u w)) then
       if MEM a A then Fold1 f z A
       else f a (Fold1 f z A)
     else z)
` ;

val MEM_lcommuting_Fold1 = store_thm(
  "MEM_lcommuting_Fold1",
  ``!B f (z:'b) (h:'a).
     (!u v w. f u (f v w) = f v (f u w)) /\ MEM h B ==>
     (Fold1 f z B = f h (Fold1 f z (B Delete1 h)))``,
  Induct_on `B` THEN SRW_TAC [][Fold1_def, MEM_Delete1] THENL [
    PROVE_TAC [],
    PROVE_TAC [NOT_MEM_Delete1_IDENT],
    PROVE_TAC []
  ]);

val Fold1_RSP = store_thm(
  "Fold1_RSP",
  ``!A B:'a list f (z:'b). leq A B ==> (Fold1 f z A = Fold1 f z B)``,
  REWRITE_TAC [leq_def] THEN Induct THEN SRW_TAC [][Fold1_def] THENL [
    PROVE_TAC [],
    `MEM h B` by PROVE_TAC [] THEN
    `Fold1 f z B = f h (Fold1 f z (B Delete1 h))`
       by PROVE_TAC [MEM_lcommuting_Fold1] THEN
    SRW_TAC [][] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][MEM_Delete1] THEN
    PROVE_TAC [],
    Cases_on `B` THEN SRW_TAC [][Fold1_def]
  ]);

val APPEND_RSP = store_thm(
  "APPEND_RSP",
  ``!A1 A2 B1 B2:'a list. leq A1 A2 /\ leq B1 B2 ==>
                          leq (APPEND A1 B1) (APPEND A2 B2)``,
  SRW_TAC [][leq_def]);

val Inter1_def = Define
   `($Inter1 ([]) B = [])  /\
    ($Inter1 ((a:'a) :: A) B = if MEM a B then a :: ($Inter1 A B)
                                          else $Inter1 A B)`;

val _ = add_infix ("Inter1", 600, HOLgrammars.LEFT);

Theorem MEM_Inter1:
   !A B (x:'a). MEM x (A Inter1 B) <=> MEM x A /\ MEM x B
Proof
    Induct
    THEN SRW_TAC [][Inter1_def]
    THEN PROVE_TAC []
QED

val Inter1_RSP = store_thm
   ("Inter1_RSP",
    ``!A1 A2 B1 B2:'a list.
           leq A1 A2 /\ leq B1 B2 ==>
           leq (A1 Inter1 B1) (A2 Inter1 B2)``,
    SRW_TAC [][leq_def, MEM_Inter1]);

(* do the quotient *)
val leq_equiv = save_thm("leq_equiv",
    refl_sym_trans_equiv leq_refl leq_sym leq_trans);

val equivs = [leq_equiv];


val fnlist =
    [{def_name="Empty_def",
      fname="Empty",
      func= ``[] :'a list``,
      fixity=NONE},

     {def_name="Insert_def",
      fname="Insert",
      func= ``CONS :'a -> 'a list -> 'a list``,
      fixity=SOME(Infixr 490)},

(* if desired, a membership constant for finite sets can be defined in
   terms of fset2set:

     fmem x s = x ∈ fset2set s                        (UOK)

   Alternatively, fmem could just be overloaded to a term of this form, as
   is done in the finite_set version of this example.

   The following doesn't work because MEM is not a constant (since f42df6bf5)

     {def_name="In_def",
      fname="In",
      func= ``MEM :'a -> 'a list -> bool``,
      fixity=SOME(Infix(NONASSOC,425))},
*)

     {def_name="Card_def",
      fname="Card",
      func= ``Card1 :'a list -> num``,
      fixity=NONE},

     {def_name="Delete_def",
      fname="Delete",
      func= ``$Delete1 :'a list -> 'a -> 'a list``,
      fixity=SOME(Infixl 500)},

     {def_name="Union_def",
      fname="Union",
      func= ``APPEND :'a list -> 'a list -> 'a list``,
      fixity=SOME(Infixl 500)},

     {def_name="Inter_def",
      fname="Inter",
      func= ``$Inter1 :'a list -> 'a list -> 'a list``,
      fixity=SOME(Infixl 600)},

     {def_name="Fold_def",
      fname="Fold",
      func= ``Fold1 :('a -> 'b -> 'b) -> 'b -> 'a list -> 'b``,
      fixity=NONE},

     {def_name="fset2set_def",
      fname="fset2set",
      func= ``LIST_TO_SET :'a list -> 'a -> bool``,
      fixity=NONE}
    ];


(* ==================================================== *)
(*   LIFT TYPES, CONSTANTS, AND THEOREMS BY QUOTIENTS   *)
(* ==================================================== *)

val _ = quotient.chatting := true;   (* Causes display of quotient as built *)


val  [finite_set_cases, Insert_LEFT_COMM, Insert_LEFT_IDEM,
      In, NONE_In_Empty, In_Insert, finite_set_strong_cases,
      Card, NOT_In_Card, Card_SUC, Card_Insert_GT_0,
      In_Card_NOT_0, NOT_Empty_Insert,
      Delete_def, In_Delete, Card_Delete,
      Insert_Delete, In_Insert_Delete, finite_set_Delete_cases,
      Union, In_Union, Inter, In_Inter,
      Fold, fset2set, finite_set_EXTENSION, finite_set_INDUCT
     ] =

    define_quotient_types

    {types = [{name = "finite_set", equiv = leq_equiv}],
     defs = fnlist,
     tyop_equivs = [],
     tyop_quotients = [FUN_QUOTIENT],
     tyop_simps = [FUN_REL_EQ, FUN_MAP_I],
     respects = [NIL_RSP, CONS_RSP, Card1_RSP, Delete1_RSP,
                 APPEND_RSP, Inter1_RSP, Fold1_RSP, list2set_RSP],
     poly_preserves = [FORALL_PRS, EXISTS_PRS, COND_PRS],
     poly_respects = [RES_FORALL_RSP, RES_EXISTS_RSP, COND_RSP],
     old_thms = [list_CASES, CONS_LEFT_COMM, CONS_LEFT_IDEM,
                 MEM, NONE_MEM_NIL, MEM_CONS, finite_set1_strong_cases,
                 Card1_def, NOT_MEM_Card1, Card1_SUC, Card1_CONS_GT_0,
                 MEM_Card1_NOT_0, NOT_NIL_EQUIV_CONS,
                 Delete1_def, MEM_Delete1, Card1_Delete1,
                 CONS_Delete1, MEM_CONS_Delete1, finite_set1_Delete1_cases,
                 APPEND, MEM_APPEND, Inter1_def, MEM_Inter1,
                 Fold1_def, list2set_thm, leq_def, list_INDUCT]
   };

val _ = map save_thm
    [("finite_set_cases",finite_set_cases),
     ("Insert_LEFT_COMM",Insert_LEFT_COMM),
     ("Insert_LEFT_IDEM",Insert_LEFT_IDEM),
     ("In",In),
     ("NONE_In_Empty",NONE_In_Empty),
     ("In_Insert",In_Insert),
     ("finite_set_strong_cases",finite_set_strong_cases),
     ("Card",Card),
     ("NOT_In_Card",NOT_In_Card),
     ("Card_SUC",Card_SUC),
     ("Card_Insert_GT_0",Card_Insert_GT_0),
     ("In_Card_NOT_0",In_Card_NOT_0),
     ("NOT_Empty_Insert",NOT_Empty_Insert),
     ("In_Delete",In_Delete),
     ("Card_Delete",Card_Delete),
     ("Insert_Delete",Insert_Delete),
     ("In_Insert_Delete",In_Insert_Delete),
     ("finite_set_Delete_cases",finite_set_Delete_cases),
     ("Union",Union),
     ("In_Union",In_Union),
     ("Inter",Inter),
     ("In_Inter",In_Inter),
     ("Fold",Fold),
     ("fset2set",fset2set),
     ("finite_set_EXTENSION",finite_set_EXTENSION),
     ("finite_set_INDUCT",finite_set_INDUCT)
    ];

val _ = export_theory();

val _ = html_theory "ext_finite_set";
