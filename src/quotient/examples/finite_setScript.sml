Theory finite_set
Ancestors
  list pred_set
Libs
  ind_rel quotientLib

(* ------------------------------------------------------------------------ *)
(* Representing finite sets as a new datatype in the HOL logic.             *)
(*                                                                          *)
(* This is a demonstration of how to use the higher order quotient package  *)
(* to construct the type of finite sets, modeled as a quotient of lists.    *)
(* ------------------------------------------------------------------------ *)


(* In interactive sessions, do:

app load ["listTheory",
          "pred_setTheory",
          "ind_rel",
          "bossLib",
          "quotientLib"];

*)

val REWRITE_THM = fn th => REWRITE_TAC[th];


(* --------------------------------------------------------------------- *)
(* Section 1, The Concrete Datatype and the Equivalence Relation.        *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Use finite lists for the free algebra of {{},INSERT} finite sets.     *)
(* --------------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Definition of equivalence between lists as finite sets.               *)
(* This uses Myra VanInwegen's mutually recursive rule induction pkg.    *)
(* See ind_rel.sig and ind_rel.sml.                                      *)
(* --------------------------------------------------------------------- *)


val fsequiv = “fsequiv: 'a list -> 'a list -> bool”;

val fsequiv_patterns = [“^fsequiv S1 S2”];

val fsequiv_rules_tm =
“


       (* ------------------------------------------------------ *)
               (^fsequiv (a :: (b :: A)) (b :: (a :: A)))               /\


       (* ------------------------------------------------------ *)
                  (^fsequiv (a :: (a :: A)) (a :: A))                   /\



       (* ------------------------------------------------------ *)
                           (^fsequiv [] [])                             /\


                           ((^fsequiv A B)
       (* ------------------------------------------------------ *) ==>
                     (^fsequiv (a :: A) (a :: B)))                      /\


                           ((^fsequiv A B)
       (* ------------------------------------------------------ *) ==>
                            (^fsequiv B A))                             /\


                    ((^fsequiv A B) /\ (^fsequiv B C)
       (* ------------------------------------------------------ *) ==>
                            (^fsequiv A C))

”;

val (fsequiv_rules_sat,fsequiv_ind_thm) =
    define_inductive_relations fsequiv_patterns fsequiv_rules_tm;

val fsequiv_inv_thms = prove_inversion_theorems
    fsequiv_rules_sat fsequiv_ind_thm;

val fsequiv_strong_ind = prove_strong_induction
    fsequiv_rules_sat fsequiv_ind_thm;

val _ = overload_on("==", ``fsequiv:'a list -> 'a list -> bool``);
val _ = add_infix ("==", 425, HOLgrammars.NONASSOC);

Theorem fsequiv_rules_sat = fsequiv_rules_sat;
Theorem fsequiv_ind_thm = fsequiv_ind_thm;
Theorem fsequiv_inv_thms = LIST_CONJ fsequiv_inv_thms;
Theorem fsequiv_strong_ind = fsequiv_strong_ind;


val [CONS_LEFT_COMM, CONS_LEFT_IDEM, NIL_RSP, CONS_RSP, fset_SYM', fset_TRANS']
    = CONJUNCTS fsequiv_rules_sat;


(* The finite set equivalence relation is reflexive, symmetric and transitive.*)

Theorem fset_REFL:
      !X:'a list. X == X
Proof
    Induct
    THEN RW_TAC std_ss [fsequiv_rules_sat]
QED

Theorem fset_SYM:
      !X Y:'a list.
           X == Y ==> Y == X
Proof
    REWRITE_TAC [fset_SYM']
QED

Theorem fset_TRANS:
      !X Y Z:'a list.
           X == Y /\ Y == Z ==> X == Z
Proof
    PROVE_TAC [fset_TRANS']
QED

Theorem fset_NIL:
      !A B:'a list.
           A == B ==> ((A = []) = (B = []))
Proof
    rule_induct fsequiv_ind_thm
    THEN REPEAT STRIP_TAC
    THEN RW_TAC list_ss []
QED



(* --------------------------------------------------------------------- *)
(* Section 2, Functions on the Free Algebra.                             *)
(*                                                                       *)
(* We either use as predefined, or define new here, the following        *)
(* functions:                                                            *)
(*                                                                       *)
(*     MEM       test of membership of an element in a list              *)
(*     Card1     number of distinct elements in a list                   *)
(*     Delete1   delete all instances of an element from a list          *)
(*     APPEND    concatenate two lists                                   *)
(*     Inter1    intersection of two lists                               *)
(*     Fold1     computes the fold of a function on a list               *)
(*     list2set  conversion of a list into a set                         *)
(*                                                                       *)
(* For each such function its respectfulness theorem is proven.          *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* The membership function to test if an element is a member of a list   *)
(* is predefined in the list library as MEM:                             *)
(*                                                                       *)
(*    |- (!x. MEM x [] = F) /\                                           *)
(*       (!x h t. MEM x (h::t) = (x = h) \/ MEM x t)                     *)
(* --------------------------------------------------------------------- *)

val _ = overload_on("MEM", ``MEM :'a -> 'a list -> bool``);

Theorem MEM_RSP1:
      !X Y. X == Y ==> (!x:'a. MEM x X = MEM x Y)
Proof
    rule_induct fsequiv_ind_thm
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss [MEM]
    THEN PROVE_TAC []
QED

Theorem MEM_RSP:
      !X Y (x:'a). X == Y ==> (MEM x X = MEM x Y)
Proof
    PROVE_TAC [MEM_RSP1]
QED

Theorem NO_MEM_NIL:
      !A. (!a:'a. ~(MEM a A)) = (A = [])
Proof
    Induct
    THEN RW_TAC std_ss [MEM]
    THEN PROVE_TAC [fsequiv_rules_sat]
QED

Theorem NONE_MEM_NIL:
      !A. (!a:'a. ~(MEM a A)) = (A == [])
Proof
    REWRITE_TAC [NO_MEM_NIL]
    THEN PROVE_TAC [fsequiv_rules_sat,fset_NIL]
QED

Theorem MEM_CONS:
      !A (a:'a). MEM a A ==> (a :: A) == A
Proof
    Induct
    THEN RW_TAC std_ss [MEM]
    THEN PROVE_TAC [fsequiv_rules_sat]
QED

Theorem finite_set1_strong_cases:
      !X. (X = []) \/ ?(a:'a) Y. ~(MEM a Y) /\ X == (a :: Y)
Proof
    Induct
    THEN PROVE_TAC [MEM,MEM_CONS,fsequiv_rules_sat]
QED

(* --------------------------------------------------------------------- *)
(* Definition of Card function to measure the size of a finite set.      *)
(* --------------------------------------------------------------------- *)

Definition Card1_def:
    (Card1 ([]) = 0)  /\
    (Card1 ((a:'a) :: A) = if MEM a A then Card1 A else SUC (Card1 A))
End

Theorem Card1_RSP:
      !A B:'a list. A == B ==> (Card1 A = Card1 B)
Proof
    rule_induct fsequiv_strong_ind
    THEN REPEAT STRIP_TAC
    THEN RW_TAC arith_ss [Card1_def,MEM]
    THEN PROVE_TAC [MEM_RSP]
QED

Theorem Card1_0:
      !A:'a list. (Card1 A = 0) = (A = [])
Proof
    Induct
    THEN RW_TAC std_ss [Card1_def]
    THEN PROVE_TAC[NO_MEM_NIL]
QED

Theorem NOT_MEM_Card1:
      !A:'a list a. ~(MEM a A) ==>
             (Card1 (a :: A) = SUC (Card1 A))
Proof
    RW_TAC std_ss [Card1_def]
QED

Theorem Card1_SUC:
      !A n. (Card1 A = SUC n) ==>
          (?(a:'a) B. ~(MEM a B) /\ A == (a :: B))
Proof
    Induct
    THEN RW_TAC std_ss [Card1_def]
    THENL
      [ PROVE_TAC[MEM_CONS,fsequiv_rules_sat],

        PROVE_TAC[fset_REFL]
      ]
QED

Theorem Card1_CONS_GT_0:
      !A (a:'a).
          0 < Card1 (a :: A)
Proof
    Induct
    THEN RW_TAC arith_ss [MEM,Card1_def]
    THEN PROVE_TAC[MEM_CONS,Card1_RSP]
QED

Theorem MEM_Card1_NOT_0:
      !A (a:'a).
         MEM a A ==> ~(Card1 A = 0)
Proof
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN IMP_RES_TAC MEM_CONS
    THEN IMP_RES_TAC Card1_RSP
    THEN PROVE_TAC [Card1_CONS_GT_0,prim_recTheory.LESS_NOT_EQ]
QED

Theorem Card1_SUC_MEM:
      !A. (Card1 A = SUC n) ==> ?a:'a. MEM a A
Proof
    Cases
    THEN PROVE_TAC [Card1_def,MEM,numTheory.NOT_SUC]
QED

Theorem NOT_NIL_EQUIV_CONS:
      !A (a:'a).
           ~([] == a :: A)
Proof
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN MP_TAC Card1_RSP
    THEN RW_TAC arith_ss [Card1_def]
    THEN IMP_RES_THEN (ACCEPT_TAC o GSYM) MEM_Card1_NOT_0
QED

(* --------------------------------------------------------------------- *)
(* Definition of function to delete an element from a finite set;        *)
(* if the element is not a member then the set is unchanged.             *)
(* --------------------------------------------------------------------- *)

Definition Delete1_def:
    ($Delete1 ([]) x = [])  /\
    ($Delete1 ((a:'a) :: A) x = if a = x then $Delete1 A x
                                     else a :: ($Delete1 A x))
End

val _ = add_infix ("Delete1", 500, HOLgrammars.LEFT);

Theorem MEM_Delete1:
      !A (a:'a) x.
         (MEM x (A Delete1 a)) = ((MEM x A) /\ ~(x = a))
Proof
    Induct
    THEN RW_TAC std_ss [MEM,Delete1_def]
    THEN PROVE_TAC []
QED

Theorem MEM_Delete1_IDENT:
      !A (a:'a).
         ~(MEM a (A Delete1 a))
Proof
    REWRITE_TAC [MEM_Delete1]
QED

Theorem Card1_Delete1:
      !A (a:'a).
         (Card1 (A Delete1 a) = if MEM a A then Card1 A - 1 else Card1 A)
Proof
    Induct
    THEN RW_TAC arith_ss [MEM, Card1_def, Delete1_def, MEM_Delete1]
    THEN PROVE_TAC [MEM_Card1_NOT_0,
                    numLib.ARITH_PROVE ``~(n = 0) ==> (SUC (n - 1) = n)``]
QED

Theorem CONS_Delete1:
      !A (a:'a).
         (a :: (A Delete1 a)) ==
                  (if MEM a A then A else a :: A)
Proof
    Induct
    THEN RW_TAC std_ss [MEM, Delete1_def]
    THEN PROVE_TAC [MEM, Delete1_def, fsequiv_rules_sat]
QED

Theorem MEM_CONS_Delete1:
      !A (a:'a). MEM a A ==>
         (a :: (A Delete1 a)) == A
Proof
    PROVE_TAC [CONS_Delete1]
QED

Theorem finite_set1_Delete1_cases1:
      !X. (X = []) \/ ?a:'a. X == a :: (X Delete1 a)
Proof
    Induct
    THEN PROVE_TAC [Delete1_def,CONS_Delete1,fsequiv_rules_sat]
QED

Theorem finite_set1_Delete1_cases:
      !X. (X = []) \/
            ?a:'a. MEM a X /\ X == a :: (X Delete1 a)
Proof
    PROVE_TAC[finite_set1_Delete1_cases1,MEM,MEM_RSP]
QED

(* The following theorem is the most critical and difficult theorem. *)

Theorem list_EXTENSION1:
      !n A B.
         (Card1 A = n) /\
         (!x:'a. MEM x A = MEM x B) ==>
         A == B
Proof
    Induct
    THEN REPEAT GEN_TAC
    THENL
      [ PROVE_TAC [NO_MEM_NIL,MEM_Card1_NOT_0,fset_REFL],

        STRIP_TAC
        THEN IMP_RES_TAC Card1_SUC_MEM  (* Chooses element "a" of list "A" *)
        THEN FIRST_ASSUM (C UNDISCH_THEN (MP_TAC o
                  SPECL[``A Delete1 (a:'a)``,``B Delete1 (a:'a)``]) o concl)
        THEN RW_TAC arith_ss [Card1_Delete1,MEM_Delete1]
        THEN POP_ASSUM (ASSUME_TAC o SPEC ``a:'a`` o MATCH_MP CONS_RSP)
        THEN PROVE_TAC[MEM_CONS_Delete1,fset_SYM,fset_TRANS]
      ]
QED

Theorem list_EXTENSION:
  !A B. A == B <=> (!a:'a. MEM a A = MEM a B)
Proof PROVE_TAC[MEM_RSP,list_EXTENSION1]
QED

Theorem Delete1_RSP:
      !A B (a:'a). A == B ==>
                     A Delete1 a == B Delete1 a
Proof
    REWRITE_TAC [list_EXTENSION]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC [MEM_Delete1]
QED

Theorem APPEND_RSP:
      !A1 A2 B1 B2:'a list.
           A1 == A2 /\ B1 == B2 ==>
           APPEND A1 B1 == APPEND A2 B2
Proof
    REWRITE_TAC[list_EXTENSION]
    THEN REPEAT STRIP_TAC
    THEN RW_TAC list_ss []
QED

Definition Inter1_def:
    ($Inter1 ([]) B = [])  /\
    ($Inter1 ((a:'a) :: A) B = if MEM a B then a :: ($Inter1 A B)
                                          else $Inter1 A B)
End

val _ = add_infix ("Inter1", 600, HOLgrammars.LEFT);

Theorem MEM_Inter1:
  !A B (x:'a).
           MEM x (A Inter1 B) <=> MEM x A /\ MEM x B
Proof
    Induct
    THEN RW_TAC list_ss [Inter1_def]
    THEN PROVE_TAC []
QED

Theorem Inter1_RSP:
      !A1 A2 B1 B2:'a list.
           A1 == A2 /\ B1 == B2 ==>
           A1 Inter1 B1 == A2 Inter1 B2
Proof
    REWRITE_TAC[list_EXTENSION]
    THEN REPEAT STRIP_TAC
    THEN RW_TAC list_ss [Inter1_def,MEM_Inter1]
QED

(* --------------------------------------------------------------------- *)
(* Definition of Fold1 function to fold a function over a finite set.    *)
(* --------------------------------------------------------------------- *)

Definition Fold1_def:
    (Fold1 f (g:'a->'b) (z:'b) ([]) = z)  /\
    (Fold1 f g z (a :: A) =
        if (!u v. f u v = f v u) /\
           (!u v w. f u (f v w) = f (f u v) w)
        then
           if MEM a A then Fold1 f g z A
                      else f (g a) (Fold1 f g z A)
        else z)
End

(* Respectfulness theorem for the Fold1 function. *)

Theorem Fold1_RSP:
      !f (g:'a->'b) z A B. A == B ==>
          (Fold1 f g z A = Fold1 f g z B)
Proof
    GEN_TAC THEN GEN_TAC THEN GEN_TAC
    THEN rule_induct fsequiv_strong_ind
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC [Fold1_def]
    THEN TRY COND_CASES_TAC
    THEN PROVE_TAC[MEM,list_EXTENSION]
QED

(* --------------------------------------------------------------------- *)
(* Definition of list2set function to convert a list to a set.           *)
(* --------------------------------------------------------------------- *)

(* Respectfulness theorem for the list2set function. *)
val _ = temp_overload_on("list2set", ``LIST_TO_SET``)
Theorem list2set_RSP:
      !X Y:'a list. X == Y ==>
          (list2set X = list2set Y)
Proof
    rule_induct fsequiv_ind_thm
    THEN REPEAT STRIP_TAC
    THEN SRW_TAC [] [INSERT_COMM,INSERT_INSERT]
QED


(* --------------------------------------------------------------------- *)
(* Section 3, Lifting the finite set type and its constants.             *)
(*                                                                       *)
(* We first set up the parameters for the call to the tool, including    *)
(* the equivalence relation on which the quotient is based, and the      *)
(* list of constants to be lifted, with their new names and fixities.    *)
(* --------------------------------------------------------------------- *)


Theorem fset_EQUIV =
    refl_sym_trans_equiv fset_REFL fset_SYM fset_TRANS;

val equivs = [fset_EQUIV];

val fnlist =
    [{def_name="Empty_def",
      fname="Empty",
      func= ``[] :'a list``,
      fixity=NONE},

     {def_name="Insert_def",
      fname="Insert",
      func= ``CONS :'a -> 'a list -> 'a list``,
      fixity=SOME(Infixr 490)},

(*
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
      func= ``Fold1 :('b -> 'b -> 'b) -> ('a -> 'b) -> 'b -> 'a list -> 'b``,
      fixity=NONE},

     {def_name="fset2set_def",
      fname="fset2set",
      func= ``list2set :'a list -> 'a -> bool``,
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

    {types = [{name = "finite_set", equiv = fset_EQUIV}],
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
                 Fold1_def, LIST_TO_SET, list_EXTENSION, list_INDUCT]
   };





(* ---------------------------------------------------------------- *)
(* Save the theorems lifted by the quotient operations.             *)
(* ---------------------------------------------------------------- *)

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

(* Notice the important induction theorem for the quotient type:

finite_set_INDUCT
  |- !P. P Empty /\ (!f. P f ==> !a. P (a Insert f)) ==> !f. P f

This is a higher-order theorem, which needs higher-order quotients
to lift.  It is also interesting in that it is by this theorem
an inductive type which was not defined inductively.
*)


(* ---------------------------------------------------------------- *)
(*      End of saving important theorems from lifting.              *)
(* ---------------------------------------------------------------- *)


(* --------------------------------------------------------------------- *)
(* Section 4, Exploitation of the new lifted type of finite sets.        *)
(*                                                                       *)
(* The rest of these proofs are achieved purely through reasoning at the *)
(* higher, quotient level.  There is never again any need to deal with   *)
(* concepts at the lower level, which may now be completely forgotten.   *)
(* --------------------------------------------------------------------- *)

(* Prove that the cardinality of a set may be expressed using Fold.      *)

Theorem Card_Fold:
      Card = Fold $+ ((K 1):'a->num) 0
Proof
    CONV_TAC FUN_EQ_CONV
    THEN HO_MATCH_MP_TAC finite_set_INDUCT
    THEN REPEAT STRIP_TAC
    THEN RW_TAC arith_ss [Fold,Card]
QED

val _ = overload_on("In", ``\e s. e IN fset2set s``);
val _ = set_fixity "In" (Infix(NONASSOC, 425))

(* --------------------------------------------------------------------- *)
(* Proof of stronger finite set induction principle.                     *)
(* --------------------------------------------------------------------- *)

Theorem finite_set_strong_induction:
      !P. P Empty /\
            (!A. P A ==> !a:'a. ~(a In A) ==> P (a Insert A))
            ==> !A. P A
Proof
    GEN_TAC THEN STRIP_TAC
    THEN HO_MATCH_MP_TAC finite_set_INDUCT
    THEN PROVE_TAC [In_Insert]
QED

Theorem fset2set_11:
      !A B:'a finite_set. (fset2set A = fset2set B) = (A = B)
Proof
    REWRITE_TAC[finite_set_EXTENSION,EXTENSION]
QED

Theorem fset2set_FINITE:
      !A:'a finite_set. FINITE (fset2set A)
Proof
    HO_MATCH_MP_TAC finite_set_INDUCT
    THEN REPEAT STRIP_TAC
    THEN RW_TAC (std_ss ++ pred_setLib.PRED_SET_ss) [fset2set]
QED

Theorem fset2set_ONTO_FINITE:
      !s. FINITE s ==> ?A:'a finite_set. fset2set A = s
Proof
    REWRITE_TAC[FINITE_DEF]
    THEN GEN_TAC
    THEN DISCH_THEN HO_MATCH_MP_TAC
    THEN REPEAT STRIP_TAC
    THEN PROVE_TAC[fset2set]
QED

(* So fset2set is a bijection between finite_set and finite pred_sets. *)

val set2fset_def =
    new_specification("set2fset_def",["set2fset"],
         CONV_RULE (DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)
             fset2set_ONTO_FINITE);

(*  |- !s. FINITE s ==> (fset2set (set2fset s) = s)      *)

Theorem set2fset_fset2set:
      !A:'a finite_set. set2fset (fset2set A) = A
Proof
    GEN_TAC
    THEN MP_TAC (MATCH_MP set2fset_def (SPEC_ALL fset2set_FINITE))
    THEN REWRITE_TAC[fset2set_11]
QED



(* ===================================================================== *)
(* End of the lifting of finite set types and definitions to the higher, *)
(* more abstract level, where equivalent expressions are actually equal. *)
(* ===================================================================== *)




val _ = print_theory_to_file "-" "finite_set.lst";

val _ = html_theory "finite_set";

fun print_theory_size () =
   (print "The theory ";
    print (current_theory ());
    print " has ";
    print (Int.toString (length (types (current_theory ()))));
    print " types, ";
    print (Int.toString (length (axioms "-")));
    print " axioms, ";
    print (Int.toString (length (definitions "-")));
    print " definitions, and ";
    print (Int.toString (length (theorems "-")));
    print " theorems.";
    print "\n" );

val _ = print_theory_size();
