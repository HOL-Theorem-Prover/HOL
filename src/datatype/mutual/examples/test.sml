(* File: test.sml *)
load "mutualLib"; open mutualLib;

(*---------------------------------------------------------------------------

   The following examples are originally by Elsa Gunter.  They have been
   rewritten for the "mutual" library. 

     t0 is an example of a simple nesting
     t1 is an example of nesting within nesting of the same type constructor
     t2 is an example of nesting within nesting of the different type
        constructors.
     t3 is an example using the prod type constructor.  Here you have to
        create your own recursion theorem.
     e0 is an example of a fairly typical nesting, with multiple cases.
     e1 is an example with irrelevant recursion theorems supplied.
     e2 is e1 without the irrelevant recursion theorems.
     e3 is an example without any actual nesting at all.
     e4 is an example with polymorphism.
     e5 is an example with constant type folding, polymorphism, 
        and deep nesting.
     e6 is a fairly common example: first order terms

     After that are some other tests.

 ---------------------------------------------------------------------------*)

(* An example of a simple nesting *)

val t0 = Lib.try (define_type [listTheory.list_Axiom])
                 `Alist = mkA of Alist list`;


(* An example of nesting within nesting *)

val t1 = define_type 
      [listTheory.list_Axiom]  `Blist = mkB of Blist list list`;

(* An example of nesting within nesting of the different type constructors. *)

val t2 = define_type
   [listTheory.list_Axiom, 
       sumTheory.sum_Axiom] `sAlist = smk of (sAlist list) + (sAlist list)`;

(* An example with prod *)

val t3 = define_type
  [pairTheory.pair_Axiom] `Aprod = End 
                                 | pmk of Aprod # Aprod`;


(* An example with mutual recursion. *)

val e0 = define_type 
  [listTheory.list_Axiom, 
   pairTheory.pair_Axiom] `state = State of (num # value) list ;
                             env = Env1 of (num # value) list 
                                 | Env2 of (num # value) list ;
                           value = Base of 'a 
                                 | Ind of env 
                                 | Ref of (state # value)`;

(* An example of irrelevant recursor theorems *)

val e1 = define_type
  [listTheory.list_Axiom,
   pairTheory.pair_Axiom,
      sumTheory.sum_Axiom]  `BBlist = mkBB of BBlist list 
                                    | mkBB1 of num`;



(* e1 with the irrelevant theorems removed *)

val e2 = define_type 
   [listTheory.list_Axiom] `BClist = mkBC of BClist list 
                                   | mkBC1 of num`;

(* An example with no actual nesting *)
(* Fails *)

val e3 = define_type [] `AB = mkAB1 of num`;

(* An example with polymorphism *)

val e4 = define_type 
  [listTheory.list_Axiom] `CClist = mkCC of CClist list 
                                  | mkCC1 of 'a`;


(* An example with constant type folding, polymorphism, and deep nesting *)

val e5 = define_type
  [listTheory.list_Axiom,
   pairTheory.pair_Axiom,
      sumTheory.sum_Axiom] 
            `DDty = DNUM of num -> bool list -> 'a -> num
                  | DVAL of (num + bool) list # (EEty list + bool) list ;

             EEty = EVAL of ((DDty list # 'a) list + EEty) list`;


(* A fairly common example: first order terms *)

val e6 = define_type
  [listTheory.list_Axiom] `term = Var of 'a
                                | App of 'b => term list`;


val e7 = define_type 
 [pairTheory.pair_Axiom,
  listTheory.list_Axiom]  `test2 = terminal2 
                                 | nonterminal2 of ('a # test2) list`;


val e8 = define_type [] `toto = empty_test`;
(* Fails *)
val e9 = define_type [] `toto1 = test1 of 'a
                               | test2 of 'b`;

val e10 = define_type []
              `tya = nil_tya
                   | cons_tya of tyb => tya ;

               tyb = contb of 'leftopen => tyc ;

               tyc = conn of 'leftopentoo => tya`;


(* Define case expressions for e10. *)

val case_defs = 
 Lib.try define_mutual_functions
  {name = "case_defs",
   rec_axiom = #New_Ty_Existence_Thm e10,
   fixities = NONE,
   def = Term
     `(a_case (nil_tya:('a,'b)tya)    = 1) /\
      (a_case (cons_tya x y)          = 2) /\
      (b_case (contb x1 y1:('a,'b)tyb) = 3)  /\
      (c_case (conn x2 y2:('a,'b)tyc)  = 4)`};

val case_defs = 
 Lib.try define_mutual_functions
  {name = "case_defs",
   rec_axiom = #New_Ty_Existence_Thm e10,
   fixities = NONE,
   def = Term
     `(a_case (nil_tya:('a,'b)tya) v f   = v) /\
      (a_case (cons_tya x y)       v f   = f x y) /\
      (b_case (contb x1 y1:('a,'b)tyb) g = g x1 y1)  /\
      (c_case (conn x2 y2:('a,'b)tyc)  h = h x2 y2)`};

(* Define a mutually recursive function over e10. *)

val emptyer_DEF = 
 define_mutual_functions
   {name = "emptyer_DEF",
    rec_axiom = #New_Ty_Existence_Thm e10,
    fixities = SOME [Infix 600, Prefix, Prefix],
    def = Term
      `(emptyer nil_tya a = F) 
    /\ (emptyer (cons_tya b a) aa =
          (aa = nil_tya) 
           \/ bemptyer b (a_case ARB (\x y. x) aa)
              /\ emptyer a (a_case ARB (\x y. y) aa))
    /\ (bemptyer (contb x c) b = cemptyer c (b_case (\x y. y) b)) 
    /\ (cemptyer (conn y a) c = emptyer a (c_case (\x y. y) c))`};


(*---------------------------------------------------------------------------
   What this could/should look like with TFL-style pattern matching:

       (emptyer  nil_tya a                     = F) 
    /\ (emptyer  (cons_tya b a) nil_tya        = T)
    /\ (emptyer  (cons_tya b a) (cons_tya c d) = bemptyer b c /\ emptyer a d)
    /\ (bemptyer (contb x c)    (contb y d)    = cemptyer c d) 
    /\ (cemptyer (conn y a)     (conn x d)     = emptyer a d)`

 ---------------------------------------------------------------------------*)


(* The End. *)
