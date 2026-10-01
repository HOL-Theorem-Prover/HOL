Theory bnfDatatypeTest
Ancestors
  bnfInitial bnfFixBNF bnfPrelims finite_map list pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib bnfFixLib bnfDatatypeLib
  legacyInduction testutils

(* ----------------------------------------------------------------------
    The package as a user meets it: one call per declaration, and
    everything a datatype is supposed to have afterwards.
   ---------------------------------------------------------------------- *)

fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

fun exists nm = can (DB.fetch "-") nm

(* ----------------------------------------------------------------------
    a recursive type
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `mylist = MNil | MCons 'a mylist`

val _ = tprint "the theorems a declaration saves"
val _ =
    if List.all (fn s => exists ("mylist" ^ s))
                ["_11", "_distinct", "_nchotomy", "_Axiom", "_induction",
                 "_case_cong", "_case_eq"]
    then OK() else die "not all saved"

val _ = tprint "and it behaves like a datatype"
val _ =
    let val th1 = Q.prove (‘MNil ≠ MCons a l ∧
                            (MCons a l = MCons b m ⇔ a = b ∧ l = m)’, simp[])
        val th2 = Q.prove (‘∀l : 'a mylist. l = MNil ∨ ∃a m. l = MCons a m’,
                           Cases >> simp[])
        val th3 = Q.prove (‘(case MCons a l of MNil => 0n | MCons _ _ => 1)
                            = 1’, simp[])
        val th4 = Q.prove (‘∀l : 'a mylist. mylistMAP I l = l’,
                           Induct >> simp[])
        val th5 = Q.prove (‘mylistSET (MCons a l) = a INSERT mylistSET l’,
                           simp[])
    in
      if List.all (null o hyp) [th1, th2, th3, th4, th5] then OK()
      else die "not proved"
    end

(* a definition over it, by the machinery a user would reach for *)
Definition len_def:
  len MNil = 0 ∧ len (MCons a l) = 1 + len l
End

val _ = tprint "a function defined over it by Define"
val _ =
    let val th = Q.prove (‘len (MCons a (MCons b MNil)) = 2’, simp[len_def])
    in
      if null (hyp th) then OK() else die "not proved"
    end

(* ----------------------------------------------------------------------
    a type that recurses through the one just declared, which is what
    registering it as a functor is for
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `rose = RLeaf | RNode 'a (rose mylist)`

val _ = tprint "a type that nests through it"
val _ =
    let val th = Q.prove (‘roseMAP f (RNode a l) =
                             RNode (f a) (mylistMAP (roseMAP f) l) ∧
                           roseSET (RNode a l) =
                             a INSERT BIGUNION (IMAGE roseSET (mylistSET l))’,
                          simp[])
        val (_, szth) = TypeBase.size_of “:'a rose”
    in
      if null (hyp th) andalso
         same (concl szth)
              “(∀f: 'a -> num. rose_size f RLeaf = 0) ∧
               ∀(f: 'a -> num) a l.
                 rose_size f (RNode a l) =
                 1 + (f a +
                      mylist_size (λx. x) (mylistMAP (rose_size f) l))”
      then OK() else die "not as expected"
    end

(* ----------------------------------------------------------------------
    the shapes that do not recurse
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `colour = Red | Green | Blue`

val _ = tprint "an enumeration through the entry point"
val _ =
    let val th1 = Q.prove (‘Red ≠ Green ∧ Green ≠ Blue’, simp[])
        val th2 = Q.prove (‘∀c. c = Red ∨ c = Green ∨ c = Blue’,
                           Cases >> simp[])
    in
      if List.all (null o hyp) [th1, th2] andalso exists "colour_nchotomy"
      then OK() else die "not as expected"
    end

val _ = bnfDatatype `point = <| x : num ; y : num |>`

val _ = tprint "a record through the entry point"
val _ =
    let val th1 = Q.prove (‘(<| x := 3; y := 4 |> : point).y = 4’, simp[])
        val th2 = Q.prove (‘(r : point with x := 1).x = 1’, simp[])
    in
      if List.all (null o hyp) [th1, th2] then OK() else die "not proved"
    end

(* ----------------------------------------------------------------------
    and the names a declaration asks for
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `stack[map=SMAP,set=stack_elems,rel=SREL,size=stack_sz] =
                       Emp | Psh 'a stack`

val _ = tprint "the names a declaration asks for"
val _ =
    let val ns = List.map (#1 o dest_const) (Theory.constants "-")
        fun has s = Lib.mem s ns
        val th = Q.prove (‘stack_elems (Psh a s) = a INSERT stack_elems s’,
                          simp[])
    in
      if List.all has ["SMAP", "stack_elems", "SREL", "stack_sz"] andalso
         not (List.exists has ["stackMAP", "stackSET", "stackREL"]) andalso
         null (hyp th)
      then OK() else die "not as expected"
    end

(* ----------------------------------------------------------------------
    and a family, through the same call
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `t1 = A 'a | B t1 t2 ; t2 = C t3 | D 'a t2 ;
                     t3 = E t1 | F t3`

val _ = tprint "a family through the entry point"
val _ =
    if List.all exists
       ["t1_Axiom", "t1_induction", "t2_Axiom", "t2_nchotomy", "t3_11",
        "t3_case_eq"]
    then OK() else die "not all saved"

val _ = tprint "the family's types and constructors"
val _ =
    let val th1 = Q.prove (‘A a ≠ B t u ∧ (E x = E y ⇔ x = y)’, simp[])
        val th2 = Q.prove (‘t1MAP f (B t u) = B (t1MAP f t) (t2MAP f u)’,
                           simp[])
        val th3 = Q.prove (‘t2SET (D a t) = a INSERT t2SET t’, simp[])
    in
      if List.all (null o hyp) [th1, th2, th3] then OK() else die "not proved"
    end

val _ = tprint "and its induction principle"
val _ =
    let val th =
            Q.prove (‘(∀t : 'a t1. t1MAP I t = t) ∧
                      (∀t : 'a t2. t2MAP I t = t) ∧
                      ∀t : 'a t3. t3MAP I t = t’,
                     ho_match_mp_tac (DB.fetch "-" "t1_induction") >> simp[])
    in
      if null (hyp th) then OK() else die "not proved"
    end

(* ----------------------------------------------------------------------
    a type that recurses under a finite map, which is what fmaptreeTheory
    builds by hand
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `ftree = FTNode 'a ('k |-> ftree)`

val _ = tprint "a type recursing under a finite map"
val _ =
    let val ax = DB.fetch "-" "ftree_Axiom"
        val ind = DB.fetch "-" "ftree_induction"
        val th1 = Q.prove (‘FTNode i1 f1 = FTNode i2 f2 ⇔ i1 = i2 ∧ f1 = f2’,
                           simp[])
        val th2 = Q.prove (‘∀t : ('a,'k) ftree. ∃i fm. t = FTNode i fm’,
                           Cases >> simp[])
    in
      if List.all (null o hyp) [th1, th2] then
        (print ("\n  axiom: " ^ thm_to_string ax ^
                "\n  induction: " ^ thm_to_string ind ^ "\n"); OK())
      else die "not proved"
    end

(* ----------------------------------------------------------------------
    a family that nests pairs of its members two collections deep
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `n1 = N1 (num list) (((n1 # n2) list) list)
                        | N2 ((n1 + n2) list) ;
                     n2 = M1 | M2 (n3 option) ;
                     n3 = P1 | P2 n1 'p 'q`

val _ = tprint "a family nesting pairs of members two deep"
val _ =
    if List.all exists
       ["n1SET1_thm", "n1SET2_thm", "n2SET1_thm", "n2SET2_thm",
        "n3SET1_thm", "n3SET2_thm", "n1MAP_thm"]
    then OK() else die "not all saved"

val _ = tprint "and what its set functions reach"
val _ =
    let val th1 = Q.prove (‘p ∈ n3SET1 (P2 t p q) ∧ q ∈ n3SET2 (P2 t p q)’,
                           simp[])
        val th2 = Q.prove (‘x ∈ n1SET1 t ⇒ x ∈ n3SET1 (P2 t p q)’, simp[])
        (* nothing reaches through an empty collection, which is the
           doubly nested argument saying so *)
        val th3 = Q.prove (‘n1SET1 (N1 l []) = ∅’, simp[])
    in
      if List.all (null o hyp) [th1, th2, th3] then OK() else die "not proved"
    end

(* ----------------------------------------------------------------------
    and the older construction's principle for a type that recurses
    under two operators, which is where their order is visible
   ---------------------------------------------------------------------- *)

val _ = bnfDatatype `zv = VA (zv option) | VB (zv list) | VC (zv option) num`

val _ = tprint "an operator per predicate, in the order first mentioned"
val _ =
    let val ops = [{induction = TypeBase.induction_of “:'a list”,
                    sets = CONJUNCTS listTheory.LIST_TO_SET},
                   {induction = TypeBase.induction_of “:'a option”,
                    sets = CONJUNCTS bnfPrelimsTheory.optSET_def}]
        val th = legacyInduction.mutual_induction
                   ops (TypeBase.induction_of “:zv”)
    in
      (* the option comes first in the specification, so it is Q0, even
         though the list's clauses are what a caller lists first *)
      if same (concl th)
           “∀P Q0 Q1.
              (∀v. Q0 v ⇒ P (VA v)) ∧ (∀l. Q1 l ⇒ P (VB l)) ∧
              (∀v. Q0 v ⇒ ∀n. P (VC v n)) ∧ Q0 NONE ∧
              (∀a. P a ⇒ Q0 (SOME a)) ∧ Q1 [] ∧
              (∀t h. P h ∧ Q1 t ⇒ Q1 (h::t)) ⇒
              (∀v. P v) ∧ (∀l. Q0 l) ∧ ∀l. Q1 l”
      then OK() else die "not the order the specification mentions them"
    end
