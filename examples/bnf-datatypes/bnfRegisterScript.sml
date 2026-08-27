Theory bnfRegister
Ancestors
  bnfInitial pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib bnfFixLib testutils

(* ----------------------------------------------------------------------
    Turning a type the package defined back into a BNF.

    This is what nested recursion needs: once ‘mylist’ is in the
    database, a later datatype can recurse through it.  The map and set
    functions come straight off the recursion principle the package
    produced, and the four laws by induction over the new type — the
    same theorems every registered functor is stored with.
   ---------------------------------------------------------------------- *)

val db = bnfBase.fullDB()
val bnf = deriveBNF db “:one + 'b1 # 'a”
val fix = defineFixpoint {tyname = "mylist", ABS = "mylist_ABS",
                          REP = "mylist_REP"} bnf
val cs = defineConstructors ["MyNil", "MyCons"] bnf fix

Theorem mylist_axiom = #existential_axiom cs
Theorem mylist_induction = valOf (#induction cs)
Theorem MyCons_11 = valOf (List.last (#one_one cs))
Theorem mylist_distinct = valOf (hd (#distinct cs))

val mylistMAP_def = Prim_rec.new_recursive_definition {
  name = "mylistMAP_def", rec_axiom = mylist_axiom,
  def = “(mylistMAP f MyNil = MyNil) ∧
         (mylistMAP f (MyCons a l) = MyCons (f a) (mylistMAP f l))”}

val mylistSET_def = Prim_rec.new_recursive_definition {
  name = "mylistSET_def", rec_axiom = mylist_axiom,
  def = “(mylistSET MyNil = ∅) ∧
         (mylistSET (MyCons a l) = a INSERT mylistSET l)”}

val _ = export_rewrites ["mylistMAP_def", "mylistSET_def"]

Theorem mylistMAP_ID:
  mylistMAP I = I
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac mylist_induction >> simp[]
QED

Theorem mylistMAP_O:
  mylistMAP (f:'c -> 'd) o mylistMAP (g:'b -> 'c) = mylistMAP (f o g)
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac mylist_induction >> simp[]
QED

Theorem mylistMAPIMAGE:
  ∀f l. mylistSET (mylistMAP f l) = IMAGE f (mylistSET l)
Proof
  gen_tac >> ho_match_mp_tac mylist_induction >> simp[]
QED

Theorem mylistMAPCONG:
  ∀f g l. (∀a. a ∈ mylistSET l ⇒ f a = g a) ⇒
          mylistMAP f l = mylistMAP g l
Proof
  ntac 2 gen_tac >> ho_match_mp_tac mylist_induction >> simp[] >>
  rpt strip_tac >> gs[]
QED

(* the elements of a list form a finite, hence countable, set *)
Theorem mylistSET_FINITE[simp]:
  ∀l. FINITE (mylistSET l)
Proof
  ho_match_mp_tac mylist_induction >> simp[]
QED

Theorem mylist_bnd:
  ∀l. mylistSET l ≼ 𝕌(:num)
Proof
  gen_tac >> irule cardinalTheory.FINITE_CLE_INFINITE >> simp[]
QED

(* MyNil's element type has to be pinned to the witness's argument: on
   its own it is a free type variable, and the database rejects that *)
Theorem mylist_wit:
  ∀a:'a1. mylistSET ((K MyNil : 'a1 -> 'a1 mylist) a) = ∅
Proof
  simp[]
QED

(* and stated at the canonical type variable, since the database checks
   the theorem's variables against the term it is stored with *)
Theorem mylist_inh:
  ∀v:'a1. v ∈ mylistSET ((flip MyCons MyNil : 'a1 -> 'a1 mylist) v)
Proof
  simp[combinTheory.C_DEF]
QED

(* the relator; the database stores one for every functor, though the
   derivation of composites doesn't consume it *)
val mylistREL_def = Prim_rec.new_recursive_definition {
  name = "mylistREL_def", rec_axiom = mylist_axiom,
  def = “(mylistREL R MyNil m ⇔ (m = MyNil)) ∧
         (mylistREL R (MyCons a l) m ⇔
            ∃b u. m = MyCons b u ∧ R a b ∧ mylistREL R l u)”}

(* ----------------------------------------------------------------------
    the registration itself
   ---------------------------------------------------------------------- *)

fun rnm s : KernelSig.kernelname = {Thy = "bnfRegister", Name = s}

val _ = bnfBase.updateDB (
  {Thy = "bnfRegister", Name = "mylist"},
  bnfBase.bI {
    bnd = “univ(:num)”,
    bndthms = [rnm "mylist_bnd"],
    canontype = “:'a1 mylist”,

    map = “mylistMAP : ('a1 -> 'c1) -> 'a1 mylist -> 'c1 mylist”,
    mapID = rnm "mylistMAP_ID",
    mapO = rnm "mylistMAP_O",
    mapIMAGE = [rnm "mylistMAPIMAGE"],
    mapCONG = rnm "mylistMAPCONG",

    relator = “mylistREL : ('a1 -> 'c1 -> bool) ->
                           'a1 mylist -> 'c1 mylist -> bool”,
    set = [“mylistSET : 'a1 mylist -> 'a1 set”],
    siblings = [],

    wits = [(“K MyNil : 'a1 -> 'a1 mylist”, rnm "mylist_wit")],
    inhabits = [(“flip MyCons MyNil : 'a1 -> 'a1 mylist”, rnm "mylist_inh")]
  }
)

(* ----------------------------------------------------------------------
    and now a functor may recurse through it
   ---------------------------------------------------------------------- *)

val nested = deriveBNF (bnfBase.fullDB()) “:one + 'b1 # 'a mylist”

val _ = tprint "deriving a functor that recurses under mylist"
val _ = if List.all (null o hyp)
                    [#mapID nested, #mapO nested, #mapIMAGE nested,
                     #mapCONG nested, #bndthm nested]
        then OK() else die "hypotheses left"

(* the whole way: a datatype whose recursion goes under mylist *)
(* rose = RNode of one + 'b1 # rose mylist: the recursion goes under
   mylist, which is itself a type this package defined *)
val rose = defineFixpoint {tyname = "rose", ABS = "rose_ABS", REP = "rose_REP"}
                          nested

Theorem rose_recursion = #recursion rose
Theorem rose_prim_recursion = #prim_recursion rose

val _ = tprint "a datatype recursing under a package-defined type"
val _ =
    if #newty rose = “:'b1 rose” andalso
       null (hyp (#recursion rose)) andalso
       null (free_vars (concl (#recursion rose)))
    then OK() else die (thm_to_string (#recursion rose))

val rcs = defineConstructors ["RLeaf", "RNode"] nested rose
Theorem rose_axiom = #axiom rcs

(* ----------------------------------------------------------------------
    What a function definition over a nested recursion looks like.

    The recursive call arrives as ‘mylistMAP h l’ — the map of the type
    being recursed under — rather than as clauses replaying mylist's own
    recursion through an auxiliary function.  That is the BNF structure
    showing through: the constructor's argument is an F of the type, so
    the function's argument is an F of the results.
   ---------------------------------------------------------------------- *)

fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

val _ = tprint "recursion through the nested map, not replayed clauses"
val _ =
    if same (concl rose_axiom)
            “∀f0 f1. ∃!h. h RLeaf = f0 ∧
                          ∀a0 a1. h (RNode a0 a1) = f1 a0 a1 (mylistMAP h a1)”
    then OK() else die (thm_to_string rose_axiom)

(* The matching induction principle is *not* the one Prim_rec derives —
   it counts recursive arguments by their type, and here the recursive
   results arrived under mylist.  The natural principle is the set-based
   one, with hypothesis "for every sub-term in mylistSET l". *)
val _ = tprint "legacy induction is declined for a nested recursion"
val _ = if not (isSome (#induction rcs)) then OK()
        else die "derived one anyway"


(* ----------------------------------------------------------------------
    Actually defining such a function.

    Prim_rec.new_recursive_definition cannot consume the nested axiom —
    it expects each recursive occurrence to be the function applied to a
    variable, and here it arrives under mylistMAP.  Going through the
    axiom directly is four lines and needs no termination argument:
    instantiate the parameters, take the existence half, and name the
    function.
   ---------------------------------------------------------------------- *)

val mylistSUM_def = Prim_rec.new_recursive_definition {
  name = "mylistSUM_def", rec_axiom = mylist_axiom,
  def = “(mylistSUM MyNil = 0n) ∧
         (mylistSUM (MyCons (n:num) l) = n + mylistSUM l)”}

val rsize_def =
    let val ax = INST_TYPE [alpha |-> numSyntax.num] rose_axiom
        val inst = SPECL [“0n”, “λ(a:'b1) (l:'b1 rose mylist) (r:num mylist).
                                    1 + mylistSUM r”] ax
    in
      new_specification ("rsize_def", ["rsize"],
                         CONV_RULE (DEPTH_CONV BETA_CONV) (EXISTENCE inst))
    end

val _ = tprint "a function whose recursive call is under a map"
val _ =
    (* the point is the shape of the recursive call, so look for it;
       matching rather than aconv, since a freshly parsed rsize gets its
       own name for the type variable *)
    if can (find_term (can (match_term “mylistMAP rsize”))) (concl rsize_def)
       andalso
       can (find_term (can (match_term “rsize RLeaf”))) (concl rsize_def)
       andalso
       null (hyp rsize_def)
    then OK() else die (thm_to_string rsize_def)

val _ = tprint "new_recursive_definition cannot take the nested axiom"
val _ =
    (ignore (Prim_rec.new_recursive_definition {
        name = "rsize2_def", rec_axiom = rose_axiom,
        def = “(rsize2 RLeaf = 0n) ∧
               (rsize2 (RNode a l) = 1 + mylistSUM (mylistMAP rsize2 l))”});
     die "accepted")
    handle HOL_ERR _ => OK()

val _ = tprint "set-based induction, split along the constructors"
val _ =
    if same (concl (#set_induction rcs))
            “∀P. P RLeaf ∧
                 (∀a l. (∀y. y ∈ mylistSET l ⇒ P y) ⇒ P (RNode a l)) ⇒
                 ∀r. P r”
    then OK() else die (thm_to_string (#set_induction rcs))
