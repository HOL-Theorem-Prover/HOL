Theory bnfShapes
Ancestors
  bnfInitial bnfFixBNF pred_set cardinal
Libs
  HolKernel Parse boolLib bossLib bnfBase bnfLib bnfFixLib testutils

(* ----------------------------------------------------------------------
    The specifications that do not recurse: an enumeration, whose type
    operator takes no arguments at all, and a record, which is one
    constructor of its fields.

    Neither is a functor of the type being defined — there is nothing to
    recurse into — so the functor the specification gives is constant in
    the recursive argument, and the initial-algebra construction does not
    apply to it.  defineCopy is the whole difference: the type is defined
    in bijection with the functor, and from there on this is the same
    path every other datatype takes.
   ---------------------------------------------------------------------- *)

(* the axioms below are stated at a type variable of the driver's own
   choosing, so compare up to renaming rather than by aconv *)
fun same t1 t2 = can (match_term t1) t2 andalso can (match_term t2) t1

val db = bnfBase.fullDB()

(* ----------------------------------------------------------------------
    an enumeration
   ---------------------------------------------------------------------- *)

val espec = parseSpec `colour = Red | Green | Blue`

val _ = tprint "an enumeration's specification"
val _ =
    if #tynames espec = ["colour"] andalso null (#params espec) andalso
       #constructors espec = [["Red", "Green", "Blue"]] andalso
       List.all (fn (ty,_) => ty = “:unit + unit + unit”) (#functors espec)
    then OK() else die "not as expected"

val ebnf = deriveBNFn db [alpha] (#1 (hd (#functors espec)))

val _ = tprint "a constant functor's map and set"
val _ =
    if same (#mkmap ebnf [mk_var("f", alpha --> beta)])
            (inst [alpha |-> “:unit + unit + unit”] combinSyntax.I_tm) andalso
       same (hd (#sets ebnf))
            (combinSyntax.mk_K_1 (pred_setSyntax.mk_empty alpha,
                                  “:unit + unit + unit”))
    then OK() else die "not as expected"

val _ = tprint "and the construction declines it"
val _ =
    if not (can (defineFixpoint {tyname = "colour", ABS = "colour_ABS",
                                 REP = "colour_REP"}) ebnf)
    then OK() else die "the fixpoint construction claimed to work"

val ecopy = defineCopy {tyname = "colour", ABS = "colour_ABS",
                        REP = "colour_REP"} ebnf
val efix = #fixpoint ecopy
val ecs = defineConstructors (hd (#constructors espec)) ebnf efix

val _ = tprint "an enumeration's axiom"
val _ =
    if #newty efix = “:colour” andalso
       List.all (fn t => type_of t = “:colour”) (#constructors ecs) andalso
       same (concl (#axiom ecs))
             “∀f0 f1 f2. ∃!h. h Red = f0 ∧ h Green = f1 ∧ h Blue = f2”
    then OK() else die (thm_to_string (#axiom ecs))

val _ = tprint "an enumeration's induction"
val _ =
    case #induction ecs of
        NONE => die "none derived"
      | SOME th => if same (concl th) “∀P. P Red ∧ P Green ∧ P Blue ⇒ ∀c. P c”
                   then OK() else die (thm_to_string th)

val _ = TypeBase.export
          (typeBaseInfo {axiom = #axiom ecs,
                         induction = valOf (#induction ecs),
                         case_defs = defineCases (#existential_axiom ecs),
                         rewrites = [[]], names = [noNames]})

val _ = tprint "an enumeration in TypeBase"
val _ =
    let val th1 = Q.prove (‘Red ≠ Green ∧ Red ≠ Blue ∧ Green ≠ Blue’, simp[])
        val th2 = Q.prove (‘∀c. c = Red ∨ c = Green ∨ c = Blue’,
                           Cases_on ‘c’ >> simp[])
        val th3 = Q.prove (‘(case Green of Red => 0n | Green => 1 | Blue => 2)
                            = 1’, simp[])
        val th4 = Q.prove (‘∀c. c = Red ∨ c ≠ Red’, Induct >> simp[])
    in
      if List.all (null o hyp) [th1, th2, th3, th4] then OK()
      else die "not proved"
    end

(* ----------------------------------------------------------------------
    a record: one constructor, and its fields as that constructor's
    arguments.  The accessors and the update functions are the existing
    record apparatus's business, not the construction's; what the
    construction owes them is the type, the constructor and the axiom.
   ---------------------------------------------------------------------- *)

val rspec = parseSpec `point = <| x : num ; y : num |>`

val pointC = TypeBasePure.mk_recordtype_constructor "point"

val _ = tprint "a record's specification"
val _ =
    if #tynames rspec = ["point"] andalso
       #constructors rspec = [[pointC]] andalso
       #fields rspec = [SOME ["x", "y"]] andalso
       List.all (fn (ty,_) => ty = “:num # num”) (#functors rspec)
    then OK() else die "not as expected"

val rbnf = deriveBNFn db [alpha] (#1 (hd (#functors rspec)))
val rfix = #fixpoint (defineCopy {tyname = "point", ABS = "point_ABS",
                                  REP = "point_REP"} rbnf)
val rcs = defineConstructors (hd (#constructors rspec)) rbnf rfix

(* the constructor's name is not one the parser can read, so the axiom is
   compared against a term built rather than written *)
val f0 = mk_var ("f0", “:num -> num -> 'c”)
val h = mk_var ("h", “:point -> 'c”)
val a0 = mk_var ("a0", “:num”)
val a1 = mk_var ("a1", “:num”)

val _ = tprint "a record's axiom"
val _ =
    if #newty rfix = “:point” andalso
       same (concl (#axiom rcs))
             (list_mk_forall
                ([f0], mk_exists1
                   (h, list_mk_forall
                      ([a0, a1],
                       mk_eq (mk_comb (h, list_mk_comb (hd (#constructors rcs),
                                                        [a0, a1])),
                              list_mk_comb (f0, [a0, a1]))))))
    then OK() else die (thm_to_string (#axiom rcs))

val _ = tprint "a record's constructor is injective"
val _ =
    case hd (#one_one rcs) of
        NONE => die "none derived"
      | SOME th =>
          if length (strip_conj (#2 (strip_forall (concl th)))) = 1 andalso
             is_eq (#2 (strip_forall (concl th)))
          then OK() else die (thm_to_string th)

(* and the accessors, the update functions and the record syntax are the
   existing apparatus's, over the entry the construction makes *)
val rtyinfo =
    hd (typeBaseInfo {axiom = #axiom rcs,
                      induction = valOf (#induction rcs),
                      case_defs = defineCases (#existential_axiom rcs),
                      rewrites = [[]], names = [noNames]})
val _ = TypeBase.export
          [RecordType.prove_recordtype_thms
             (rtyinfo, valOf (hd (#fields rspec)))]

val _ = tprint "a record's accessors and updates"
val _ =
    let val th1 = Q.prove (‘(<| x := 3; y := 4 |> : point).x = 3’, simp[])
        val th2 = Q.prove (‘(r : point with x := 1).y = r.y’, simp[])
        val th3 = Q.prove (‘∀r : point. r with <| x := r.x; y := r.y |> = r’,
                           simp[DB.fetch "-" "point_component_equality"])
    in
      if List.all (null o hyp) [th1, th2, th3] then OK() else die "not proved"
    end

(* ----------------------------------------------------------------------
    a record with a parameter.  This is where the difference from the
    existing package's world shows: the type is a functor in its
    parameter, and its map and set functions are the functor's own,
    carried across the bijection.
   ---------------------------------------------------------------------- *)

val pty = mk_vartype "'p"
val pbnf = deriveBNFn db [alpha, pty] “:'p # num”
val pcopy = defineCopy {tyname = "wrap", ABS = "wrap_ABS",
                        REP = "wrap_REP"} pbnf
val pfix = #fixpoint pcopy
val pcs = defineConstructors ["Wrap"] pbnf pfix

val _ = tprint "a parameterised record's axiom"
val _ =
    if same (concl (#axiom pcs))
             “∀f0. ∃!h. ∀a0 a1. h (Wrap a0 a1) = f0 a0 a1”
    then OK() else die (thm_to_string (#axiom pcs))

(* the type is a functor in its parameter: the functor's own structure,
   conjugated by the bijection.  The BNF is derived in the parameter
   alone here — the recursive argument the construction wants is not one
   of the new type's arguments — and the transport needs nothing else. *)
val pbnf' = deriveBNFn db [pty] “:'p # num”
val ptr = transportBNF noNames {abs = #abs pcopy, rep = #rep pcopy,
                                absrep = #absrep pcopy,
                                repabs = #repabs pcopy} pbnf'

val _ = tprint "a parameterised record is a functor"
val _ =
    let val d = bnfBase.insert (#key ptr, #info ptr) db
        val mapth =
            Q.prove (‘∀f a n. wrapMAP f (Wrap a n) = Wrap (f a) n’,
                     simp[#map_def ptr, hd (#defs pcs), #cons_def pfix,
                          combinTheory.o_THM,
                          SRULE [FUN_EQ_THM, combinTheory.o_THM]
                                (#repabs pcopy)])
        val setth =
            Q.prove (‘∀a n. wrapSET (Wrap a n) = {a}’,
                     simp[hd (#set_defs ptr), hd (#defs pcs), #cons_def pfix,
                          combinTheory.o_THM,
                          SRULE [FUN_EQ_THM, combinTheory.o_THM]
                                (#repabs pcopy)] >>
                     simp[LAM_EQ_SING] >>
                     simp[EXTENSION, bnfPrelimsTheory.IN_equal, EQ_SYM_EQ])
    in
      if null (hyp mapth) andalso null (hyp setth) then OK()
      else die "not proved"
    end
