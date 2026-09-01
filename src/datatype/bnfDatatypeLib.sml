structure bnfDatatypeLib :> bnfDatatypeLib =
struct

open HolKernel boolLib bnfFixLib

val ERR = mk_HOL_ERR "bnfDatatypeLib"

(* ----------------------------------------------------------------------
    Registering what has just been built.

    The database records a theorem's *name*, so that a later session
    finds it in the theory rather than in this process; the laws the
    construction hands back are theorems, so each is saved first.
   ---------------------------------------------------------------------- *)

fun saveAs nm th : KernelSig.kernelname =
    (ignore (save_thm (nm, th)); {Thy = current_theory(), Name = nm})

fun numberedNames nm k =
    if k = 1 then [nm]
    else List.tabulate (k, fn i => nm ^ Int.toString (i + 1))

fun registerBNF {tyname} (key, bnfBase.bI info) =
    let
      val {bnd, bndthms, canontype, map, mapID, mapO, mapIMAGE, mapCONG,
           relator, set, wits, inhabits} = info
      fun each nm ths =
          ListPair.mapEq (fn (n, th) => saveAs n th)
                         (numberedNames (tyname ^ nm) (length ths), ths)
      fun eachP nm ps =
          ListPair.mapEq (fn (n, (t, th)) => (t, saveAs n th))
                         (numberedNames (tyname ^ nm) (length ps), ps)
    in
      bnfBase.updateDB
        (key,
         bnfBase.bI {
           bnd = bnd, bndthms = each "_bnd" bndthms, canontype = canontype,
           map = map, set = set,
           mapID = saveAs (tyname ^ "_MAP_ID") mapID,
           mapO = saveAs (tyname ^ "_MAP_O") mapO,
           mapIMAGE = each "_MAP_IMAGE" mapIMAGE,
           mapCONG = saveAs (tyname ^ "_MAP_CONG") mapCONG,
           relator = relator,
           wits = eachP "_wit" wits,
           inhabits = eachP "_inh" inhabits})
    end

(* ----------------------------------------------------------------------
    Making the entry stick, the way the old package does: the entry
    itself, the theorems under the names a development expects, the
    case constant's overload, and what the evaluator needs.
   ---------------------------------------------------------------------- *)

(* the theorem that records what the declaration said, which is what
   EmitML and the like read a datatype's shape off *)
fun datatype_presentation (spec : spec) =
    let
      val thy = current_theory()
      fun mkc n = prim_mk_const {Name = n, Thy = thy}
      fun decl (tyname, cs, flds) =
          case flds of
              NONE =>
              let val constrs = List.map (mkc o #1) cs
                  val tyv = mk_var (tyname,
                                    List.foldr (op -->) bool
                                               (List.map type_of constrs))
              in
                list_mk_comb (tyv, constrs)
              end
            | SOME fields =>
              let
                fun pmc f = mkc (TypeBasePure.mk_recordtype_fieldsel
                                   {tyname = tyname, fieldname = f})
                val hdc = pmc (hd fields)
                fun fieldvar n =
                    let val c = pmc n in mk_var (n, #2 (dom_rng (type_of c))) end
                val fvars = List.map fieldvar fields
                val tyv = mk_var (tyname, #1 (dom_rng (type_of hdc)))
                val recv = mk_var ("record",
                                   List.foldr (op -->) bool
                                     (type_of tyv :: List.map type_of fvars))
              in
                list_mk_comb (recv, tyv :: fvars)
              end
      val decls =
          List.map (fn (nm, (cs, flds)) => decl (nm, cs, flds))
                   (ListPair.zip (#tynames spec,
                                  ListPair.zip (#constructors spec,
                                                #fields spec)))
      val nm = hd (#tynames spec)
    in
      ignore (save_thm ("datatype_" ^ nm,
                        EQT_ELIM (ISPEC (list_mk_conj decls)
                                        boolTheory.DATATYPE_TAG_THM)))
    end

fun persist tyinfos =
    let
      open TypeBasePure
      fun saveThms tyi =
          let
            val tname = #2 (ty_name_of tyi)
            fun name s = tname ^ s
            fun optsave nm =
                fn NONE => () | SOME th => ignore (save_thm (name nm, th))
          in
            optsave "_11" (one_one_of tyi);
            optsave "_distinct" (distinct_of tyi);
            ignore (save_thm (name "_nchotomy", nchotomy_of tyi));
            ignore (save_thm (name "_Axiom", axiom_of tyi));
            ignore (save_thm (name "_induction", induction_of tyi));
            ignore (save_thm (name "_case_cong", case_cong_of tyi));
            ignore (save_thm (name "_case_eq", case_eq_of tyi))
          end
      (* the same word the other constructions say, in the same form:
         a session tells the reader what it has just defined *)
      val tynames = List.map (Lib.quote o #2 o ty_name_of) tyinfos
      val message = "Defined type" ^
                    (if length tynames > 1 then "s" else "") ^ ": " ^
                    String.concat (Lib.commafy tynames)
    in
      TypeBase.export tyinfos
    ; List.app saveThms tyinfos
    ; List.app (fn tyi => Parse.overload_on ("case", case_const_of tyi))
               tyinfos
    ; List.app computeLib.write_datatype_info tyinfos
    ; Feedback.HOL_MESG message
    end

(* ----------------------------------------------------------------------
    A specification of one type.

    Whether the construction or the copy builds it is decided by the
    specification: the variable standing for the type either occurs in
    the functor or does not.
   ---------------------------------------------------------------------- *)

fun theTypesConstants tyname =
    {tyname = tyname, ABS = tyname ^ "_ABS", REP = tyname ^ "_REP"}

(* Which of the specification's own variables the type can be a functor
   in: `'k |-> ftree` is functorial in the tree and not in the key, and
   a variable the specification uses in a position like that is an
   argument of the new type all the same — carried along, passive. *)
fun liveParams db (spec : spec) =
    let
      (* a member the variable does not occur in says nothing about it *)
      fun ok p (fty, _) =
          not (Lib.mem p (Type.type_vars fty)) orelse
          Lib.mem p (bnfLib.liveTyvars db fty)
      (* and a variable no member mentions at all is not an argument of
         these types: a declaration whose members fall into groups
         leaves each group only the variables it wrote *)
      fun used p =
          List.exists (fn (fty, _) => Lib.mem p (Type.type_vars fty))
                      (#functors spec)
    in
      List.filter (fn p => used p andalso List.all (ok p) (#functors spec))
                  (#params spec)
    end

(* The construction numbers a specification's variables 'b1, 'b2 ...,
   because those cannot collide with the type variables the stored laws
   are instantiated at.  What is saved says what the specification said:
   `:'a list`, not `:'b1 list`.  This is not cosmetic — ACCEPT_TAC and
   everything else that matches a theorem against a goal matches type
   variables by name. *)
fun asWritten (spec : spec) =
    let
      val theta = List.map (fn (p, w) => p |-> w) (#written spec)
      val internal = List.map #1 (#written spec)
      val written = List.map #2 (#written spec)
      (* The construction chose its own answer type, avoiding the names
         it was working with rather than the ones the specification
         wrote: `('a,'b,'c) ty` gets an axiom over 'b, and renaming the
         parameters back would then say 'b for two different things. *)
      fun freshFor avoid =
          let fun go [] = Type.gen_tyvar()
                | go (c::cs) = let val v = mk_vartype c
                               in if Lib.mem v avoid then go cs else v end
          in
            go ["'a", "'b", "'c", "'d", "'e", "'f", "'g", "'h"]
          end
      fun rename th =
          let
            val vs = Term.type_vars_in_term (concl th)
            val clashing = List.filter
                             (fn v => not (Lib.mem v internal) andalso
                                      Lib.mem v written)
                             vs
            fun fresh (v, (acc, avoid)) =
                let val n = freshFor avoid
                in ((v |-> n) :: acc, n :: avoid) end
            val (extra, _) = List.foldl fresh ([], written @ vs) clashing
          in
            INST_TYPE (theta @ extra) th
          end
    in
      if null theta then Lib.I else rename
    end

(* The older construction quantifies a clause's arguments outside the
   hypothesis, and `munge_ind_thm` pushes back in the ones the
   hypothesis does not mention — one at a time, innermost first, which
   turns their order around.  A clause built with them already inside
   keeps the order the specification wrote, and a proof that names them
   would then be reading a different argument, so they are put back
   outside first and munged from there.  *)
fun asOldQuantified th =
    let
      fun outward tm =
          (Conv.RIGHT_IMP_FORALL_CONV THENC BINDER_CONV outward) tm
          handle HOL_ERR _ => REFL tm
      val pull = STRIP_QUANT_CONV outward
    in
      CONV_RULE (STRIP_QUANT_CONV
                   (RATOR_CONV (RAND_CONV (EVERY_CONJ_CONV (QCONV pull)))))
                th
    end

fun oneType db (spec : spec) =
    let
      val tyname = hd (#tynames spec)
      val (fty, slots) = hd (#functors spec)
      val slot = hd slots
      val params = liveParams db spec
      val nms = hd (#names spec)
      val cnames = hd (#constructors spec)
      val recursive = Lib.mem slot (Type.type_vars fty)
      val bnf = bnfLib.deriveBNFn db (slot :: params) fty
      (* the type, and the constructors split along the functor's shape *)
      val (fix, copy) =
          if recursive then (defineFixpoint (theTypesConstants tyname) bnf,
                             NONE)
          else let val c = defineCopy (theTypesConstants tyname) bnf
               in (#fixpoint c, SOME c) end
      val cs = defineConstructors nms cnames bnf fix
      val wr = asWritten spec
      val axiom = wr (#existential_axiom cs)
      (* a nested recursion has no constructor-wise induction principle;
         the set-based one is what it keeps *)
      (* the induction principle as the rest of HOL reads one: the
         argument's quantifiers past the hypothesis, and the bound
         variables named for their types *)
      val induction =
          ind_types.munge_ind_thm
            (asOldQuantified
               (wr (case #induction cs of
                        SOME th => th
                      | NONE => #set_induction cs)))
      (* the new type as a functor of its own, so that a later
         specification can recurse through it *)
      (* a type with no arguments is not a functor: there is nothing for
         a map to move, and nothing for a later specification to recurse
         through it with *)
      val eqns =
          case copy of
              NONE =>
              if null params then []
              else
              let val res = fixpointBNF nms bnf fix
                  val e = constructorEqns cs res
              in
                registerBNF {tyname = tyname} (#key res, #info res)
              ; List.map wr ([#map_eqns e] @ #set_eqns e)
              end
            | SOME c =>
              (* nothing recurses, so the functor is the type's own,
                 conjugated by the bijection.  A type with no arguments
                 at all is not a functor and needs no entry. *)
              if null params then []
              else
                let val fbnf = bnfLib.deriveBNFn db params fty
                    val res = transportBNF nms {abs = #abs c, rep = #rep c,
                                                absrep = #absrep c,
                                                repabs = #repabs c} fbnf
                in
                  registerBNF {tyname = tyname} (#key res, #info res)
                ; []
                end
      val tyinfos =
          typeBaseInfo {axiom = axiom, induction = induction,
                        case_defs = defineCases axiom,
                        rewrites = [eqns], names = #names spec}
      (* a record's accessors, update functions and literal syntax are
         the existing apparatus's, over the entry just made *)
      val tyinfos =
          case hd (#fields spec) of
              NONE => tyinfos
            | SOME flds =>
              [RecordType.prove_recordtype_thms (hd tyinfos, flds)]
    in
      List.app (fn th => ignore (save_thm (name_of_eqn th, th))) eqns
    ; datatype_presentation spec
    ; persist tyinfos
    ; tyinfos
    end
(* an equation is named after the constant it is about.  Each
   constructor's clause carries its own quantifier, so the conjunct has
   to be opened as well as the theorem. *)
and name_of_eqn th =
    let val c = hd (strip_conj (#2 (strip_forall (concl th))))
        val l = lhs (#2 (strip_forall c))
    in
      #1 (dest_const (#1 (strip_comb l))) ^ "_thm"
    end

(* ----------------------------------------------------------------------
    A specification of several types at once.

    The construction builds the family from the last member back, each
    member an instance of an operator over the members before it, so the
    types it defines are not the ones the specification asks for.  They
    are scaffolding: the members are copied onto types of their own —
    named as the specification names them — and the constructors, the
    principle, and each member's functoriality are carried across.
   ---------------------------------------------------------------------- *)

fun manyTypes db (spec : spec) =
    let
      val tynames = #tynames spec
      val n = length tynames
      val params = liveParams db spec
      val fam = defineFamily {tynames = List.map (fn s => s ^ "_raw") tynames}
                             db params (#functors spec)
      val principle = familyPrinciple fam
      val coll = collapseFamily {tynames = tynames} fam principle
      val ccs = collapsedConstructors (hd (#names spec))
                                      (#constructors spec) coll
      val cdefs = List.map #defs ccs
      val wr = asWritten spec
      val axiom = wr (familyAxiomOf cdefs (familyExistence (#principle coll)))
      val induction =
          ind_types.munge_ind_thm
            (asOldQuantified
               (wr (familyInductionOf cdefs
                      (familySetInductionOf fam (#types coll, #cons coll)
                                            (#principle coll)))))
      (* each member as a functor of its own: the copy of a composite
         already in the database, conjugated by the bijection *)
      val cbnfs =
          if null params then []
          else
          List.tabulate
            (n, fn j =>
                  transportBNF (List.nth (#names spec, j))
                    {abs = List.nth (#abs coll, j),
                     rep = List.nth (#rep coll, j),
                     absrep = List.nth (#absrep coll, j),
                     repabs = List.nth (#repabs coll, j)}
                    (bnfLib.deriveBNFn (#db fam) params
                                       (List.nth (#types fam, j))))
      val _ = List.app (fn (nm, r : copied_bnf) =>
                           registerBNF {tyname = nm} (#key r, #info r))
                       (ListPair.zip (tynames, cbnfs))
      val eqns = if null params then [] else collapsedEqns coll fam cbnfs ccs
      val rewrites = if null params then List.map (fn _ => []) tynames
                     else List.map (fn e => List.map wr
                                              (#map_eqns e :: #set_eqns e))
                                   eqns
      val tyinfos =
          typeBaseInfo {axiom = axiom, induction = induction,
                        case_defs = defineCases axiom,
                        rewrites = rewrites, names = #names spec}
      (* a member written as a record gets the record apparatus, as a
         type of its own would *)
      val tyinfos =
          ListPair.mapEq
            (fn (NONE, tyi) => tyi
              | (SOME flds, tyi) =>
                  RecordType.prove_recordtype_thms (tyi, flds))
            (#fields spec, tyinfos)
    in
      List.app (fn th => ignore (save_thm (name_of_eqn th, th)))
               (List.concat rewrites)
    ; datatype_presentation spec
    ; persist tyinfos
    ; tyinfos
    end

(* ----------------------------------------------------------------------
    The groups a declaration falls into.

    A declaration's members need not refer to each other.  `a2 = A num ;
    b = B 'a` says two independent things, and the older construction
    defines two types of their own arities from it — not one family of
    two.  The construction here takes a group of members that reach each
    other; the groups themselves come in the order their references say,
    each built over the types the ones before it defined.
   ---------------------------------------------------------------------- *)
fun groupsOf (spec : spec) =
    let
      fun upto k = List.tabulate (k, fn i => i)
      val n = length (#tynames spec)
      val functors = #functors spec
      fun slotOf j = List.nth (#2 (List.nth (functors, 0)), j)
      (* member j reaches member k when k's slot is in j's functor; its
         own slot is alpha wherever it appears *)
      fun reaches j k =
          let val (fty, slots) = List.nth (functors, j)
              val v = if j = k then Type.alpha else List.nth (slots, k)
          in
            Lib.mem v (Type.type_vars fty)
          end
      (* the members that reach each other, by closing the relation *)
      fun closure j =
          let fun go seen [] = seen
                | go seen (k::ks) =
                  if Lib.mem k seen then go seen ks
                  else go (k :: seen)
                          (List.filter (reaches k) (upto n) @ ks)
          in
            go [] [j]
          end
      (* a group keeps the order the declaration wrote its members in:
         which member is built first, and which type variable stands for
         which member, are read off that order *)
      val group =
          List.tabulate
            (n, fn j => List.filter (fn k => Lib.mem k (closure j) andalso
                                             Lib.mem j (closure k))
                                    (upto n))
      (* the groups, each once, in an order where a member's own group
         comes after the groups it reaches *)
      fun add (j, gs) =
          if List.exists (fn g => Lib.mem j g) gs then gs
          else gs @ [List.nth (group, j)]
      val gs = List.foldl add [] (upto n)
      fun ready done g =
          List.all (fn j => List.all (fn k => Lib.mem k g orelse
                                              Lib.mem k done)
                                     (List.filter (reaches j) (upto n)))
                   g
      fun order (done, gs) =
          if null gs then []
          else
            case List.find (ready done) gs of
                NONE => raise ERR "groupsOf"
                              "the declaration's references do not settle"
              | SOME g => g :: order (done @ g,
                                      List.filter (fn h => h <> g) gs)
    in
      order ([], gs)
    end

(* A member's own entry names its own slot α, so the variable standing
   for member k is read off the entry of any other member. *)
fun slotOf (spec : spec) k =
    let val j = if k = 0 then 1 else 0
    in
      if length (#functors spec) = 1 then
        (* one member names nothing but itself *)
        List.nth (#2 (hd (#functors spec)), k)
      else List.nth (#2 (List.nth (#functors spec, j)), k)
    end

(* the members a group names, with the types the groups before it
   defined put in for their slots *)
fun subSpec (spec : spec) theta g : spec =
    let
      fun pick l = List.map (fn j => List.nth (l, j)) g
      fun ftorOf j =
          let val (fty, slots) = List.nth (#functors spec, j)
              val slots' =
                  List.map (fn k => List.nth (slots, k)) g
          in
            (Type.type_subst theta fty, slots')
          end
    in
      {tynames = pick (#tynames spec), params = #params spec,
       functors = List.map ftorOf g,
       constructors = pick (#constructors spec),
       fields = pick (#fields spec), names = pick (#names spec),
       written = #written spec}
    end

fun ofSpec spec =
    let
      val groups = groupsOf spec
      (* what a group has just defined, for the groups that name it *)
      fun defined (g, tyinfos) =
          ListPair.mapEq
            (fn (j, tyi) => slotOf spec j |-> TypeBasePure.ty_of tyi)
            (g, tyinfos)
      fun go (theta, []) = []
        | go (theta, g :: gs) =
          let val db = bnfBase.fullDB()
              val sub = subSpec spec theta g
              val tyinfos = if length g = 1 then oneType db sub
                            else manyTypes db sub
          in
            tyinfos @ go (theta @ defined (g, tyinfos), gs)
          end
    in
      go ([], groups)
    end

fun bnfDatatypeInfo q = ofSpec (parseSpec q)

fun bnfDatatype q = ignore (bnfDatatypeInfo q)

(* ----------------------------------------------------------------------
    Can this construction express the specification at all?

    A type the specification defines has to occur where a map can move
    it: inside operators the functor database knows, in the arguments
    they are functorial in.  `t = c of 'a => t itself` recurses through
    an operator that holds no elements of its argument, so there is
    nothing for the construction to take a fixed point of — the
    specification is outside the BNF world rather than merely awkward,
    and it is the older construction's to build.
   ---------------------------------------------------------------------- *)
fun expressible astl =
    let
      val spec = specOfASTs (List.map (fn (name, form) =>
                                          {name = name, attrs = [],
                                           form = form})
                                      astl)
      val db = bnfBase.fullDB()
      fun ok (fty, slots) =
          let val live = bnfLib.liveTyvars db fty
              val occurs = List.filter
                             (fn v => Lib.mem v (Type.type_vars fty)) slots
          in
            List.all (fn v => Lib.mem v live) occurs
          end
    in
      List.all ok (#functors spec)
    end
    handle HOL_ERR _ => false

(* what a caller that has parsed already hands over: the older entry
   point's syntax gives the same declarations, without attributes *)
fun bnfDatatypeASTs astl =
    ignore (ofSpec (specOfASTs
                      (List.map (fn (name, form) =>
                                    {name = name, attrs = [], form = form})
                                astl)))

end
