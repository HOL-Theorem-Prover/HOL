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
    in
      TypeBase.export tyinfos
    ; List.app saveThms tyinfos
    ; List.app (fn tyi => Parse.overload_on ("case", case_const_of tyi))
               tyinfos
    ; List.app computeLib.write_datatype_info tyinfos
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
    in
      List.filter (fn p => List.all (ok p) (#functors spec)) (#params spec)
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
      val cs = defineConstructors cnames bnf fix
      val axiom = #existential_axiom cs
      (* a nested recursion has no constructor-wise induction principle;
         the set-based one is what it keeps *)
      val induction = case #induction cs of
                          SOME th => th
                        | NONE => #set_induction cs
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
              ; [#map_eqns e] @ #set_eqns e
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
      val ccs = collapsedConstructors (#constructors spec) coll
      val cdefs = List.map #defs ccs
      val axiom = familyAxiomOf cdefs (familyExistence (#principle coll))
      val induction =
          familyInductionOf cdefs
            (familySetInductionOf fam (#types coll, #cons coll)
                                  (#principle coll))
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
                       (ListPair.zipEq (tynames, cbnfs))
      val eqns = if null params then [] else collapsedEqns coll fam cbnfs ccs
      val rewrites = if null params then List.map (fn _ => []) tynames
                     else List.map (fn e => #map_eqns e :: #set_eqns e) eqns
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
    ; persist tyinfos
    ; tyinfos
    end

fun bnfDatatypeInfo q =
    let val spec = parseSpec q
        val db = bnfBase.fullDB()
    in
      if length (#tynames spec) = 1 then oneType db spec else manyTypes db spec
    end

fun bnfDatatype q = ignore (bnfDatatypeInfo q)

end
