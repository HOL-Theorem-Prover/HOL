signature Defn =
sig
  type hol_type     = Type.hol_type
  type term         = Term.term
  type thm          = Thm.thm
  type conv         = Abbrev.conv
  type tactic       = Abbrev.tactic
  type thry         = TypeBasePure.typeBase
  type proofs       = GoalstackPure.proofs
  type absyn        = Absyn.absyn
  type ppstream     = Portable.ppstream
  type 'a quotation = 'a Portable.frag list
  type ('a,'b)subst = ('a,'b) Lib.subst

  type defn         = DefnBase.defn

  val monitoring : bool ref    (* currently useless *)

  val ind_suffix : string ref
  val def_suffix : string ref

  val mk_defn    : string -> term -> defn
  val mk_Rdefn   : string -> term -> term -> defn
  val Hol_defn   : string -> term quotation -> defn
  val Hol_Rdefn  : string -> term quotation -> term quotation -> defn

  val eqns_of    : defn -> thm list
  val ind_of     : defn -> thm option
  val tcs_of     : defn -> term list
  val reln_of    : defn -> term option
  val params_of  : defn -> term list

  val aux_defn   : defn -> defn option
  val union_defn : defn -> defn option

  val inst_defn  : defn -> (term,term)subst * (hol_type,hol_type)subst -> defn
  val set_reln   : defn -> term -> defn

  val elim_tcs   : defn -> thm list -> defn
  val simp_tcs   : defn -> conv -> defn
  val prove_tcs  : defn -> tactic -> defn

  val save_defn  : defn -> unit

  val parse_defn : term quotation -> term * string list

  val tgoal      : defn -> proofs
  val tprove     : defn * tactic -> thm * thm



   (* Historical relics *)

   val prim_wfrec_definition :
        thry -> string
             -> {R:term, functional:term}
             -> {def:thm, corollary:thm, theory:thry}

   val gen_wfrec_definition :
         thry -> string
              -> {R:term, eqs:term}
              -> {rules : thm,
                  TCs : term list list,
                  full_pats_TCs : (term * term list) list,
                  patterns : Functional.pattern list,
                  theory:thry}


(*---------------------------------------------------------------------------

 [mk_defn stem eqns] attempt to define a function, given some input
     equations (eqns) and a "bindstem" (stem). The input equations are
     treated as a specification, and mk_defn attempts to derive them from
     a more primitive definition. For non-primitive recursions, termination
     constraints are automatically synthesized. The following kinds of
     equations are handled:

       1. Single equation, Non-recursive, varstructs (tuples of variables)
          allowed on the left hand side.
             -- use standard abbreviation mechanism of HOL

       2. Primitive recursive (or non-recursive) over known datatype.
             -- use Prim_rec.new_recursive_definition with a datatype
                axiom fetched from theTypeBase(). This case includes
                some mutual recursions, i.e., those that fit into the
                input format accepted by new_recursive_definition
                (all arguments to recursive calls are immediate subterms
                of the argument to the initiating call).

       3. Non-recursive set of equations, over more complex patterns than
          allowed in 1.
             -- use wellfounded recursion, and automatically eliminate
                the vacuous wellfoundedness requirement. There will be
                no other termination conditions.

       4. Recursions (not mutual or nested) that aren't handled by 2.
             -- use wellfounded recursion, and automatically synthesize
                the termination conditions, which become hypotheses.
                The synthesis of termination conditions also happens
                in 5-7.

       5. Nested recursions.
             -- use wellfounded recursion. An "auxiliary" function
                is defined in order to allow the termination relation
                to be deferred. The termination conditions will be
                those of the auxiliary function.

       6. Mutual recursions that aren't handled by 2.
             -- use wellfounded recursion. An auxiliary `union' function
                is defined , from which the specified functions are derived.
                If the union function is a nested recursion, then 5 is
                also called. The termination conditions will be those
                of the auxiliary function.

       7. Schematic definitions (must be recursive).
             -- free variables occurring in the right hand side and not the
                left are abstracted out as parameters. All kinds of recursion,
                including mutual and nested styles are accepted.

     For 3-7, induction theorems are derived. Also, the implementation
     of wellfounded recursion processes functions over a single tupled
     argument, but it is convenient for users to give curried definitions,
     so for 3-7, there is an automatic translation from curried recursion
     equations (and induction theorems) into (and back out of) the tupled
     form.

     A number of primitive definitions may be made in the course of
     defining the specified function. Since these must be stored in the
     current theory, names for the ML bindings of these will be invented
     by "mk_defn". Such names will be derived from the "stem" argument,
     which must be an alphanumeric. In the case that the specified
     function is non-recursive or primitive recursive, the specified
     equation(s) will be added to the current theory under the stem
     name. Otherwise, the specified equation(s) and induction theorem
     will not be stored in the current theory (although underlying
     definitions used to derive the equations will be). The reasoning
     behind this is that the user will typically want to eliminate
     termination conditions before storing the equations (and associated
     induction theorem) in the current theory.

     Schematic definitions are a counter-example to this. For the sake of
     consistency, a scheme definition and its associated induction theorem
     are not stored in the current theory by "mk_defn".

 ---------------------------------------------------------------------------*)

end
