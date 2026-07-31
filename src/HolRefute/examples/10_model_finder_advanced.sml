(* ===================================================================== *)
(*  HolRefute by example, 10: the model finder on harder types           *)
(*                                                                       *)
(*  Fixpoints, codatatypes, typedefs and quotients: the constructions    *)
(*  where "translate the definition" is not enough and the model finder  *)
(*  needs either an unrolling depth or a registration to work with.  Also*)
(*  the display registry, which changes how models are printed without   *)
(*  touching what is certified.                                          *)
(*                                                                       *)
(*  Needs Kodkodi (see 09_model_finder.sml).  About 30 seconds end to    *)
(*  end: fifteen Kodkodi calls of roughly 1.3 seconds each, most of      *)
(*  that the JVM.  It runs one Kodkodi thread, so the quoted outputs     *)
(*  reproduce rather than racing between scopes.                         *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/10_model_finder_advanced.sml                      *)
(* ===================================================================== *)

load "Refute";
load "llistTheory";
load "lbtreeTheory";
load "quotientLib";
open Refute;
open quotient;

(* One Kodkodi thread, so the scopes are tried smallest first instead of *)
(* racing; that is what makes the models quoted below reproduce.         *)
val mf = !the_config
  |> upd_backends (SOME ["kodkod"])
  |> upd_max_threads 1
  |> upd_card [(NONE, [2, 3])];

(* --------------------------------------------------------------------- *)
(* 1.  Inductive predicates                                              *)
(*                                                                       *)
(* A least fixpoint is either solved directly, when its equations are    *)
(* well-founded, or approximated by unrolling.  [upd_iter] sets the      *)
(* unrolling depths, [upd_wf] overrides the well-foundedness verdict, and*)
(* [upd_star_linear_preds] chooses exact closure for linear predicates.  *)
(* A mutual group shares one iterator row.                               *)
(*                                                                       *)
(* Nothing in sections 1 to 5 is certified.  A Hol_reln constant, a      *)
(* codatatype, a typedef and a quotient are all outside the executable   *)
(* fragment Refute_Cert replays, so the model finder stops at Potential  *)
(* and says why: "untrusted Kodkodi model; no HOL certificate".  The     *)
(* certainty ladder is in 09_model_finder.sml.                           *)
(* --------------------------------------------------------------------- *)

val (even_rel_rules, even_rel_ind, even_rel_cases) = Hol_reln `
  (even_rel (0 : num)) /\
  (!n. even_rel n ==> even_rel (n + 2))`;
(* ==> even_rel_cases =                                                  *)
(* ==>   ⊢ ∀a0. even_rel a0 ⇔ a0 = 0 ∨ ∃n. a0 = n + 2 ∧ even_rel n       *)
(*                                                                       *)
(* The `: num` is load-bearing.  Without it the numerals resolve to      *)
(* :rat, and every goal below then comes back                            *)
(*   Unknown ["kodkod: formula was semantically weakened by whack or     *)
(*             ersatz after checking 4 of 4 scopes"]                     *)
(* because rational arithmetic goes through the Frac ersatz encoding of  *)
(* section 6.                                                            *)

val even_rel_pred = ``even_rel : num -> bool``;

refute mf ``even_rel n ==> n = 0``;
(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(* ==>   kodkod, 1.2s):                                                  *)
(* ==>   Scope: card num = 3                                             *)
(* ==>     n = 2                                                         *)
(* ==>   Potential counterexample:                                       *)
(* ==>     untrusted Kodkodi model; no HOL certificate                   *)
(* ==>   …continuing search for a genuine counterexample                 *)
(*                                                                       *)
(* That is the shape of every model in sections 1 to 5; only the scope   *)
(* and the bindings are quoted from here on.                             *)

refute (mf |> upd_star_linear_preds false
           |> upd_iter [(SOME even_rel_pred, [2]), (NONE, [0])])
  ``~even_rel 2``;
(* ==> Potential counterexample, Scope: card num = 3.  The goal is       *)
(*     closed, so the model has no bindings: the content is that 2 is    *)
(*     reachable within two unrollings of the base clause.               *)

refute (upd_wf [(NONE, SOME false)] mf) ``even_rel n ==> n = 0``;
(* ==> Potential counterexample, Scope: card num = 3, n = 2.  Denying    *)
(*     well-foundedness switches to the unrolled approximation, which    *)
(*     is visible in the model: it now reports                           *)
(*       $var$(even_rel.base) = {0; ... }                                *)
(*       $var$(even_rel.step) = K $?                                     *)
(*       even_rel ≤ $?                                                   *)
(*     - a lower bound on the predicate rather than an equation.         *)

refute (upd_star_linear_preds false mf) ``even_rel n ==> n = 0``;
(* ==> Potential counterexample, Scope: card num = 3, n = 2.  Turning    *)
(*     exact closure off costs nothing here; the predicate is still      *)
(*     well-founded, so the direct equation is used either way.          *)

(* --------------------------------------------------------------------- *)
(* 2.  Coinductive predicates                                            *)
(*                                                                       *)
(* Greatest fixpoints have to be introduced with Hol_coreln: a           *)
(* hand-rolled gfp is not recognised as one.  Unrolling is again the     *)
(* fallback, with the same iterator row.                                 *)
(* --------------------------------------------------------------------- *)

val (always_rules, always_coind, always_cases) = Hol_coreln `
  !b. b /\ always b ==> always b`;
(* ==> always_cases = ⊢ ∀a0. always a0 ⇔ a0 ∧ always a0                  *)
(*     The greatest solution of that equation is {T}, so `always F` is   *)
(*     false and the model finder should refute it.                      *)

refute mf ``always F``;
(* ==> Potential counterexample, Scope: iter scratch$always = 0.  The    *)
(*     scope entry is the gfp iterator, not a cardinality: the model     *)
(*     lives in the type :'refute$gfpit$scratch$always.  Closed goal, so *)
(*     no bindings; the model reports λi. always = K $?.                 *)

refute (upd_iter [(SOME ``always : bool -> bool``, [2]), (NONE, [0])] mf)
  ``always F``;
(* ==> the same counterexample, now at the pinned depth                  *)
(*     Scope: iter scratch$always = 1, with stats reporting              *)
(*     ("scopes", 1) instead of ("scopes", 2).                           *)

(* --------------------------------------------------------------------- *)
(* 3.  Codatatypes and bisimulation                                      *)
(*                                                                       *)
(* Lazy lists are cyclic objects, and the countermodel below is one: an  *)
(* infinite list equal to its own tail.  Equality of such values is      *)
(* checked by bisimulation up to [bisim_depth], which appears in the     *)
(* scope as an iterator of its own; setting the depth to ~1 drops that   *)
(* iterator and skips the recheck.                                       *)
(* --------------------------------------------------------------------- *)

refute mf ``(xs : num llist) <> llist$LCONS a xs``;
(* ==> Refute warning: the conjecture either holds for the given scopes  *)
(* ==>   or lies outside the supported fragment; only potentially        *)
(* ==>   spurious models may be found                                    *)
(* ==> Potential counterexample:                                         *)
(* ==>   Scope: bisim_depth = 1, card num llist = 2, card num = 2        *)
(* ==>     xs = safe_The (λω. ω = 0:::ω)                                 *)
(* ==>     a = 0                                                         *)
(*                                                                       *)
(* [safe_The (λω. ω = 0:::ω)] is the cyclic value: the unique list equal *)
(* to [0:::] itself.  The model also prints the reconstructed relation   *)
(* $var$(refute$bisim), indexed by bisimulation depth.                   *)

refute (upd_bisim_depth [~1] mf)
  ``(xs = llist$LCONS (a : num) xs /\ ys = llist$LCONS a ys) ==> xs = ys``;
(* ==> Potential counterexample:                                         *)
(* ==>   Scope: card num llist = 2, card num = 2                         *)
(* ==>     xs = safe_The (λω. ω = 1:::ω)                                 *)
(* ==>     a = 1                                                         *)
(* ==>     ys = safe_The (λω. ω = 1:::ω)                                 *)
(*                                                                       *)
(* Note the missing bisim_depth entry, and that the reported enumeration *)
(* of :num llist lists safe_The (λω. ω = 1:::ω) twice.  With the recheck *)
(* off nothing compares those two atoms coinductively, so the "counter-  *)
(* example" may well be two names for one list.                          *)

(* Registering an audited built-in codatatype is idempotent: it          *)
(* validates the registration instead of creating theory content.  Pass  *)
(* the case and constructor constants at their own generic types; a      *)
(* description that disagrees with the built-in one is rejected with     *)
(* "registration disagrees with the built-in codatatype".                *)
register_codatatype
  {tyop = {Thy = "lbtree", Tyop = "lbtree"},
   case_const = ``lbtree$lbtree_case``,
   constructors = [``lbtree$Lf``, ``lbtree$Nd``]};
(* ==> val it = (): unit                                                 *)

refute mf ``t = lbtree$Nd (a : num) t t ==> t = lbtree$Lf``;
(* ==> Potential counterexample:                                         *)
(* ==>   Scope: bisim_depth = 1, card num lbtree = 2, card num = 2       *)
(* ==>     t = safe_The (λω. ω = Nd 0 ω ω)                               *)
(* ==>     a = 0                                                         *)
(*                                                                       *)
(* A branching codatatype has cyclic values too, so t can be its own     *)
(* left and right subtree without being a leaf.                          *)

(* --------------------------------------------------------------------- *)
(* 4.  A typedef of your own                                             *)
(*                                                                       *)
(* The model finder harvests typedef metadata on demand, and an explicit *)
(* registration supplies it directly when harvesting cannot.             *)
(* [absrep_thm] is the exported conjunction of the two bijection laws,   *)
(* and it has to agree with the type's <tyop>_TY_DEF theorem.            *)
(* --------------------------------------------------------------------- *)

val mirror_exists = prove (``?n : num. (\n. T) n``,
  Q.EXISTS_TAC `0` >> simp []);

val mirror_tydef = new_type_definition ("mirror", mirror_exists);
(* ==> ⊢ ∃rep. TYPE_DEFINITION (λn. T) rep                               *)

val mirror_absrep = define_new_type_bijections
  {name = "mirror_absrep", ABS = "mirror_abs", REP = "mirror_rep",
   tyax = mirror_tydef};
(* ==> ⊢ (∀a. mirror_abs (mirror_rep a) = a) ∧                           *)
(* ==>   ∀r. (λn. T) r ⇔ mirror_rep (mirror_abs r) = r                   *)

register_typedef
  {ty = ``:mirror``, abs = ``mirror_abs``, rep = ``mirror_rep``,
   absrep_thm = mirror_absrep};
(* ==> val it = (): unit                                                 *)

refute (upd_card [(SOME ``:mirror``, [2]), (NONE, [2])] mf)
  ``mirror_rep (x : mirror) = 0``;
(* ==> Potential counterexample:                                         *)
(* ==>   Scope: card mirror = 2, card num = 2                            *)
(* ==>     x = mirror_abs 1                                              *)
(* ==>   Evaluated terms:                                                *)
(* ==>     mirror_rep x = 1                                              *)
(* ==>     0 = 0                                                         *)
(*                                                                       *)
(* Values of the new type are displayed through its abstraction          *)
(* function, and the type enumeration in the model reads                 *)
(* [mirror_abs 0; mirror_abs 1].  The cardinalities are pinned so that   *)
(* this call solves one scope rather than the two [mf] would offer.      *)

(* --------------------------------------------------------------------- *)
(* 5.  A quotient of your own                                            *)
(*                                                                       *)
(* [register_quotient] takes the abstraction and representation          *)
(* constants and a hypothesis-free theorem fixing the equivalence        *)
(* relation.  Either shape does: the `QUOTIENT R abs rep` that           *)
(* [quotient.define_quotient_type] returns, or the total extensionality  *)
(* theorem handed to it.  The theorem's shape, not the legacy [partial]  *)
(* field, picks the encoding: `QUOTIENT` gets the sound partial one, a   *)
(* total equivalence drops its then redundant domain axiom.              *)
(* --------------------------------------------------------------------- *)

val par_def = Define `par (x : num) y <=> (EVEN x = EVEN y)`;

val par_equiv = prove (``!x y. par x y = (par x = par y)``,
  simp [par_def, FUN_EQ_THM, EQ_IMP_THM] >> metis_tac []);

val par_quot = define_quotient_type "parity" "parity_abs" "parity_rep"
  par_equiv;
(* ==> ⊢ QUOTIENT par parity_abs parity_rep                              *)

register_quotient
  {qty = ``:parity``, rty = ``:num``,
   abs = ``parity_abs``, rep = ``parity_rep``,
   equiv_thm = par_quot, partial = false};
(* ==> val it = (): unit                                                 *)

refute (upd_card [(SOME ``:num``, [2]), (NONE, [2])] mf)
  ``(x : parity) = y``;
(* ==> Potential counterexample:                                         *)
(* ==>   Scope: card num = 2, card parity = 2                            *)
(* ==>     x = «0»                                                       *)
(* ==>     y = «1»                                                       *)
(*                                                                       *)
(* «0» and «1» are equivalence classes, printed by their representative  *)
(* and returned as the terms Quot 0 and Quot 1.  0 and 1 have different  *)
(* parities, so the two classes are distinct and the goal fails.         *)

(* --------------------------------------------------------------------- *)
(* 6.  How model values are printed                                      *)
(*                                                                       *)
(* A term postprocessor is a display-only, bottom-up transformation for  *)
(* every type matching a pattern; it must preserve the term's type.      *)
(* Certification always uses the untouched raw terms, so a postprocessor *)
(* can never make a bogus counterexample look good.  General patterns    *)
(* run before more specific ones, and re-registering a pattern replaces  *)
(* it.                                                                   *)
(* --------------------------------------------------------------------- *)

register_term_postprocessor ``:num``
  (fn tm => if numSyntax.is_numeral tm then ``SUC 0 * ^tm`` else tm);

refute mf ``(n : num) < 1``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card num = 2                                             *)
(* ==>     n = SUC 0 * 1                                                 *)
(* ==>   Certified: ⊢ ¬∀n. n < 1                                         *)
(*                                                                       *)
(* This goal is executable, so unlike sections 1 to 5 the model is       *)
(* certified.  Every numeral on display goes through the postprocessor - *)
(* the returned model enumerates :num as [SUC 0 * 0; SUC 0 * 1] - while  *)
(* the certificate is stated in ordinary numerals.                       *)

Option.isSome (lookup_term_postprocessor ``:num``);
(* ==> val it = true: bool                                               *)
(*     The lookup returns the composed transformation for :num.          *)

(* Rationals are displayed through the built-in Frac encoding, which is  *)
(* registered by default; this call restores or refreshes it.            *)
register_frac_type_rat ();
(* ==> val it = (): unit                                                 *)

(* Put plain numerals back, so the models below read normally.           *)
register_term_postprocessor ``:num`` (fn tm => tm);

(* --------------------------------------------------------------------- *)
(* 7.  Type variables: one scope or many                                 *)
(*                                                                       *)
(* Independent type variables get independent scopes, which multiplies   *)
(* the work.  [upd_merge_type_vars true] instantiates them all to the    *)
(* alphabetically first one: fewer scope blocks, at the cost of losing   *)
(* models that need different cardinalities.                             *)
(* --------------------------------------------------------------------- *)

refute (upd_merge_type_vars true mf)
  ``(f : 'a -> 'b) x = (g : 'a -> 'b) x``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card α = 2                                               *)
(* ==>     f = (K _)⦇a2 ↦ a1; a1 ↦ a1⦈                                   *)
(* ==>     x = a1                                                        *)
(* ==>     g = (K _)⦇a2 ↦ a2; a1 ↦ a2⦈                                   *)
(* ==>   Evaluated terms:                                                *)
(* ==>     f x = rf2_2                                                   *)
(* ==>     g x = rf2_1                                                   *)
(* ==>   Certified: ⊢ ¬∀f x g. f x = g x                                 *)
(*                                                                       *)
(* One scope block, on α alone: β has been instantiated away, so f and g *)
(* are endofunctions here rather than α -> β.                            *)

(* --------------------------------------------------------------------- *)
(* 8.  Translation knobs                                                 *)
(*                                                                       *)
(*   upd_mono              force or forbid treating a type as monotonic. *)
(*   upd_finitize          finitize an infinite type when monotonicity   *)
(*                         permits (NONE lets Refute choose).            *)
(*   upd_box               box functions and pairs.                      *)
(*   upd_specialize        specialize static higher-order arguments.     *)
(*   upd_destroy_constrs   split constructor applications.               *)
(*   upd_total_consts      assume constants are total.                   *)
(*   upd_user_axioms       take user axioms into account.                *)
(*   upd_peephole_optim    peephole-optimise the relational formula.     *)
(*   upd_datatype_sym_break, upd_kodkod_sym_break                        *)
(*                         symmetry-breaking budgets.                    *)
(*                                                                       *)
(* They mostly matter when a translation is too slow or too weak; the    *)
(* defaults are chosen to be sound either way.                           *)
(* --------------------------------------------------------------------- *)

refute
  (mf |> upd_mono [(SOME ``:num``, SOME true)]
      |> upd_finitize [(NONE, SOME true)]
      |> upd_box [(NONE, SOME false)]
      |> upd_specialize false
      |> upd_destroy_constrs false
      |> upd_total_consts (SOME true)
      |> upd_user_axioms (SOME false)
      |> upd_peephole_optim false
      |> upd_datatype_sym_break 3
      |> upd_kodkod_sym_break 10)
  ``xs <> [] ==> HD (xs : num list) = 0``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card num list = 2, card num = 2                          *)
(* ==>     xs = [1]                                                      *)
(* ==>   Evaluated terms:                                                *)
(* ==>     HD xs = 1                                                     *)
(* ==>     0 = 0                                                         *)
(* ==>   Certified: ⊢ ¬∀xs. xs ≠ [] ⇒ HD xs = 0                          *)
(*                                                                       *)
(* Ten knobs away from the defaults and the answer is unchanged, which   *)
(* is the point: they trade translation size against precision, not      *)
(* soundness.                                                            *)

(* --------------------------------------------------------------------- *)
(* 9.  Looking inside the translation                                    *)
(*                                                                       *)
(* [upd_debug true] does not narrate the run.  It makes the generated    *)
(* Kodkodi problem verbose - readable atom names and scope comments -    *)
(* sends one scope per Kodkodi call instead of a whole batch, and skips  *)
(* the solved-problem cache.  [upd_overlord true] additionally leaves    *)
(* the generated .kki, .out and .err files in a fresh directory under    *)
(* the working directory instead of deleting them.  Both are for         *)
(* diagnosing a translation, not for daily use.                          *)
(* --------------------------------------------------------------------- *)

refute (upd_debug true mf) ``SUC n = n``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card num = 2                                             *)
(* ==>     n = 1                                                         *)
(* ==>   Certified: ⊢ ¬∀n. SUC n = n                                     *)
(*                                                                       *)
(* The only difference visible from here is in the returned stats: two   *)
(* scopes now mean ("batches", 2), where every other section in this     *)
(* file reports ("batches", 1).                                          *)
