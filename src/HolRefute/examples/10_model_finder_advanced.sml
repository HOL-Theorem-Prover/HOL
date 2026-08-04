(* ===================================================================== *)
(*  HolRefute by example, 10: the model finder on harder types           *)
(*                                                                       *)
(*  Fixpoints, codatatypes, typedefs and quotients: the constructions    *)
(*  where "translate the definition" is not enough and the model finder  *)
(*  needs either an unrolling depth or a registration to work with.  Also*)
(*  the display registry, which changes how models are printed without   *)
(*  touching what is certified.                                          *)
(*                                                                       *)
(*  Needs Kodkodi (see 09_model_finder.sml).  Around 32 seconds end to   *)
(*  end on an otherwise idle 32-core host: 16 Kodkodi calls ranging      *)
(*  from 1.3 to 2.6 seconds, median 1.3, about 24 of those seconds       *)
(*  spent inside Kodkodi and most of the rest in session start-up and    *)
(*  the JVM.  Read the figure as machine-dependent rather than as a      *)
(*  promise — it moves with the host, the Java runtime, and whatever     *)
(*  else the machine is doing, and it roughly doubles when the machine   *)
(*  is busy.                                                             *)
(*                                                                       *)
(*  Every model-finder call in the corpus pins [upd_max_threads 1] and   *)
(*  an explicit [upd_card] row, so that the scopes are tried smallest    *)
(*  first and the quoted outputs reproduce instead of racing.  This      *)
(*  file's [mf] below is where that convention comes from.  Exactly one  *)
(*  call is deliberately left racing — the opener of section 1 of        *)
(*  09_model_finder.sml — and says so.                                   *)
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
(* fragment Refute_Cert replays, so there is nothing for the kernel to   *)
(* work on and every report below ends "Certification: uncertified".     *)
(* That does not weaken the verdict: a model-finder result takes its     *)
(* certainty from the encoding, and these encodings are sound and exact, *)
(* so the models are Genuine with cert = NONE.  The one exception is     *)
(* section 3's second call, where switching the bisimulation recheck off *)
(* makes the encoding inexact and the models come back QuasiGenuine with *)
(* the caveat attached.  The certainty ladder is in 09_model_finder.sml. *)
(* --------------------------------------------------------------------- *)

val (even_rel_rules, even_rel_ind, even_rel_cases) = Hol_reln `
  (even_rel (0 : num)) /\
  (!n. even_rel n ==> even_rel (n + 2))`;
(* ==> even_rel_cases =                                                  *)
(* ==>   ⊢ ∀a0. even_rel a0 ⇔ a0 = 0 ∨ ∃n. a0 = n + 2 ∧ even_rel n       *)
(*                                                                       *)
(* The `: num` is load-bearing.  Without it the numerals resolve to      *)
(* :rat, rational arithmetic goes through the Frac ersatz encoding of    *)
(* section 6, and every goal below comes back NoCounterexample: the      *)
(* scopes then hold a handful of rationals rather than 0, 1, 2.          *)

val even_rel_pred = ``even_rel : num -> bool``;

refute (upd_expect ExpectGenuine mf) ``even_rel n ==> n = 0``;
(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(* ==>   kodkod, 1.2s):                                                  *)
(* ==>   Scope: card num = 3                                             *)
(* ==>     n = 2                                                         *)
(* ==>   Certification: uncertified                                      *)
(*                                                                       *)
(* That is the shape of every model in sections 1 to 5; only the scope   *)
(* and the bindings are quoted from here on.                             *)

refute (mf |> upd_star_linear_preds false
           |> upd_iter [(SOME even_rel_pred, [2]), (NONE, [0])]
           |> upd_expect ExpectGenuine)
  ``~even_rel 2``;
(* ==> Scope: card num = 3, uncertified.  The goal is closed, so the     *)
(*     model has no bindings: the content is that 2 is reachable within  *)
(*     two unrollings of the base clause.                                *)

refute (mf |> upd_wf [(NONE, SOME false)]
           |> upd_expect ExpectGenuine)
  ``even_rel n ==> n = 0``;
(* ==> Scope: card num = 3, n = 2, uncertified.  Denying                 *)
(*     well-foundedness switches to the unrolled approximation, which    *)
(*     is visible in the model: it now reports                           *)
(*       $var$(even_rel.base) = {0; ... }                                *)
(*       $var$(even_rel.step) = (K $?)⦇2 ↦ {2}; 1 ↦ {2}; 0 ↦ {2}⦈        *)
(*       even_rel ≤ {0; 2; ... }                                         *)
(*     - a lower bound on the predicate rather than an equation.  A      *)
(*     lower bound only makes the premise harder to satisfy, so the      *)
(*     model it yields is still Genuine.                                 *)

refute (mf |> upd_star_linear_preds false
           |> upd_expect ExpectGenuine)
  ``even_rel n ==> n = 0``;
(* ==> Scope: card num = 3, n = 2, uncertified.  Turning exact closure   *)
(*     off costs nothing here; the predicate is still well-founded, so   *)
(*     the direct equation is used either way.                           *)

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

refute (upd_expect ExpectGenuine mf) ``always F``;
(* ==> Scope: iter scratch$always = 0, uncertified.  The scope entry is  *)
(*     the gfp iterator, not a cardinality: the model lives in the type  *)
(*     :'refute$gfpit$scratch$always.  Closed goal, so no bindings; the  *)
(*     model reports λi. always = K $?.                                  *)

refute (mf |> upd_iter [(SOME ``always : bool -> bool``, [2]), (NONE, [0])]
           |> upd_expect ExpectGenuine)
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

refute (upd_expect ExpectGenuine mf)
  ``(xs : num llist) <> llist$LCONS a xs``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: bisim_depth = 1, card num llist = 2, card num = 2        *)
(* ==>     xs = safe_The (λω. ω = 0:::ω)                                 *)
(* ==>     a = 0                                                         *)
(* ==>   Certification: uncertified                                      *)
(*                                                                       *)
(* [safe_The (λω. ω = 0:::ω)] is the cyclic value: the unique list equal *)
(* to [0:::] itself.  The model also prints the reconstructed relation   *)
(* $var$(refute$bisim), indexed by bisimulation depth.  The recheck is   *)
(* what makes the encoding exact, so the verdict is Genuine.             *)

refute (mf |> upd_bisim_depth [~1]
           |> upd_expect ExpectQuasiGenuine)
  ``(xs = llist$LCONS (a : num) xs /\ ys = llist$LCONS a ys) ==> xs = ys``;
(* ==> two models, at the two cardinalities [mf] offers:                 *)
(* ==>   Scope: card num llist = 2, card num = 2                         *)
(* ==>     xs = safe_The (λω. ω = 1:::ω)                                 *)
(* ==>     a = 1                                                         *)
(* ==>     ys = safe_The (λω. ω = 1:::ω)                                 *)
(* ==>   Quasi-genuine:                                                  *)
(* ==>     Try again with "bisim_depth" set to a nonnegative value       *)
(* ==>   ... and the same shape again at card 3 with a = 2.              *)
(*                                                                       *)
(* Note the missing bisim_depth entry, and that the reported enumeration *)
(* of :num llist lists safe_The (λω. ω = 1:::ω) twice.  With the recheck *)
(* off nothing compares those two atoms coinductively, so the "counter-  *)
(* example" may well be two names for one list — which is exactly what   *)
(* QuasiGenuine records, and what its caveat tells you to undo.  A       *)
(* quasi-genuine model does not spend the [max_genuine] budget, which is *)
(* why the search kept going and reported the second scope too.          *)

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

refute (upd_expect ExpectGenuine mf)
  ``t = lbtree$Nd (a : num) t t ==> t = lbtree$Lf``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: bisim_depth = 1, card num lbtree = 2, card num = 2       *)
(* ==>     t = safe_The (λω. ω = Nd 0 ω ω)                               *)
(* ==>     a = 0                                                         *)
(* ==>   Certification: uncertified                                      *)
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

refute (mf |> upd_card [(SOME ``:mirror``, [2]), (NONE, [2])]
           |> upd_expect ExpectGenuine)
  ``mirror_rep (x : mirror) = 0``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card mirror = 2, card num = 2                            *)
(* ==>     x = mirror_abs 1                                              *)
(* ==>   Evaluated terms:                                                *)
(* ==>     mirror_rep x = 1                                              *)
(* ==>     0 = 0                                                         *)
(* ==>   Certification: uncertified                                      *)
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

refute (mf |> upd_card [(SOME ``:num``, [2]), (NONE, [2])]
           |> upd_expect ExpectGenuine)
  ``(x : parity) = y``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card num = 2, card parity = 2                            *)
(* ==>     x = «0»                                                       *)
(* ==>     y = «1»                                                       *)
(* ==>   Certification: uncertified                                      *)
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

refute (upd_expect ExpectGenuine mf) ``(n : num) < 1``;
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

refute (mf |> upd_merge_type_vars true
           |> upd_expect ExpectGenuine)
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
      |> upd_kodkod_sym_break 10
      |> upd_expect ExpectGenuine)
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

refute (mf |> upd_debug true
           |> upd_expect ExpectGenuine)
  ``SUC n = n``;
(* ==> Refute found a counterexample:                                    *)
(* ==>   Scope: card num = 2                                             *)
(* ==>     n = 1                                                         *)
(* ==>   Certified: ⊢ ¬∀n. SUC n = n                                     *)
(*                                                                       *)
(* The only difference visible from here is in the returned stats: two   *)
(* scopes now mean ("batches", 2), where every other section in this     *)
(* file reports ("batches", 1).                                          *)
