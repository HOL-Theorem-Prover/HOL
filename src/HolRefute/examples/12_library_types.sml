(* ===================================================================== *)
(*  HolRefute by example, 12: types from the standard library            *)
(*                                                                       *)
(*  Integers, characters and strings, machine words, rationals and       *)
(*  finite maps.  For each of them: which half of Refute can say         *)
(*  anything, how strong the answer is, and what the report looks like   *)
(*  when a type is out of reach altogether.                              *)
(*                                                                       *)
(*  Sections 4 and 5 are model-finder only; sections 2 and 3 close with  *)
(*  one model-finder call each, and section 6 with two.  All ten need a  *)
(*  Kodkodi component (see 09_model_finder.sml).  Without one they       *)
(*  answer Unknown ["no configured backend"], and the expectation each   *)
(*  carries then raises Refute.expect — except in section 3, whose call  *)
(*  expects an Unknown anyway.  See examples/README.                     *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/12_library_types.sml                              *)
(* ===================================================================== *)

load "Refute";
load "intLib";
open Refute;

(* [refuteheap] already parses every type below, so no further theory    *)
(* has to be loaded to state the goals.  [intLib] is loaded for a        *)
(* different reason: it is what puts integer arithmetic into computeLib. *)
(* Without it section 1 answers Unknown ["not executable: $&"] instead   *)
(* of testing anything, which is the general rule for the QC half — a    *)
(* type is executable exactly as far as its evaluation theorems have     *)
(* been loaded.                                                          *)

(* Two configurations serve the whole file.  [qc] is the enumerating     *)
(* half.  Naming its two backends rather than taking the default keeps   *)
(* the reason lists quoted below exactly as printed; narrowing is        *)
(* 06_narrowing.sml's subject and contributes reasons of its own.  [mf]  *)
(* is the model finder, pinned to a single Kodkodi thread as the corpus  *)
(* convention requires — see the header of 10_model_finder_advanced.sml  *)
(* — with every call adding its own explicit [upd_card] row.             *)

val qc = upd_backends (SOME ["exhaustive", "random"]) (!the_config);

val mf = !the_config
  |> upd_backends (SOME ["kodkod"])
  |> upd_max_threads 1;

(* --------------------------------------------------------------------- *)
(* 1.  Integers: served by both halves                                   *)
(*                                                                       *)
(* :int is the comfortable case.  computeLib runs integer arithmetic, so *)
(* the QC backends can test the goal, and the model finder has an        *)
(* encoding for :int as well, so either half will answer.                *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine qc) ``(i : int) + 1 = i``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       i = -1                                                          *)
(*     Certified: |- ~!i. i + 1 = i                                      *)

refute (upd_expect ExpectGenuine qc) ``(i : int) - j = j - i``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       i = -1                                                          *)
(*       j = 0                                                           *)
(*     Evaluated terms:                                                  *)
(*       i - j = -1                                                      *)
(*       j - i = 1                                                       *)
(*     Certified: |- ~!i j. i - j = j - i                                *)

(* Section 2 of 09_model_finder.sml puts the first of those goals to the *)
(* model finder instead, at card int = 3, and section 9 there runs :int  *)
(* through the binary encoding; neither is repeated here.  What is worth *)
(* carrying away is the difference in the closing line.  The model       *)
(* finder reports Genuine but uncertified — a unary integer model is not *)
(* something computeLib can replay — whereas the calls above come back   *)
(* with a HOL theorem.  Where both halves serve a type, the QC half is   *)
(* the one that leaves you something to keep.                            *)

(* --------------------------------------------------------------------- *)
(* 2.  Characters and strings: executable, and only that                 *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine qc) ``(s : string) ++ "a" = s``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       s = ""                                                          *)
(*     Certified: |- ~!s. STRCAT s "a" = s                               *)

(* The empty string is the smallest witness and the very first test      *)
(* reaches it: the smallest-first enumeration that gives section 1 of    *)
(* 01_first_steps.sml its x = 0.                                         *)

refute (upd_expect ExpectGenuine qc) ``ORD (c : char) < 60``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 10):                *)
(*       c = #"<"                                                        *)
(*     Certified: |- ~!c. ORD c < 60                                     *)

(* #"<" is character 60, so :char is enumerated by code point.  The size *)
(* figure in that report is not what decided how far the run got: :char  *)
(* is finite, 256 values, and the exhaustive backend walks the whole     *)
(* carrier — 61 tests here — whatever size it is given.  Shrinking the   *)
(* bound to 1 therefore changes nothing, which is the opposite of what   *)
(* section 6 of 03_datatypes_and_functions.sml shows for the infinite    *)
(* :num, where size really is the reach.                                 *)

refute (upd_expect ExpectGenuine (upd_size 1 qc)) ``ORD (c : char) < 60``;

(* ==> the same c = #"<", now reported at size 1                         *)

(* The model finder has little to offer here, and says so honestly       *)
(* rather than wrongly.  A string is a list of characters, and at the    *)
(* cardinalities that keep such a translation tractable the scope holds  *)
(* no witness at all.                                                    *)

refute (mf |> upd_card [(NONE, [2])] |> upd_expect ExpectNone)
  ``(s : string) <> ""``;

(* ==> Refute: no counterexample found within the tested finite bounds   *)
(*     (NoCounterexample)                                                *)

(* That is a statement about the two-element scope, not about the goal,  *)
(* which is plainly false.  A string conjecture belongs to quickcheck.   *)

(* --------------------------------------------------------------------- *)
(* 3.  Machine words, and a numeral trap                                 *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine qc) ``(w : word8) + 1w <> 0w``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 10):                *)
(*       w = 255w                                                        *)
(*     Certified: |- ~!w. w + 1w <> 0w                                   *)

refute (upd_expect ExpectGenuine qc) ``(w : word4) + 1w <> 0w``;

(* ==> the same goal one type narrower:                                  *)
(*       w = 15w                                                         *)
(*     Certified: |- ~!w. w + 1w <> 0w                                   *)

(* The witness is the type's own maximum in both cases, and nothing in   *)
(* the goal text mentions a width: the modulus is respected by the       *)
(* generator, which enumerates the carrier of :word8 and of :word4       *)
(* alike, rather than by anything the conjecture says.                   *)

(* The practical trap is in the numerals.  Written with a bare 1 in      *)
(* place of 1w the term does not parse at all, and the complaint comes   *)
(* from HOL's type inference before Refute is reached — it is not a      *)
(* Refute failure, though it is the first thing a reader hits.  The      *)
(* exception below is deliberate; it and the two in section 5 of         *)
(* 01_first_steps.sml and section 8 of 02_verdicts_and_config.sml are    *)
(* the only ones this corpus expects, and the handler prints it so that  *)
(* the transcript carries on.  Section 5 of 06_narrowing.sml documents   *)
(* the sibling trap, where bare :num numerals resolve to :rat instead.   *)

refute (upd_expect ExpectGenuine qc) ``(w : word8) + 1 <> 0w``
  handle e => (Feedback.HOL_MESG (Feedback.exn_to_string e);
               NoCounterexample);

(* ==> Exception raised at Preterm.type-analysis: at line …,             *)
(*     character …:                                                      *)
(*       Couldn't infer a type for the numeric literal `1`               *)
(*     then val it = NoCounterexample: outcome                           *)
(*     (the elided position is that of the bare numeral just above)      *)

(* The model finder declines word goals, and names what it is missing.   *)

refute (mf |> upd_card [(NONE, [2, 3])] |> upd_expect ExpectUnknown)
  ``(w : word8) + 1w <> 0w``;

(* ==> Refute could not determine an answer                              *)
(*     Reasons:                                                          *)
(*       kodkod: unregistered typedef cart: register with                *)
(*         Refute.register_typedef                                       *)

(* Words are built on the cart typedef, which the model finder has not   *)
(* harvested, and the report names both the missing registration and the *)
(* function that would supply it — section 4 of                          *)
(* 10_model_finder_advanced.sml is that function in use.  Registering    *)
(* cart is left to the reader: the QC path already answers word goals,   *)
(* and answers them with a certificate.                                  *)

(* --------------------------------------------------------------------- *)
(* 4.  Rationals: model finder only                                      *)
(*                                                                       *)
(* Rational arithmetic has no computeLib equations to run, so every QC   *)
(* backend declines before testing anything.                             *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectUnknown qc) ``(r : rat) + 1 = r``;

(* ==> Refute could not determine an answer                              *)
(*     Reasons:                                                          *)
(*       not executable: $+                                              *)
(*     val it = Unknown ["not executable: $+"]                           *)

(* The model finder does not need them: it encodes :rat through the      *)
(* built-in Frac representation, which section 5 takes apart.            *)

refute (mf |> upd_card [(NONE, [3])] |> upd_expect ExpectGenuine)
  ``(r : rat) + 1 = r``;

(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(*     kodkod):                                                          *)
(*       Scope: card int = 3, card num = 3, card rat = 3                 *)
(*         r = 0 // 1                                                    *)
(*       Certification: uncertified                                      *)

refute (mf |> upd_card [(NONE, [4])] |> upd_expect ExpectGenuine)
  ``!r : rat. r + r <> 1``;

(* ==> Scope: card int = 4, card num = 4, card rat = 4                   *)
(*       Skolem constants:                                               *)
(*         r = 1 // 2                                                    *)
(*     Certification: uncertified                                        *)

refute (mf |> upd_card [(NONE, [3])] |> upd_expect ExpectGenuine)
  ``(r : rat) < s ==> r + 1 < s``;

(* ==> Scope: card int = 3, card num = 3, card rat = 3                   *)
(*       r = -1 // 1                                                     *)
(*       s = 0 // 1                                                      *)
(*     Certification: uncertified                                        *)

(* Three things to read out of those.  A rational scope drags in an int  *)
(* scope and a num scope, because the encoding is built on them.  The // *)
(* in the witnesses is not raw model output but the built-in term        *)
(* postprocessor that [register_frac_type_rat] installs — the display    *)
(* registry of section 6 of 10_model_finder_advanced.sml — and 1 // 2 is *)
(* a genuine non-integer witness, which no :int scope could have         *)
(* produced.  And every one of these is Genuine with cert = NONE.  That  *)
(* is the pair of axes section 11 of 09_model_finder.sml separates, on a *)
(* type where the QC half cannot help at all: no certificate is to be    *)
(* had here, and the verdict is full strength regardless, because it     *)
(* follows from the encoding rather than from the kernel.                *)

(* --------------------------------------------------------------------- *)
(* 5.  register_frac_type, on the type it ships for                      *)
(*                                                                       *)
(* [register_frac_type] is the general entry point behind that encoding: *)
(* it declares a type to be a field of fractions and maps its arithmetic *)
(* onto the surrogates Refute knows how to translate.  Rather than       *)
(* invent a fraction type, the three steps below re-register :rat,       *)
(* which is exactly what [register_frac_type_rat ()] does for you.       *)
(*                                                                       *)
(* Registering an ersatz table asserts that each surrogate denotes the   *)
(* same function as the constant it replaces, and nothing checks that —  *)
(* the same contract section 4 of 11_extending_refute.sml states for     *)
(* [register_ersatz].  Step 2 breaks it deliberately.                    *)
(* --------------------------------------------------------------------- *)

fun rat_ersatz pairs =
  map (fn (original, replacement) =>
         {original = {Thy = "rat", Name = original},
          replacement = {Thy = "refute", Name = replacement}})
      pairs;

(* Step 1: the whole table, twelve rat constants against their           *)
(* refute$*_frac surrogates.                                             *)

register_frac_type
  {tyop = {Thy = "rat", Tyop = "rat"},
   ersatz = rat_ersatz
     [("rat_0", "zero_frac"), ("rat_1", "one_frac"),
      ("rat_ainv", "uminus_frac"), ("rat_minv", "inverse_frac"),
      ("rat_add", "plus_frac"), ("rat_sub", "subtract_frac"),
      ("rat_mul", "times_frac"), ("rat_div", "divide_frac"),
      ("rat_les", "less_frac"), ("rat_leq", "less_eq_frac"),
      ("rat_of_num", "of_num_frac"), ("rat_cons", "frac")]};
(* ==> val it = (): unit                                                 *)

refute (mf |> upd_card [(NONE, [3])] |> upd_expect ExpectGenuine)
  ``(r : rat) + 1 = r``;

(* ==> exactly section 4's first answer:                                 *)
(*       Scope: card int = 3, card num = 3, card rat = 3                 *)
(*         r = 0 // 1                                                    *)
(*       Certification: uncertified                                      *)

(* Step 2: the same registration with all but one entry left out.        *)

register_frac_type
  {tyop = {Thy = "rat", Tyop = "rat"},
   ersatz = rat_ersatz [("rat_add", "plus_frac")]};
(* ==> val it = (): unit                                                 *)

refute (mf |> upd_card [(NONE, [3])] |> upd_expect ExpectPotential)
  ``(r : rat) + 1 = r``;

(* ==> Refute warning: the conjecture either holds for the given scopes  *)
(*     or lies outside the supported fragment; only potentially spurious *)
(*     models may be found                                               *)
(*     Refute found a counterexample (backend: kodkod, substrate:        *)
(*     kodkod):                                                          *)
(*       Scope: card frac = 3, card int = 3, card num = 3,               *)
(*              card rat = 3                                             *)
(*         r = -1 // 1                                                   *)
(*       …continuing search for a genuine counterexample                 *)

(* One incomplete registration, three observable consequences.  The      *)
(* scope now exposes card frac beside card rat, because the constants    *)
(* left unmapped force the raw frac representation into the model.  The  *)
(* run warns that only potentially spurious models may be found.  And    *)
(* the verdict falls out of Genuine to Potential.                        *)
(*                                                                       *)
(* This is what [max_potential] is for.  Section 6 of                    *)
(* 09_model_finder.sml explains that it bounds models whose *encoding*   *)
(* is unsound, and that on a sound problem raising it changes nothing;   *)
(* every problem in that file is sound, so the other case never shows.   *)
(* Here the encoding really is unsound, and this is the model that would *)
(* spend the budget.                                                     *)

(* Step 3: put the built-in registration back.                           *)

register_frac_type_rat ();
(* ==> val it = (): unit                                                 *)

refute (mf |> upd_card [(NONE, [3])] |> upd_expect ExpectGenuine)
  ``(r : rat) + 1 = r``;

(* ==> step 1's report again, card frac gone from the scope:             *)
(*       Scope: card int = 3, card num = 3, card rat = 3                 *)
(*         r = 0 // 1                                                    *)
(*       Certification: uncertified                                      *)
(*                                                                       *)
(* Which is the "idempotent entry point restores or refreshes" line of   *)
(* Refute.sig, watched rather than read.                                 *)

(* --------------------------------------------------------------------- *)
(* 6.  Finite maps: not supported, and how you can tell                  *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectUnknown qc)
  ``FLOOKUP (fm : num |-> num) 0 = SOME 0``;

(* ==> Refute could not determine an answer                              *)
(*     Reasons:                                                          *)
(*       exhaustive: native: no generator for :num |-> num - no          *)
(*         constructors in TypeBase; register a generator                *)
(*       exhaustive: cv: cv: :num |-> num - no constructors in           *)
(*         TypeBase; register a generator                                *)
(*       exhaustive: compute: no generator for :num |-> num - no         *)
(*         constructors in TypeBase; register a generator                *)
(*       ... and the same three reasons again for random                 *)
(*                                                                       *)
(* One reason per backend and substrate pair, each naming the capability *)
(* that is missing.  :num |-> num has no constructors in TypeBase, so    *)
(* nothing can enumerate it.                                             *)

(* The model finder does not decline — it answers, and the answer is     *)
(* vacuous.                                                              *)

refute (mf |> upd_card [(NONE, [2])] |> upd_expect ExpectNone)
  ``FLOOKUP (fm : num |-> num) 0 = SOME 0``;

(* ==> Refute: no counterexample found within the tested finite bounds   *)
(*     (NoCounterexample)                                                *)

refute (mf |> upd_card [(NONE, [2])]
           |> upd_falsify false
           |> upd_expect ExpectNone)
  ``FLOOKUP (fm : num |-> num) 0 = SOME 0``;

(* ==> Refute: no model found within the tested finite bounds            *)
(*     (NoCounterexample)                                                *)

(* Asked to refute the goal and asked to satisfy it, the same scope      *)
(* comes back empty both times, which is how you can tell that it holds  *)
(* no finite maps at all rather than that the conjecture survived        *)
(* scrutiny — the goal is false, FEMPTY refutes it.  "Within the tested  *)
(* finite bounds" is a claim about the bounds, and when a type is not    *)
(* modelled the bounds are empty and the claim is worth nothing.  The    *)
(* second call is section 7 of 09_model_finder.sml's [upd_falsify false] *)
(* used as a diagnostic.                                                 *)

(* That is the closing lesson of the file.  An Unknown naming a missing  *)
(* capability is how Refute reports the edge of what it can do.  It is   *)
(* never a statement about the conjecture, and the reasons list is where *)
(* to look for what would move the edge — a generator here, a typedef    *)
(* registration in section 3, an ersatz table in section 5.  Section 4   *)
(* of 02_verdicts_and_config.sml makes the same point for :ind, where    *)
(* the QC backends decline for want of a generator and the model finder  *)
(* then answers the goal outright.                                       *)
