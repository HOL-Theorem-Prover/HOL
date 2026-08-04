(* ===================================================================== *)
(*  HolRefute by example, 9: the Kodkod model finder                     *)
(*                                                                       *)
(*  The QC backends run your definitions.  The model finder instead      *)
(*  translates the goal into relational logic over finite scopes and asks *)
(*  a SAT solver for a countermodel.  That reaches statements no test    *)
(*  loop can execute — uninterpreted functions, sets, relations,         *)
(*  underspecified constants — and it reports the cardinalities it used. *)
(*                                                                       *)
(*  Needs a Kodkodi 1.5.7 component and a Java runtime:                  *)
(*                                                                       *)
(*      export HOL4_KODKODI=/path/to/kodkodi-1.5.7                       *)
(*                                                                       *)
(*  Without it every call below answers Unknown ["no configured          *)
(*  backend"], and the expectation each call carries then raises         *)
(*  Refute.expect; see examples/README.                                  *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/09_model_finder.sml                               *)
(*                                                                       *)
(*  Around 46 seconds end to end on an otherwise idle 32-core host: 27   *)
(*  Kodkodi calls ranging from 0.05 to 2.6 seconds, median 1.3, about    *)
(*  35 of those seconds spent inside Kodkodi and most of the rest in     *)
(*  session start-up and the JVM.  Read the figure as machine-dependent  *)
(*  rather than as a promise — it moves with the host, the Java          *)
(*  runtime, and whatever else the machine is doing, and it roughly      *)
(*  doubles when the machine is busy.                                    *)
(*                                                                       *)
(*  Corpus convention: every model-finder call in examples/ pins its     *)
(*  search with [upd_max_threads 1] and an explicit [upd_card] row, so   *)
(*  the scope, bindings and model quoted under each call are exactly     *)
(*  what that call prints.  Unpinned, the finder solves the candidate    *)
(*  scopes in parallel, and where the configuration leaves a choice of   *)
(*  cardinality the winning scope — and hence the model — differs        *)
(*  between runs.  Section 1 opens with the one deliberately unpinned    *)
(*  call in the whole corpus, labelled as such, to show that; every      *)
(*  call after it reproduces exactly.                                    *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* Is the model finder usable in this session?                           *)
Refute_Forl.is_configured ();
(* ==> true on this machine; false if HOL4_KODKODI is unset, and then    *)
(*     every call below answers Unknown.  Note that Refute_Forl is an    *)
(*     implementation module, not part of Refute.sig.                    *)

(* [nitpick] is [refute] restricted to the kodkod backend.  [mf] is the  *)
(* same restriction as a configuration, pinned to one thread so that the *)
(* calls below do not race.                                              *)
val mf = upd_max_threads 1 (upd_backends (SOME ["kodkod"]) (!the_config));

(* --------------------------------------------------------------------- *)
(* 1.  Uninterpreted functions and relations                             *)
(*                                                                       *)
(* There is nothing to run here: [f] and [s] are variables.  The model    *)
(* finder picks small carriers, finds an assignment falsifying the goal,  *)
(* and prints the scope it worked in.                                    *)
(* --------------------------------------------------------------------- *)

val _ = the_config := upd_expect ExpectGenuine (!the_config);

nitpick ``(f : bool -> num) b = 0``;
(* ==> Refute found a counterexample (backend: kodkod, substrate: kodkod):*)
(*       Scope: card num = 6                                             *)
(*         f = (K _)⦇T ↦ 5; F ↦ 4⦈                                       *)
(*         b = T                                                         *)
(*       Evaluated terms: f b = 5 and 0 = 0                              *)
(*       Certified: ⊢ ¬∀f b. f b = 0                                     *)
(*     The [Scope:] line is the cardinality assignment the model lives   *)
(*     in.  This one call is left unpinned on purpose, to show the       *)
(*     scopes racing: at the default row of cardinalities 1 to 10        *)
(*     several of them refute the goal and the first one home wins, so   *)
(*     the scope and the [f] you see will not be the ones quoted above.  *)
(*     It is the only unpinned call in the corpus — every call from      *)
(*     here on fixes [upd_card] and reproduces exactly.                  *)

val _ = the_config := upd_expect NoExpectation (!the_config);

refute (upd_expect ExpectGenuine (upd_card [(NONE, [3])] mf))
  ``(n : num) IN (s : num set)``;
(* ==> Scope: card num = 3, with n = 1 and s = {2},                      *)
(*     Certified: ⊢ ¬∀n s. n ∈ s                                         *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [3])] mf))
  ``(r : num -> num -> bool) x y ==> r y x``;
(* ==> Scope: card num = 3                                               *)
(*       r = (K ?)⦇2 ↦ {1}; 1 ↦ {0; 1}; 0 ↦ {2}⦈                         *)
(*       x = 2, y = 1                                                    *)
(*     and "Certification: uncertified".  The verdict is still Genuine:   *)
(*     it follows from the encoding, which is sound and exact here, not    *)
(*     from whether a theorem was built.  An uninterpreted [r] gives       *)
(*     computeLib nothing to re-evaluate, so [cert] stays NONE.            *)
(*     Section 11 comes back to this.                                      *)

(* --------------------------------------------------------------------- *)
(* 2.  Datatypes and arithmetic                                          *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [2])] mf))
  ``xs <> [] ==> HD (xs : num list) = 0``;
(* ==> Scope: card num list = 2, card num = 2, xs = [1],                 *)
(*     evaluated terms HD xs = 1 and 0 = 0, Certified.                   *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [5])] mf))
  ``REVERSE (xs ++ ys : num list) = REVERSE xs ++ REVERSE ys``;
(* ==> Scope: card num list = 5, card num = 5, xs = [4], ys = [3],       *)
(*     with REVERSE (xs ⧺ ys) = [3; 4] against                           *)
(*     REVERSE xs ⧺ REVERSE ys = [4; 3], Certified.                      *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [2])] mf))
  ``SUC n = n``;
(* ==> Scope: card num = 2, n = 1,                                       *)
(*     Certified: ⊢ ¬∀n. SUC n = n                                       *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [3])] mf))
  ``(i : int) + 1 = i``;
(* ==> Scope: card int = 3, card num = 3, i = -1, Genuine but            *)
(*     "Certification: uncertified": the unary integer encoding gives    *)
(*     a sound model, and computeLib cannot replay it.                   *)

(* --------------------------------------------------------------------- *)
(* 3.  When there is no counterexample in the scope                      *)
(*                                                                       *)
(* Over the finite scopes it checked, the model finder found nothing —    *)
(* which for a genuinely small type is close to a proof, and for an       *)
(* infinite one is exactly as weak as the QC verdicts.                   *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectNone (upd_card [(NONE, [2])] mf))
  ``!b : bool. b \/ ~b``;
(* ==> Refute: no counterexample found within the tested finite bounds   *)
(*     (NoCounterexample).  Here bool really is exhausted — no card row  *)
(*     can make it bigger than its two values.                           *)

(* --------------------------------------------------------------------- *)
(* 4.  Controlling the scopes                                            *)
(*                                                                       *)
(* [upd_card] sets the candidate cardinalities, either for every type     *)
(* (NONE key) or per type.  Small scopes are fast; large ones reach       *)
(* counterexamples that need more elements.  [upd_max] is its             *)
(* per-constructor sibling, at the end of this section.                   *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectNone (upd_card [(NONE, [1, 2])] mf))
  ``!x y z : 'a. x = y \/ y = z \/ x = z``;
(* ==> NoCounterexample: with at most two elements two of x, y, z must   *)
(*     coincide, so the statement holds in every scope checked.          *)

refute (upd_expect ExpectPotential (upd_card [(NONE, [3])] mf))
  ``!x y z : 'a. x = y \/ y = z \/ x = z``;
(* ==> Scope: card α = 3                                                 *)
(*       Skolem constants: x = a1, y = a2, z = a3                        *)
(*       Potential counterexample:                                       *)
(*         evaluation stuck on: $\/                                      *)
(*       …continuing search for a genuine counterexample                 *)
(*     Three distinct elements refute it.  The verdict is Potential      *)
(*     rather than Genuine because an abstract α has no computable       *)
(*     equality, so the witness cannot be re-evaluated in HOL.           *)

refute (upd_expect ExpectGenuine
          (upd_card [(SOME ``:num``, [8]), (NONE, [2])] mf))
  ``(n : num) < 5``;
(* ==> Scope: card unsigned_bit bitword = 8, card unsigned_bit = 3,      *)
(*     n = 6, Certified: ⊢ ¬∀n. n < 5                                    *)
(*     The per-type row wins over the NONE fallback row — but with the   *)
(*     default [binary_ints], which is "use them where they help", the   *)
(*     8 arrives as the size of the binary carrier for :num rather than  *)
(*     as a card num entry, and the witness is whichever value of that   *)
(*     carrier the solver picked.  Section 9 is about that encoding.     *)

refute
  (mf |> upd_binary_ints (SOME false)
      |> upd_card [(SOME ``:num``, [8]), (NONE, [2])]
      |> upd_expect ExpectGenuine)
  ``(n : num) < 5``;
(* ==> Scope: card num = 8, n = 7, Certified: ⊢ ¬∀n. n < 5               *)
(*     Forcing the unary encoding puts the same row back on :num itself. *)

(* [upd_max] bounds a scope from the other side.  Its rows are keyed by   *)
(* constructor rather than by type, and say how many values that          *)
(* constructor may contribute to its type's carrier; ~1, the default, is  *)
(* unbounded.  The constructor is written with its result type because    *)
(* a row is matched by name and result type together.                    *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [4])] mf))
  ``LENGTH (xs : num list) < 2``;
(* ==> Scope: card num list = 4, card num = 4                            *)
(*       xs = [0; 0]                                                     *)
(*     Certified: ⊢ ¬∀xs. LENGTH xs < 2                                  *)

refute
  (mf |> upd_card [(NONE, [4])]
      |> upd_max [(SOME ``CONS : num -> num list -> num list``, [1])]
      |> upd_expect ExpectNone)
  ``LENGTH (xs : num list) < 2``;
(* ==> NoCounterexample                                                  *)
(*     One cons cell cannot build a two-element list, so bounding CONS   *)
(*     removes the counterexample while leaving the requested            *)
(*     cardinality alone — which is what [upd_card] on its own has no    *)
(*     way to say.                                                       *)

refute
  (mf |> upd_card [(NONE, [4])]
      |> upd_max [(SOME ``CONS : num -> num list -> num list``, [2])]
      |> upd_expect ExpectGenuine)
  ``LENGTH (xs : num list) < 2``;
(* ==> Scope: card num list = 3, card num = 4                            *)
(*       xs = [2; 0]                                                     *)
(*     Certified: ⊢ ¬∀xs. LENGTH xs < 2                                  *)
(*     Two cons cells are enough again, and the list carrier is now 3    *)
(*     rather than the 4 that was asked for: two values from CONS plus   *)
(*     [] is everything the type can hold under that bound.  That is     *)
(*     what "contribute to its type's carrier" means — the bound is on   *)
(*     the constructor, and the carrier follows.                         *)

(* --------------------------------------------------------------------- *)
(* 5.  Reading the model                                                 *)
(*                                                                       *)
(* By default the report shows the bindings and any Skolem constants      *)
(* (section 4 above printed some).  [upd_show_types] adds the carrier of  *)
(* each type, [upd_show_consts] the interpretations of the constants      *)
(* involved, and [upd_format] groups curried arguments of a model         *)
(* function into tuples.                                                 *)
(* --------------------------------------------------------------------- *)

refute
  (mf |> upd_show_types true
      |> upd_show_consts true
      |> upd_show_skolems true
      |> upd_card [(NONE, [3])]
      |> upd_expect ExpectGenuine)
  ``xs <> [] ==> HD (xs : num list) = 0``;
(* ==> Scope: card num list = 3, card num = 3 with xs = [2], plus        *)
(*       Types:                                                          *)
(*         num list = {[], [2], [1], ...}                                *)
(*         num = {0, 1, 2, ...}                                          *)
(*       Constants:                                                      *)
(*         HD = (K ?)⦇[] ↦ 2; [2] ↦ 2⦈                                   *)
(*     The trailing "..." marks a carrier that is a fragment of an        *)
(*     infinite type.  No Skolem constants here: nothing was skolemised.  *)

refute (upd_expect ExpectGenuine (upd_card [(NONE, [2])] mf))
  ``(r : num -> num -> bool) x y ==> r y x``;
(* ==> Scope: card num = 2, with x = 1, y = 0, and                       *)
(*     r = (K ?)⦇1 ↦ {0; 1}; 0 ↦ ∅⦈ : curried, one argument at a time.   *)

refute (upd_expect ExpectGenuine
          (upd_format [(NONE, [2])] (upd_card [(NONE, [2])] mf)))
  ``(r : num -> num -> bool) x y ==> r y x``;
(* ==> r = (K ?)⦇(1,1) ↦ T; (1,0) ↦ T⦈ : the same relation with its two  *)
(*     arguments grouped into a pair.                                    *)

(* --------------------------------------------------------------------- *)
(* 6.  Several models at once                                            *)
(*                                                                       *)
(* [upd_max_genuine] and [upd_max_potential] are the global budgets on    *)
(* how many models the search returns; asking for more than one switches  *)
(* to an incremental SAT solver when necessary.  They are the model-      *)
(* finder budgets: [upd_max_counterexamples] governs the QC backends and  *)
(* does not cap this list.                                               *)
(*                                                                       *)
(* The two budgets are not interchangeable.  [max_genuine] bounds the     *)
(* models of a soundly encoded problem — every one of them, whatever      *)
(* certainty its reconstruction lands on.  [max_potential] bounds only    *)
(* the models that may be spurious because the *encoding* behind them is  *)
(* unsound, so on a sound problem raising it changes nothing.             *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine
          (upd_max_genuine 3 (upd_card [(NONE, [3])] mf)))
  ``SUC n = n``;
(* ==> three certified counterexamples in one report, all at             *)
(*     Scope: card num = 3, with n = 1, n = 2 and n = 0.                 *)

refute (upd_expect ExpectGenuine
          (upd_max_genuine 3 (upd_card [(NONE, [3])] mf)))
  ``(r : num -> num -> bool) x y ==> r y x``;
(* ==> three models, all at Scope: card num = 3 with x = 2 and y = 1,    *)
(*     differing in r: (K ?)⦇2 ↦ {0; 1}; 1 ↦ {1}; 0 ↦ {1}⦈, then         *)
(*     (K ?)⦇2 ↦ {1}; 1 ↦ {0; 1}; 0 ↦ {2}⦈, then                         *)
(*     (K ?)⦇2 ↦ {1; 2}; 1 ↦ {0}; 0 ↦ {2}⦈.  Each is Genuine and         *)
(*     uncertified, as in section 1, so each spends a [max_genuine]      *)
(*     slot; with [upd_max_potential 3] instead only the first comes     *)
(*     back, because this encoding is sound and no potential budget is   *)
(*     in play.                                                          *)

(* --------------------------------------------------------------------- *)
(* 7.  Models instead of counterexamples                                 *)
(*                                                                       *)
(* [upd_falsify false] asks for an assignment satisfying the goal rather  *)
(* than refuting it, and the report says "model" instead of               *)
(* "counterexample".  Handy for sanity-checking that a definition is      *)
(* satisfiable at all.                                                   *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine
          (upd_falsify false (upd_card [(NONE, [2, 3])] mf)))
  ``(r : 'a -> 'a -> bool) x y /\ ~r y x``;
(* ==> Refute found a model (backend: kodkod, substrate: kodkod):        *)
(*       Scope: card α = 2                                               *)
(*         r = (K _)⦇a2 ↦ {a1; a2}; a1 ↦ ∅⦈                              *)
(*         x = a2, y = a1                                                *)
(*       Certification: uncertified                                      *)
(*     Both offered cardinalities admit a model; pinned to one thread    *)
(*     the smaller is solved first, so it is the one reported.           *)
(*     "model" replaces "counterexample" throughout the report.  There    *)
(*     is nothing to certify — a certificate proves the negation of the  *)
(*     goal, which is not what was asked for — so [cert] is NONE while    *)
(*     the encoding still makes the verdict Genuine.  Had the            *)
(*     reconstruction come out weaker, the report would have read         *)
(*     "Potential model" rather than "Potential counterexample".          *)

(* --------------------------------------------------------------------- *)
(* 8.  Steering the search                                               *)
(*                                                                       *)
(*   upd_whack   drop the definitions of named constants, leaving them    *)
(*               uninterpreted — a way past a definition that blows up    *)
(*               the translation, at the price of a weaker formula.       *)
(*   upd_need    insist that particular values occur in the model.        *)
(*   upd_atoms   name the atoms of a type, so models read nicely.         *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectUnknown
          (upd_whack [``$+ : num -> num -> num``]
             (upd_card [(NONE, [3])] mf)))
  ``(x : num) + y = y``;
(* ==> Unknown ["kodkod: formula was semantically weakened by whack      *)
(*     after checking 1 of 1 scopes"].  Whacking [+] leaves the goal     *)
(*     talking about a constant the translation no longer interprets,    *)
(*     so the search gives up rather than call the absence of a model    *)
(*     an answer.  Whack is a translation-debugging tool, not a way to   *)
(*     get answers about a constant the goal actually uses.              *)

refute (upd_expect ExpectGenuine
          (upd_need (SOME [``3 : num``]) (upd_card [(NONE, [5])] mf)))
  ``(n : num) < 3``;
(* ==> Scope: card num = 5, n = 4, Certified: ⊢ ¬∀n. n < 3               *)
(*     The needed value 3 fits: the carrier is {0, 1, 2, 3, 4}.          *)

refute (upd_expect ExpectNone
          (upd_need (SOME [``[2; 2] : num list``])
             (upd_card [(NONE, [2])] mf)))
  ``LENGTH (xs : num list) <> 2``;
(* ==> "Refute warning: the conjecture either holds for the given scopes  *)
(*     or lies outside the supported fragment", then NoCounterexample:    *)
(*     no two-element scope can contain [2; 2], so the demand makes the   *)
(*     problem trivially false.  Without the [need] the same call is      *)
(*     simply NoCounterexample, with no warning; at card 3 both find      *)
(*     xs = [2; 2].                                                      *)

refute
  (mf |> upd_atoms [(SOME ``:'a``, ["a", "b", "c"])]
      |> upd_card [(NONE, [3])]
      |> upd_expect ExpectPotential)
  ``!x y : 'a. x = y``;
(* ==> Scope: card α = 3                                                 *)
(*       Skolem constants:                                               *)
(*         x = a                                                         *)
(*         y = b                                                         *)
(*       Potential counterexample:                                       *)
(*         evaluation stuck on: x                                        *)
(*       …continuing search for a genuine counterexample                 *)
(*     The supplied names replace the default a1, a2, a3.  The verdict   *)
(*     is Potential for the reason section 4 gives and section 11        *)
(*     generalises: an abstract α has no computable equality, so the     *)
(*     witness cannot be re-evaluated.                                   *)

(* --------------------------------------------------------------------- *)
(* 9.  Integers: unary or binary                                         *)
(*                                                                       *)
(* Integers are represented unarily by default.  [upd_binary_ints] turns  *)
(* on the binary encoding (NONE lets Refute decide, SOME forces), and     *)
(* [upd_bits] bounds the word widths it may try.                         *)
(* --------------------------------------------------------------------- *)

refute
  (mf |> upd_binary_ints (SOME true)
      |> upd_bits [2, 3]
      |> upd_card [(NONE, [3])]
      |> upd_expect ExpectGenuine)
  ``(i : int) * 2 = i``;
(* ==> Scope: card signed_bit bitword = 3, card signed_bit = 3,          *)
(*     with i = 1 and "Certification: uncertified".  The scope line      *)
(*     names the bitword types the binary encoding introduces, in place  *)
(*     of card int.  Narrowing [bits] is a cost control, not a semantic  *)
(*     one: the default row of widths 1 to 10 returns the same model     *)
(*     here, in about the same time.                                     *)

(* --------------------------------------------------------------------- *)
(* 10.  Solver and effort                                                *)
(*                                                                       *)
(* SAT4J is the portable default; JNI and external solvers are advertised *)
(* only when their libraries or *_HOME variables are present.             *)
(* [upd_batch_size] controls how many scopes go to the solver at a time,  *)
(* [upd_max_threads] caps parallelism (0 = unrestricted), and             *)
(* [upd_tac_timeout] bounds the inner tactic calls (0 skips them).        *)
(* [mf] already sets [upd_max_threads 1], as the corpus convention        *)
(* requires; the call below repeats it to show the option in use.         *)
(* --------------------------------------------------------------------- *)

refute
  (mf |> upd_sat_solver "SAT4J"
      |> upd_batch_size 8
      |> upd_max_threads 1
      |> upd_tac_timeout 1.0
      |> upd_timeout 60.0
      |> upd_card [(NONE, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
      |> upd_expect ExpectGenuine)
  ``xs <> [] ==> TL (xs : num list) = []``;
(* ==> Scope: card num list = 3, card num = 3, xs = [2; 2],              *)
(*     with TL xs = [2] against [] = [], Certified.  The ten scopes of   *)
(*     the pinned row reach SAT4J in two batches, [batch_size] capping   *)
(*     each at eight.                                                    *)

(* --------------------------------------------------------------------- *)
(* 11.  Genuine, potential, and certificates                             *)
(*                                                                       *)
(* A model-finder verdict is decided by the translation, never by         *)
(* whether a theorem was built: the encoding's soundness and exactness    *)
(* flags map onto Genuine, QuasiGenuine and Potential.  Refute trusts     *)
(* Kodkodi here exactly as Isabelle's Nitpick trusts Kodkod.  So          *)
(* [certainty] tells you the semantic strength and [cert] tells you       *)
(* whether a HOL theorem exists — they are independent, and "genuine,     *)
(* uncertified" is a normal answer rather than a hedge.  What does pull   *)
(* a model down to Potential is a goal Refute did try to certify and got  *)
(* stuck on: the kernel then contradicts nothing but confirms nothing     *)
(* either, and its complaint replaces the encoding's verdict.  A goal     *)
(* with nothing executable in it, like the relation of section 1, is      *)
(* never taken to the kernel at all, so its encoding has the last word.   *)
(* --------------------------------------------------------------------- *)

fun verdict tm =
  case refute (upd_expect ExpectCex
                 (upd_quiet true (upd_card [(NONE, [3])] mf))) tm of
      Counterexample (cex :: _) =>
        (case (#certainty cex, #cert cex) of
             (Genuine, SOME _) => "genuine, certified"
           | (Genuine, NONE) => "genuine, uncertified"
           | (QuasiGenuine _, _) => "quasi-genuine"
           | (Potential reasons, _) =>
               "potential: " ^ String.concatWith "; " reasons)
    | Counterexample [] => "counterexample list was empty"
    | NoCounterexample => "none in scope"
    | Unknown reasons => "unknown: " ^ String.concatWith "; " reasons;

verdict ``SUC n = n``;
(* ==> "genuine, certified": the witness evaluates, so Refute proved      *)
(*     ⊢ ¬∀n. SUC n = n.                                                 *)

verdict ``(r : num -> num -> bool) x y ==> r y x``;
(* ==> "genuine, uncertified": section 1's relation again, seen through   *)
(*     the two fields rather than through the report.                     *)

verdict ``?n : num. n <> n``;
(* ==> "potential: evaluation stuck on: $?": the goal is false, so any    *)
(*     scope refutes it, and this one Refute does try to certify — but    *)
(*     the negation of an existential over an infinite type is not        *)
(*     something computeLib can settle, so the attempt reports where it   *)
(*     stopped and the verdict follows it down to Potential.              *)
