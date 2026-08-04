(* ===================================================================== *)
(*  HolRefute by example, 3: your own datatypes and definitions          *)
(*                                                                       *)
(*  Refuting conjectures about freshly defined types and recursive       *)
(*  functions: trees, records, options, pairs, sets, and polymorphic     *)
(*  statements.  Also the two knobs that decide how far the search       *)
(*  reaches: size and the treatment of type variables.                   *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/03_datatypes_and_functions.sml                    *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* The default substrate choice, Auto, lets each QC backend pick the   *)
(* first substrate that accepts the goal, and the cv substrate defines *)
(* and cv-translates a fresh test loop per call — a screenful of       *)
(* "Definition has been stored under ..." feedback every time.  None   *)
(* of the points below depend on that, so pin the native substrate     *)
(* once and keep the transcript readable.  It also carries the         *)
(* expectation for the [refute_def] calls below, which take no         *)
(* configuration argument; the explicit [refute] calls each override   *)
(* it.  Substrates are the actual subject of                           *)
(* 04_substrates_and_determinism.sml.                                  *)

val _ = the_config := (!the_config
                         |> upd_substrate NativeSML
                         |> upd_expect ExpectGenuine);

(* --------------------------------------------------------------------- *)
(* 1.  A binary search tree and two functions over it                    *)
(*                                                                       *)
(* Nothing here is special to Refute: define types and functions exactly *)
(* as you would in any theory script.  Refute reads the datatype from    *)
(* TypeBase and the equations from the definition database.              *)
(* --------------------------------------------------------------------- *)

val _ = Datatype `btree = Leaf | Branch btree num btree`;

val insert_def = Define `
  (insert x Leaf = Branch Leaf x Leaf) /\
  (insert x (Branch l v r) =
     if x < v then Branch (insert x l) v r
     else if v < x then Branch l v (insert x r)
     else Branch l v r)`;

val flatten_def = Define `
  (flatten Leaf = []) /\
  (flatten (Branch l v r) = flatten l ++ [v] ++ flatten r)`;

(* --------------------------------------------------------------------- *)
(* 2.  A plausible-looking lemma that is false                           *)
(*                                                                       *)
(* Inserting does not append: the new element lands in the middle.  The  *)
(* counterexample names the smallest tree and element that show it, and  *)
(* the "Evaluated terms" block shows the two sides diverging.            *)
(* --------------------------------------------------------------------- *)

refute_def ``flatten (insert x t) = flatten t ++ [x]``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 2):                 *)
(*       x = 0                                                           *)
(*       t = Branch Leaf 0 Leaf                                          *)
(*     Evaluated terms:                                                  *)
(*       flatten (insert x t) = [0]                                      *)
(*       flatten t ++ [x] = [0; 0]                                       *)
(*     Certified: |- ~!x t. flatten (insert x t) = flatten t ++ [x]      *)

(* --------------------------------------------------------------------- *)
(* 3.  A lemma that is false only because an invariant is missing        *)
(*                                                                       *)
(* [flatten t] is sorted for search trees, but [t] here is an arbitrary  *)
(* tree, and Refute happily builds an unsorted one.  This is the usual   *)
(* way a "surely this holds" lemma turns out to need a hypothesis; see   *)
(* 07_custom_generators.sml for how to restrict generation to the        *)
(* well-formed trees instead.                                            *)
(*                                                                       *)
(* The exhaustive backend reaches the smallest such tree first, so the   *)
(* witness is a fully ground one.  Narrowing would report the same tree  *)
(* with a hole in the subtree it never inspected; 06_narrowing.sml       *)
(* selects that backend by name to show it.                              *)
(* --------------------------------------------------------------------- *)

refute_def ``SORTED (<) (flatten t)``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 3):                 *)
(*       t = Branch Leaf 0 (Branch Leaf 0 Leaf)                          *)
(*     Certified: |- ~!t. SORTED $< (flatten t)                          *)

(* --------------------------------------------------------------------- *)
(* 4.  Records                                                           *)
(*                                                                       *)
(* Record types come from Datatype like any other, and both the field    *)
(* accessors and the field-update syntax are available in goals.         *)
(* --------------------------------------------------------------------- *)

val _ = Datatype `point = <| px : num ; py : num |>`;

refute_def ``(p : point).px = p.py``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 2):                 *)
(*       p = point 0 1                                                   *)
(*     Evaluated terms:                                                  *)
(*       p.px = 0                                                        *)
(*       p.py = 1                                                        *)
(*     Certified: |- ~!p. p.px = p.py                                    *)

refute_def ``((p : point) with px := 1).px = p.px``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       p = point 0 0                                                   *)
(*     Evaluated terms:                                                  *)
(*       (p with px := 1).px = 1                                         *)
(*       p.px = 0                                                        *)
(*     Certified: |- ~!p. (p with px := 1).px = p.px                     *)

(* A goal that compares two whole record *values* across an update, such *)
(* as [(p : point) with px := 0 = p], is a different matter: computeLib  *)
(* does not reduce the record-update constant, so certification gets     *)
(* stuck on [px_fupd] and every candidate stays Potential.  Reading a    *)
(* field back out of an update, as above, reduces fine.                  *)

(* --------------------------------------------------------------------- *)
(* 5.  Options, pairs, and sets                                          *)
(* --------------------------------------------------------------------- *)

refute_def ``IS_SOME (opt : num option) ==> THE opt = 0``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       opt = SOME 1                                                    *)
(*     Evaluated terms:                                                  *)
(*       THE opt = 1                                                     *)
(*       0 = 0                                                           *)
(*     Certified: |- ~!opt. IS_SOME opt ==> THE opt = 0                  *)

refute_def ``FST (p : num # num) = SND p``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 2):                 *)
(*       p = (0,1)                                                       *)
(*     Evaluated terms:                                                  *)
(*       FST p = 0                                                       *)
(*       SND p = 1                                                       *)
(*     Certified: |- ~!p. FST p = SND p                                  *)

(* Sets are functions, and set comprehension is not executable: the QC   *)
(* backends decline outright with "no extractable equations for constant *)
(* pred_set$GSPEC" rather than testing anything.  The model finder is    *)
(* what settles this goal — it is the backend 09_model_finder.sml is     *)
(* about, and the one call in this file that needs the Kodkodi component *)
(* (without it the answer is Unknown).  [upd_genuine_only true] keeps    *)
(* the report to the verdict that survives.  The single Kodkodi thread   *)
(* and the explicit cardinality row are the corpus convention for        *)
(* model-finder calls — see the header of                                *)
(* 10_model_finder_advanced.sml — and are what makes the scope and the   *)
(* model quoted below exact instead of whichever scope won a race.       *)

refute
  (!the_config
     |> upd_genuine_only true
     |> upd_max_threads 1
     |> upd_card [(NONE, [2])]
     |> upd_expect ExpectGenuine)
  ``(s : num set) UNION t = s``;

(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(*     kodkod), with [s] a proper subset of [s UNION t]:                 *)
(*       Scope: card num = 2                                             *)
(*       s = ∅                                                           *)
(*       t = {0; 1}                                                      *)
(*     Evaluated terms:                                                  *)
(*       (s UNION t) x = ?                                               *)
(*       s x = ?                                                         *)
(*     Certified: |- ~!s t. s UNION t = s                                *)

(* --------------------------------------------------------------------- *)
(* 6.  Reach: the size bound                                             *)
(*                                                                       *)
(* Exhaustive QC enumerates values up to [size] (default 10), so a       *)
(* counterexample that only exists further out is never reached.  The    *)
(* enumeration did not finish either, so the verdict is Unknown          *)
(* ("search space not exhausted"): Refute reports that it ran out of     *)
(* budget rather than claiming anything about the conjecture.  Raising   *)
(* the bound finds it.                                                   *)
(* --------------------------------------------------------------------- *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_expect ExpectUnknown)
  ``(x : num) < 20``;

(* ==> Refute could not determine an answer                              *)
(*     Reasons:                                                          *)
(*       exhaustive: search space not exhausted                          *)
(*     val it = Unknown ["exhaustive: search space not exhausted"]       *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_size 25
     |> upd_expect ExpectGenuine)
  ``(x : num) < 20``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 20):                *)
(*       x = 20                                                          *)
(*     Certified: |- ~!x. x < 20                                         *)

(* --------------------------------------------------------------------- *)
(* 7.  Polymorphic conjectures                                           *)
(*                                                                       *)
(* With [finite_types] (the default) type variables are instantiated to  *)
(* the built-in finite types rf1, rf2, ... up to [finite_type_size],     *)
(* which is usually the cheapest way to refute a statement about 'a.     *)
(* Turning that off falls back to [default_type].                        *)
(* --------------------------------------------------------------------- *)

refute_def ``(xs : 'a list) ++ ys = ys ++ xs``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 2):                 *)
(*       xs = [rf2_1]                                                    *)
(*       ys = [rf2_2]                                                    *)
(*     Certified: |- ~!xs ys. xs ++ ys = ys ++ xs                        *)

refute
  (!the_config
     |> upd_finite_types false
     |> upd_default_type [``:num``]
     |> upd_expect ExpectGenuine)
  ``(xs : 'a list) ++ ys = ys ++ xs``;

(* ==> the same conjecture, now instantiated at :num instead:            *)
(*       xs = [0]                                                        *)
(*       ys = [1]                                                        *)
(*     Certified: |- ~!xs ys. xs ++ ys = ys ++ xs                        *)

(* [finite_type_size] caps how large the rfN types may get.  Two         *)
(* elements are already enough to refute "all values are equal".         *)

refute
  (!the_config
     |> upd_finite_type_size 2
     |> upd_expect ExpectGenuine)
  ``!x y : 'a. x = y``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 10):                *)
(*       x = rf2_1                                                       *)
(*       y = rf2_2                                                       *)
(*     Certified: |- ~!x y. x = y                                        *)

(* --------------------------------------------------------------------- *)
(* 8.  Quantifiers inside the goal                                       *)
(*                                                                       *)
(* Free variables and outermost universal quantifiers are the same thing *)
(* to Refute: the two calls below produce identical output.              *)
(* --------------------------------------------------------------------- *)

refute_def ``(x : num) + y = x``;

refute_def ``!x y : num. x + y = x``;

(* ==> both: Refute found a counterexample                               *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       x = 0                                                           *)
(*       y = 1                                                           *)
(*     Certified: |- ~!x y. x + y = x                                    *)

(* A genuinely nested quantifier is harder.  [!xs. ?ys. xs = ys ++ ys]   *)
(* is false — no list of odd length is a concatenation of some list with *)
(* itself — and it is out of reach for QC testing ("not executable:      *)
(* unexpanded binder"), so only native narrowing has a chance.           *)
(* Narrowing does find [xs = [0]], but to rule out every [ys] it can     *)
(* only search the finitely many it refined, and it says so: the inner   *)
(* existential was decided on an incomplete approximation.  That keeps   *)
(* the candidate at Potential, so nothing is returned as a               *)
(* counterexample and the run ends Unknown, naming what stopped each     *)
(* backend.                                                              *)
(*                                                                       *)
(* Both calls below name the three QC backends explicitly, which is what *)
(* this section is about.  At default settings the model finder is       *)
(* selected for this goal too and spends most of the whole-call budget   *)
(* on it.  Finishing inside the timeout, it reports that it searched     *)
(* every scope it was given and found nothing — "Refute: no              *)
(* counterexample found within the tested finite bounds", a statement    *)
(* about the bounds searched rather than about the conjecture — and that *)
(* NoCounterexample outranks the reasons below.  Not finishing, it       *)
(* leaves the Unknown shown here.  Naming the backends takes the         *)
(* documented outcome off the clock.                                     *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive", "random", "narrowing"])
     |> upd_expect ExpectUnknown)
  ``!xs : num list. ?ys. xs = ys ++ ys``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: narrowing, substrate: native, size 1):                  *)
(*       xs = [0]                                                        *)
(*     Potential counterexample:                                         *)
(*       PNF testing used an incomplete finite approximation             *)
(*     …continuing search for a genuine counterexample                   *)
(*     Refute could not determine an answer                              *)
(*     Reasons:                                                          *)
(*       not executable: unexpanded binder                               *)
(*       narrowing: narrowing search exhausted                           *)
(*     val it = Unknown ["not executable: unexpanded binder",            *)
(*                       "narrowing: narrowing search exhausted"]        *)

(* Opting out of certification does not rescue it.  [upd_certify false]  *)
(* only skips the kernel check on a candidate that would otherwise pass  *)
(* it; a candidate already known to rest on an incomplete search is not  *)
(* promoted, so the same Potential report comes back.  That distinction  *)
(* is the subject of 02_verdicts_and_config.sml.                         *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive", "random", "narrowing"])
     |> upd_certify false
     |> upd_expect ExpectUnknown)
  ``!xs : num list. ?ys. xs = ys ++ ys``;

(* ==> the same Potential report, and the same Unknown again             *)

(* The smart-quantifier translation is a separate knob, and it is what   *)
(* lets bounded exhaustive testing solve for a variable that an          *)
(* equational premise already pins down instead of enumerating blindly.  *)
(* At size 3 the smart translation reaches the four-element list at      *)
(* once; switched off, the same budget cannot get there.                 *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_size 3
     |> upd_expect ExpectGenuine)
  ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``;

(* ==> Refute found a counterexample                                     *)
(*     (backend: exhaustive, substrate: native, size 1):                 *)
(*       xs = [T; T; T; T]                                               *)
(*     Certified: |- ~!xs. xs = REVERSE [T; T; T; T] ==> F               *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_size 3
     |> upd_smart_quantifier false
     |> upd_expect ExpectUnknown)
  ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``;

(* ==> Refute could not determine an answer                              *)
(*     Reasons:                                                          *)
(*       exhaustive: search space not exhausted                          *)
