(* ===================================================================== *)
(*  HolRefute by example, 6: native narrowing                            *)
(*                                                                       *)
(*  The narrowing backend starts from wholly unknown values and refines  *)
(*  only the parts the goal actually inspects.  That buys three things   *)
(*  the enumerating backends do not have: counterexamples that are       *)
(*  functions, counterexamples with holes in the irrelevant positions,   *)
(*  and refutation of existential goals.                                 *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap < examples/06_narrowing.sml  *)
(* ===================================================================== *)

load "Refute";
open Refute;

val narrowing = upd_backends (SOME ["narrowing"]) (!the_config);

(* --------------------------------------------------------------------- *)
(* 1.  Function-valued counterexamples                                   *)
(*                                                                       *)
(* Nothing says a counterexample has to be a number or a list.  Function *)
(* inputs are represented by finite update chains: the unrefined part    *)
(* prints as a constant lambda, and every point the goal actually looked *)
(* at prints as a HOL UPDATE on top of it, so you can read off exactly   *)
(* which arguments matter.                                               *)
(* --------------------------------------------------------------------- *)

refute narrowing ``(f : num -> num) 0 = f 1``;
(* ==> f = (λx. 0)⦇0 ↦ 1⦈, with evaluated terms f 0 = 1 and f 1 = 0,     *)
(*     certified by  ⊢ ¬∀f. f 0 = f 1                                    *)

refute narrowing ``MAP (f : num -> num) xs = xs``;
(* ==> f = λx. 0 and xs = 1::_ : no argument of f is distinguished, so   *)
(*     the function stays constant while the list is refined one cell    *)

refute narrowing ``(f : num -> num) 0 < f 1 ==> f 1 < f 2``;
(* ==> f = (λx. 0)⦇1 ↦ 1⦈, which satisfies the premise (0 < 1) and       *)
(*     falsifies the conclusion (1 < 0)                                  *)

(* --------------------------------------------------------------------- *)
(* 2.  Turning finite functions off                                      *)
(*                                                                       *)
(* [upd_finite_functions false] restores the older behaviour, where a    *)
(* function-typed variable simply makes the goal inapplicable.  Useful   *)
(* mainly to see what the representation is doing for you.               *)
(* --------------------------------------------------------------------- *)

refute (upd_finite_functions false narrowing) ``(f : num -> num) 0 = f 1``;
(* ==> Unknown ["narrowing: native: narrowing cannot generate function   *)
(*     type :num -> num before finitization", ...]; the cv and compute   *)
(*     substrates are tried next and decline the problem in turn         *)

(* --------------------------------------------------------------------- *)
(* 3.  Partial counterexamples                                           *)
(*                                                                       *)
(* [NULL xs] only looks at the outermost constructor of [xs], so         *)
(* narrowing stops there and prints an underscore for the unexamined     *)
(* parts: any list of that shape is a counterexample, not just one.      *)
(* [upd_evals] fills in a concrete representative alongside it.          *)
(* --------------------------------------------------------------------- *)

refute (upd_evals [``xs : num list``] narrowing) ``NULL (xs : num list)``;
(* ==> xs = _::_ , with the evaluated term xs = [0] as one witness of    *)
(*     that shape; certified by  ⊢ ¬∀xs. NULL xs                         *)

(* --------------------------------------------------------------------- *)
(* 4.  Refinement depth                                                  *)
(*                                                                       *)
(* For narrowing, [size] is the refinement-depth bound rather than a     *)
(* value bound.  A conjecture whose smallest counterexample is deep      *)
(* needs a deeper budget.                                                *)
(* --------------------------------------------------------------------- *)

val deep = ``LENGTH (xs : num list) <> 4``;

refute (upd_size 2 narrowing) deep;
(* ==> Unknown ["narrowing: narrowing search exhausted"]: two levels of  *)
(*     refinement cannot reach a four-element list                       *)

refute (upd_size 6 narrowing) deep;
(* ==> xs = [_; _; _; _] , reported at size 4: the length is all the     *)
(*     goal inspects, so none of the four elements is refined            *)

(* --------------------------------------------------------------------- *)
(* 5.  Existential goals                                                 *)
(*                                                                       *)
(* Refuting [?x. P x] means showing that no witness exists, which is     *)
(* only meaningful over a domain the search can exhaust.  Narrowing      *)
(* supports prenex existentials; [upd_allow_existentials false] declines *)
(* them instead.                                                         *)
(* --------------------------------------------------------------------- *)

val _ = Datatype `colour = Red | Green | Blue`;

(* The [n] suffixes pin the numerals to :num.  Without them the ambient  *)
(* heap resolves the overloading elsewhere and narrowing reports "no     *)
(* TypeBase information for :rat".                                       *)
val code_def = Define `
  (code Red = 0n) /\ (code Green = 1n) /\ (code Blue = 4n)`;

(* No colour has code 2.                                                 *)
refute narrowing ``?c. code c = 2``;
(* ==> a counterexample with no bindings at all, certified by            *)
(*     ⊢ ¬∃c. code c = 2 : the whole three-element domain was exhausted  *)

refute (upd_allow_existentials false narrowing) ``?c. code c = 2``;
(* ==> Unknown ["narrowing: narrowing existential goals require          *)
(*     allow_existentials"]                                              *)

(* A witness does exist here, so there is nothing to report.             *)
refute narrowing ``?c. code c = 1``;
(* ==> Unknown ["narrowing: narrowing search exhausted"]: failing to     *)
(*     refute is reported as ignorance, not as a positive verdict        *)

(* --------------------------------------------------------------------- *)
(* 6.  Certification of a narrowing hit                                  *)
(*                                                                       *)
(* Narrowing candidates are validated by replaying the recorded case     *)
(* tree; ground and partial candidates fall back to evaluation.  Either  *)
(* way the verdict comes with a HOL theorem, and that theorem is about   *)
(* the quantified statement, not about one instance.                     *)
(* --------------------------------------------------------------------- *)

val cert_thm =
  case refute (upd_quiet true narrowing) ``NULL (xs : num list)`` of
      Counterexample ({cert = SOME theorem, ...} :: _) => theorem
    | _ => raise Fail "expected a certified narrowing counterexample";
(* ==> val cert_thm = ⊢ ¬∀xs. NULL xs : the closed negation, although    *)
(*     the counterexample that produced it was the partial one above     *)

Tag.dest_tag (Thm.tag cert_thm);
(* ==> (["DISK_THM"], []): the theorem carries no Refute oracle, only    *)
(*     the standard tag inherited from theorems loaded from disk         *)

(* --------------------------------------------------------------------- *)
(* 7.  Where narrowing sits in the default race                          *)
(*                                                                       *)
(* With the default backend selection all of exhaustive, random,         *)
(* narrowing and (when configured) kodkod compete, and the strongest     *)
(* verdict wins.  Asking for the narrowing backend by name, as above,    *)
(* is how you see its answer specifically.                               *)
(* --------------------------------------------------------------------- *)

case refute (upd_quiet true (!the_config)) ``(f : num -> num) 0 = f 1`` of
    Counterexample (cex :: _) => (#backend cex, #substrate cex)
  | _ => ("none", "none");
(* ==> ("exhaustive", "native"): on this goal the enumerating backend    *)
(*     wins the race, and the narrowing answer of section 1 is the one   *)
(*     you only see by selecting that backend                            *)
