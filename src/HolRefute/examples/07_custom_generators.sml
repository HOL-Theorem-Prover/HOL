(* ===================================================================== *)
(*  HolRefute by example, 7: generating only the values you care about   *)
(*                                                                       *)
(*  Refute derives generators from datatype declarations, which is right  *)
(*  until your type carries an invariant the declaration does not know    *)
(*  about.  Then a conjecture that only holds for well-formed values      *)
(*  looks refutable, and the "counterexample" is garbage input.  Two      *)
(*  registries fix that: register_generator and abstract_generator.       *)
(*                                                                       *)
(*  Custom and abstract generators are supported by the Compute           *)
(*  substrate, so these examples select it explicitly.                    *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/07_custom_generators.sml                          *)
(* ===================================================================== *)

load "Refute";
open Refute;

val compute = !the_config
  |> upd_substrate Compute
  |> upd_backends (SOME ["exhaustive"]);

(* --------------------------------------------------------------------- *)
(* 1.  The problem                                                       *)
(*                                                                       *)
(* [flatten] produces a sorted list for search trees, but the derived     *)
(* generator builds arbitrary [btree] values, so the conjecture is        *)
(* refuted by a tree no program of yours would ever construct.           *)
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

refute (upd_expect ExpectGenuine compute) ``SORTED (<) (flatten t)``;
(* ==> Counterexample: t = Branch Leaf 0 (Branch Leaf 0 Leaf)           *)

(* --------------------------------------------------------------------- *)
(* 2.  A generator that only builds search trees                         *)
(*                                                                       *)
(* An enumerating custom generator is a function from the current size to *)
(* a list of closed HOL terms.  Here every term is a tree built by        *)
(* repeated insertion, so the invariant holds by construction.  The       *)
(* [size] argument lets you scale with the search budget.                *)
(* --------------------------------------------------------------------- *)

fun insertions elements =
  let
    val list = listSyntax.mk_list
      (map (numSyntax.term_of_int) elements, ``:num``)
  in
    rhs (concl (EVAL ``FOLDR insert Leaf ^list``))
  end;

(* [FOLDR] consumes the list from the right, so this inserts 1, then 3,  *)
(* then 0, then 2.  Whatever the order, the result is a search tree.     *)
insertions [2, 0, 3, 1];
(* ==> Branch (Branch Leaf 0 Leaf) 1 (Branch (Branch Leaf 2 Leaf) 3 Leaf) *)

val insertion_orders =
  [[], [0], [1, 0], [0, 1], [1, 0, 2], [2, 1, 0], [0, 1, 2],
   [2, 0, 3, 1]];

val search_trees : custom_gen =
  {enumerate = SOME (fn size =>
     map insertions
       (List.filter (fn order => length order <= size + 1)
          insertion_orders)),
   random = NONE};

val () = register_generator ``:btree`` search_trees;

(* The same conjecture is no longer refuted: every generated tree is     *)
(* sorted, so the whole size schedule runs without a hit.  The verdict   *)
(* is Unknown rather than NoCounterexample because neither registry      *)
(* claims that its values exhaust the type -- a restricted search never  *)
(* reports a completed one.  "Not refuted within the tested bounds" is   *)
(* all you get, and all you should want: it is not a proof.              *)
refute (upd_expect ExpectUnknown compute) ``SORTED (<) (flatten t)``;
(* ==> Unknown ["exhaustive: search space not exhausted"]                *)

(* And a genuinely false conjecture about search trees still falls; the  *)
(* witness below is [insertions [0]].                                    *)
refute (upd_expect ExpectGenuine compute)
  ``LENGTH (flatten (insert x t)) = LENGTH (flatten t) + 1``;
(* ==> Counterexample: x = 0, t = Branch Leaf 0 Leaf                    *)

(* --------------------------------------------------------------------- *)
(* 3.  A random component                                                *)
(*                                                                       *)
(* The second half of a custom generator draws one value from the shared  *)
(* 64-bit stream and returns the advanced state, which is what keeps a    *)
(* seeded run reproducible.  [Refute_Eval.rand_below] is the primitive to *)
(* use; do not invent your own stepping.  Note that Refute_Eval is an     *)
(* implementation module, not part of Refute.sig.                        *)
(* --------------------------------------------------------------------- *)

val trees_with_random : custom_gen =
  {enumerate = #enumerate search_trees,
   random = SOME (fn size => fn state =>
     let
       val orders = List.filter
         (fn order => length order <= size + 1) insertion_orders
       val count = IntInf.fromInt (length orders)
       val (choice, next) = Refute_Eval.rand_below count state
     in
       (insertions (List.nth (orders, IntInf.toInt choice)), next)
     end)};

(* A later registration for the same type replaces the earlier one.      *)
val () = register_generator ``:btree`` trees_with_random;

fun random_refute expectation quiet tm =
  refute
    (compute
       |> upd_backends (SOME ["random"])
       |> upd_seed (SOME 1234)
       |> upd_iterations 50
       |> upd_quiet quiet
       |> upd_expect expectation)
    tm;

(* Every tree drawn is a search tree, so the random backend runs out of  *)
(* its iteration budget without a hit.                                   *)
random_refute ExpectUnknown false ``SORTED (<) (flatten t)``;
(* ==> Unknown ["random: random search exhausted"]                       *)

random_refute ExpectGenuine false
  ``LENGTH (flatten (insert x t)) = LENGTH (flatten t) + 1``;
(* ==> Counterexample: x = 1, t = Branch (Branch Leaf 0 Leaf) 1 Leaf     *)

(* The seed pins the draw, so the same run repeats exactly.              *)
fun witnesses outcome =
  case outcome of
      Counterexample (cex :: _) =>
        map (Parse.term_to_string o #2) (#bindings cex)
    | _ => [];

fun random_witness () =
  witnesses (random_refute ExpectGenuine true
    ``LENGTH (flatten (insert x t)) = LENGTH (flatten t) + 1``);

random_witness () = random_witness ();
(* ==> true                                                              *)

(* --------------------------------------------------------------------- *)
(* 4.  Abstract generators: constructors plus an invariant               *)
(*                                                                       *)
(* When the values you want are exactly the constructor applications      *)
(* satisfying a predicate, [abstract_generator] says so directly instead  *)
(* of enumerating terms by hand.  Candidates failing [pred] are never     *)
(* offered to the goal.                                                   *)
(* --------------------------------------------------------------------- *)

val _ = Datatype `interval = <| lo : num ; hi : num |>`;

(* Without the invariant, lo > hi intervals refute this at once.         *)
refute (upd_expect ExpectGenuine compute) ``(i : interval).lo <= i.hi``;
(* ==> Counterexample: i = interval 1 0                                  *)

val interval_constructors =
  TypeBasePure.constructors_of (valOf (TypeBase.fetch ``:interval``));

val () = abstract_generator
  {ty = ``:interval``,
   constructors = interval_constructors,
   pred = SOME ``\i : interval. i.lo <= i.hi``};

(* Now only well-formed intervals are generated, so nothing is found ... *)
refute (upd_expect ExpectUnknown compute) ``(i : interval).lo <= i.hi``;
(* ==> Unknown ["exhaustive: search space not exhausted"]                *)

(* ... while a false claim about well-formed intervals still falls, and  *)
(* its witness does satisfy the invariant.                               *)
refute (upd_expect ExpectGenuine compute)
  ``(i : interval).hi - i.lo <= 1``;
(* ==> Counterexample: i = interval 0 2                                  *)

(* --------------------------------------------------------------------- *)
(* 5.  Registrations are session state, not theory content               *)
(*                                                                       *)
(* The datatypes and definitions above are theory content, but the       *)
(* registries themselves are ML refs: nothing Refute-created reaches the  *)
(* current theory.                                                       *)
(* --------------------------------------------------------------------- *)

List.filter (String.isSubstring "refute")
  (map (#1 o Term.dest_const) (Theory.constants "scratch"));
(* ==> [] : string list                                                  *)

(* Undoing a restriction is just another registration: dropping [pred]   *)
(* brings the lo > hi intervals -- and the counterexample -- back.       *)
val () = abstract_generator
  {ty = ``:interval``,
   constructors = interval_constructors,
   pred = NONE};

refute (upd_expect ExpectGenuine compute) ``(i : interval).lo <= i.hi``;
(* ==> Counterexample: i = interval 1 0                                  *)

Theory.current_theory ();
(* ==> "scratch"                                                         *)
