(*---------------------------------------------------------------------------*)
(* Regular expressions and a regexp matcher.                                 *)
(* Originated from Konrad Slind, tweaked by MJCG for Accellera PSL SEREs     *)
(* An automata-based matcher added by Joe Hurd                               *)
(*---------------------------------------------------------------------------*)

structure regexpTools :> regexpTools =
struct

(*
app load ["bossLib", "metisLib", "stringLib", "matcherTheory"];
*)

open HolKernel Parse boolLib;
open bossLib metisLib pairTheory combinTheory listTheory rich_listTheory
     pred_setTheory arithmeticTheory;
open regexpTheory matcherTheory;

(*---------------------------------------------------------------------------*)
(* Tracing.                                                                  *)
(*---------------------------------------------------------------------------*)

val trace_level = ref 1;
val () = register_trace ("regexpTools", trace_level, 3);
fun chatting n = n <= !trace_level;
fun chat n s = if chatting n then Lib.say s else ();

(*---------------------------------------------------------------------------*)
(* Needed to execute the naive matcher.                                      *)
(*---------------------------------------------------------------------------*)

val () = computeLib.add_funs [LAST_DEF];

(*---------------------------------------------------------------------------*)
(* Caches.                                                                   *)
(*---------------------------------------------------------------------------*)

fun cache order f =
  let
    val cache = ref (Binarymap.mkDict order)
  in
    fn x =>
    case Binarymap.peek (!cache, x) of
      SOME y => (true, y)
    | NONE =>
        let
          val y = f x
          val () = cache := Binarymap.insert (!cache, x, y)
        in
          (false, y)
        end
  end;

(*---------------------------------------------------------------------------*)
(* A conversion to execute the automata matcher.                             *)
(*---------------------------------------------------------------------------*)

fun cache_conv m conv =
  let
    val cconv = cache compare conv
  in
    fn tm =>
    let
      val (hit, th) = cconv tm
      val _ = chat m (if hit then "+" else "-")
      val _ = if chatting (m + 1) then Lib.say (thm_to_string th ^ "\n") else ()
    in
      th
    end
  end;

val initial_regexp2na_conv =
  cache_conv 2 (ONCE_REWRITE_CONV [initial_regexp2na] THENC EVAL);

val accept_regexp2na_conv =
  cache_conv 2 (ONCE_REWRITE_CONV [accept_regexp2na] THENC EVAL);

val transition_regexp2na_conv =
  cache_conv 2 (ONCE_REWRITE_CONV [transition_regexp2na] THENC EVAL);

val eval_transitions_conv =
  cache_conv 1 (ONCE_REWRITE_CONV [eval_transitions_def] THENC EVAL);

(* Prefer the cached versions
val () = computeLib.add_funs
  [initial_regexp2na, accept_regexp2na, transition_regexp2na];
*)

val () = computeLib.add_convs
  [(``initial_regexp2na : 'a regexp -> num``, 1, initial_regexp2na_conv),
   (``accept_regexp2na : 'a regexp -> num -> bool``, 2, accept_regexp2na_conv),
   (``transition_regexp2na : 'a regexp -> num -> 'a -> num -> bool``, 4,
    transition_regexp2na_conv),
   (``eval_transitions : 'a regexp -> num list -> 'a -> num list``, 3,
    eval_transitions_conv)];

end
