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
val () = register_trace ("regexpTools", trace_level, 4);
fun chatting n = n <= !trace_level;
fun chat n s = if chatting n then Lib.say s else ();

(*---------------------------------------------------------------------------*)
(* Function caches.                                                          *)
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
(* Executing the semantic-driven matcher.                                    *)
(*---------------------------------------------------------------------------*)

val () = computeLib.add_funs [LAST_DEF];

(*---------------------------------------------------------------------------*)
(* Executing the automata matcher.                                           *)
(*---------------------------------------------------------------------------*)

fun cache_conv m n conv =
  let
    val cconv = cache compare conv
  in
    fn tm =>
    let
      val (hit, th) = cconv tm
      val _ = chat m (if hit then "+" else "-")
      val _ = if chatting n then Lib.say ("\n" ^ thm_to_string th) else ()
    in
      th
    end
  end;

val initial_regexp2na_conv =
  cache_conv 3 4 (ONCE_REWRITE_CONV [initial_regexp2na] THENC EVAL);

val accept_regexp2na_conv =
  cache_conv 3 4 (ONCE_REWRITE_CONV [accept_regexp2na] THENC EVAL);

val transition_regexp2na_conv =
  cache_conv 3 4 (ONCE_REWRITE_CONV [transition_regexp2na] THENC EVAL);

val eval_transitions_conv =
  cache_conv 1 3 (ONCE_REWRITE_CONV [eval_transitions_def] THENC EVAL);

local
  fun hol_rev tm =
    let val (l,ty) = listSyntax.dest_list tm
    in listSyntax.mk_list (rev l, ty)
    end;
in
  fun areport_conv tm =
    let
      val l = hol_rev (rand (rator tm))
      val () = if not (chatting 2) then ()
               else Lib.say ("\nmatch: " ^ term_to_string l)
    in
      REWR_CONV areport_def
    end tm;
end;

val () = computeLib.add_funs
  [(* Prefer the cached conversions
      initial_regexp2na, accept_regexp2na, transition_regexp2na, *)
   matcherTheory.astep_def];

val () = computeLib.add_convs
  [(``initial_regexp2na : 'a regexp -> num``, 1, initial_regexp2na_conv),
   (``accept_regexp2na : 'a regexp -> num -> bool``, 2, accept_regexp2na_conv),
   (``transition_regexp2na : 'a regexp -> num -> 'a -> num -> bool``, 4,
    transition_regexp2na_conv),
   (``eval_transitions : 'a regexp -> num list -> 'a -> num list``, 3,
    eval_transitions_conv),
   (``areport : 'a -> 'b -> 'b``, 2, areport_conv)];

(*---------------------------------------------------------------------------*)
(* Speed up the evaluation of very long lists.                               *)
(*---------------------------------------------------------------------------*)

local
  val dropize =
    (CONV_RULE o LAND_CONV o ONCE_REWRITE_CONV) [GSYM (CONJUNCT1 drop_def)];

  fun dest_single l =
    let
      val (h,t) = listSyntax.dest_cons l
      val _ = listSyntax.is_nil t orelse raise ERR "dest_single" ""
    in
      h
    end;

  val is_single = can dest_single;

  val reduce = CONV_RULE (LAND_CONV reduceLib.REDUCE_CONV);

  fun loop acc th =
    let
      val acc = MATCH_MP head_drop th :: acc
    in
      if is_single (snd (dest_eq (concl th))) then
        CONV_RULE reduceLib.REDUCE_CONV (MATCH_MP length_drop th) :: acc
      else loop acc (reduce (MATCH_MP tail_drop th))
    end;
in
  fun EVAL_BIGLIST def = let val def = dropize def in loop [def] def end;
end;

end
