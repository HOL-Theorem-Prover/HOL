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

(******************************************************************************
* The trace levels of the regular expression library:      
* 0: silent
* 1: 1 character (either - or +) for each list element processed
* 2: matches as they are discovered
* 3: transitions as they are calculated
* 4: internal state of the automata
******************************************************************************)

val trace_level = ref 1;
val () = register_trace ("regexpTools", trace_level, 4);
fun chatting n = n <= !trace_level;
fun chat n s = if chatting n then Lib.say s else ();

(*---------------------------------------------------------------------------*)
(* Terms.                                                                    *)
(*---------------------------------------------------------------------------*)

val initial_regexp2na_tm = ``initial_regexp2na : 'a regexp -> num``;
val accept_regexp2na_tm = ``accept_regexp2na : 'a regexp -> num -> bool``;
val transition_regexp2na_tm =
  ``transition_regexp2na : 'a regexp -> num -> 'a -> num -> bool``;
val eval_accepts_tm = ``eval_accepts : 'a regexp -> num list -> bool``;
val eval_transitions_tm =
  ``eval_transitions : 'a regexp -> num list -> 'a -> num list``;
val exists_transition_regexp2na_tm =
  ``exists_transition_regexp2na : 'a regexp -> num -> num -> bool``;
val areport_tm = ``areport : 'a -> 'b -> 'b``;

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

local
  val t_or = CONJUNCT1 (SPEC_ALL OR_CLAUSES);

  fun witness_conv tm =
    let
      val () = if not (chatting 4) then ()
               else Lib.say ("\nwitness_conv: " ^ term_to_string tm)
      val (x,b) = dest_exists tm
      val (ty,_) = dom_rng (type_of x)
      val conjs = strip_conj b
      val emp_tm = inst [alpha |-> ty] pred_setSyntax.empty_tm
      val ins_tm = inst [alpha |-> ty] pred_setSyntax.insert_tm
      fun ins (v,s) = mk_comb (mk_comb (ins_tm, rand (rator v)), s)
      val set = foldr ins emp_tm (filter (not o is_neg) conjs)
      val goal = subst [x |-> set] b
      val wit_th = EQT_ELIM (EVAL goal)
      val ex_th = EXISTS (tm, set) wit_th
    in
      EQT_INTRO ex_th
    end;

  val sat_conv =
    QUANT_CONV normalForms.DNF_CONV
    THENC (REWR_CONV boolTheory.EXISTS_SIMP
           ORELSEC (EXISTS_OR_CONV
                    THENC LAND_CONV witness_conv
                    THENC REWR_CONV t_or)
           ORELSEC witness_conv);
in
  fun set_sat_conv tm =
    let
      val () = if not (chatting 4) then ()
               else Lib.say ("\nset_sat_conv: " ^ term_to_string tm)
    in
      sat_conv tm
      handle e as HOL_ERR _ => Raise e
    end;
 end;

local
  val chr_ss = simpLib.++ (boolSimps.bool_ss, numSimps.REDUCE_ss);
in
  val chr_sat_conv =
    QUANT_CONV normalForms.DNF_CONV
    THENC SIMP_CONV chr_ss [chr_11, chr_suff, chr_suff1];
end;

val prefix_sat_conv = ref set_sat_conv;

local
  fun exists_conv tm =
    (ONCE_REWRITE_CONV [exists_transition_regexp2na_def]
     THENC QUANT_CONV EVAL
     THENC !prefix_sat_conv) tm;
in
  val exists_transition_regexp2na_conv = cache_conv 3 4 exists_conv;
end;

val initial_regexp2na_conv =
  cache_conv 3 4 (ONCE_REWRITE_CONV [initial_regexp2na] THENC EVAL);

val accept_regexp2na_conv =
  cache_conv 3 4 (ONCE_REWRITE_CONV [accept_regexp2na] THENC EVAL);

val transition_regexp2na_conv =
  cache_conv 3 4 (ONCE_REWRITE_CONV [transition_regexp2na] THENC EVAL);

val eval_accepts_conv =
  cache_conv 2 3 (ONCE_REWRITE_CONV [eval_accepts_def] THENC EVAL);

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
  [(* Prefer the cached conversions of
      initial_regexp2na, accept_regexp2na, transition_regexp2na,
      eval_accepts, eval_transitions *)
   matcherTheory.astep_def,
   matcherTheory.dijkstra_def];

val () = computeLib.add_convs
  [(initial_regexp2na_tm,           1, initial_regexp2na_conv),
   (accept_regexp2na_tm,            2, accept_regexp2na_conv),
   (transition_regexp2na_tm,        4, transition_regexp2na_conv),
   (eval_accepts_tm,                2, eval_accepts_conv),
   (eval_transitions_tm,            3, eval_transitions_conv),
   (exists_transition_regexp2na_tm, 3, exists_transition_regexp2na_conv),
   (areport_tm,                     2, areport_conv)];

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

(*---------------------------------------------------------------------------*)
(* Export a regular expression as a Verilog state machine.                   *)
(*---------------------------------------------------------------------------*)

local
  val empty : (term, int * bool * term list) Binarymap.dict =
    Binarymap.mkDict compare;

  fun finalize acc =
    let
      fun h ((i,_,_), (j,_,_)) = Int.compare (i,j)
      fun g t = let val (i,_,_) = Binarymap.find (acc,t) in i end
      fun f (_,(i,a,ts),l) = (i, a, map g ts) :: l
    in
      mlibUseful.sort h (Binarymap.foldl f [] acc)
    end;

  fun initial r =
    let
      val ty = (hd o snd o dest_type o type_of) r
      val e = inst [alpha |-> ty] initial_regexp2na_tm
      val t = mk_comb (e, r)
      val res = rhs (concl (EVAL t))
    in
      listSyntax.mk_list ([res], numSyntax.num)
    end;

  fun accepting r s =
    let
      val ty = (hd o snd o dest_type o type_of) r
      val e = inst [alpha |-> ty] eval_accepts_tm
      val t =
        list_mk_comb (e, [r, s])
        handle HOL_ERR _ => raise Fail "export_dfa.transition.list_mk_comb"
      val res = rhs (concl (EVAL t))
      val _ =
        res = T orelse res = F orelse
        raise ERR "export_regexp" "couldn't reduce eval_accepts"        
    in 
      res = T
    end;

  fun transition r s x =
    let
      val ty = (hd o snd o dest_type o type_of) r
      val e = inst [alpha |-> ty] eval_transitions_tm
      val t =
        list_mk_comb (e, [r, s, x])
        handle HOL_ERR _ =>
          raise Fail
            ("export_dfa.transition.list_mk_comb:" ^
             " e = " ^ type_to_string (type_of e) ^
             ", r = " ^ type_to_string (type_of r) ^
             ", s = " ^ type_to_string (type_of s) ^
             ", x = " ^ type_to_string (type_of x))
      val res = rhs (concl (EVAL t))
    in
      res
    end;

  fun export _ _ acc [] = finalize acc
    | export alph r acc (s :: rest) =
    if Option.isSome (Binarymap.peek (acc,s)) then export alph r acc rest else
      let
        val i = Binarymap.numItems acc
        val a = accepting r s
        val ts = map (transition r s) alph
        val acc = Binarymap.insert (acc, s, (i,a,ts))
      in
        export alph r acc (ts @ rest)
      end;
in
  fun export_dfa alphabet r = export alphabet r empty [initial r];
end;

fun all_subsets [] = [[]]
  | all_subsets (x :: xs) =
  let val y = all_subsets xs
  in map (cons (x,true)) y @ map (cons (x,false)) y
  end;

fun hol_subset l =
  let
    val ty = type_of (fst (hd l))
    val emp = inst [alpha |-> ty] pred_setSyntax.empty_tm
    val ins = inst [alpha |-> ty] pred_setSyntax.insert_tm
    fun f ((_,false),s) = s
      | f ((x,true),s) =
      list_mk_comb (ins, [x,s])
      handle HOL_ERR _ => raise Fail "export_set_dfa.hol_subset.f"
  in
    foldr f emp l
  end;

fun export_set_dfa props r =
  let
    val x = all_subsets props
    val y = map hol_subset x
  in
    (x, export_dfa y r)
  end;

end