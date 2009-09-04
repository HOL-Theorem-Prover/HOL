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

val LINE_LENGTH = ref 79;

local fun dup _ 0 l = l | dup x n l = dup x (n - 1) (x :: l);
in fun chs x n = implode (dup x n []);
end;

fun DISCH_CONJ [] = I
  | DISCH_CONJ [x] = DISCH x
  | DISCH_CONJ (x :: (xs as _ :: _)) =
  CONV_RULE (REWR_CONV AND_IMP_INTRO) o DISCH x o DISCH_CONJ xs;

fun all_subsets [] = [[]]
  | all_subsets (x :: xs) =
  let val y = all_subsets xs
  in map (cons (x,true)) y @ map (cons (x,false)) y
  end;

val dest_in = dest_binop ``(IN)`` (ERR "dest_in" "");

fun mk_alph s =
  let
    val t = map (rhs o concl o EVAL) s
    val ts = zip t s
  in
    fn x => assoc x ts
  end;

datatype 'a condition =
  Leaf of 'a
| Branch of string * 'a condition * 'a condition;

local
  val s = ``s : num -> bool``;

  val empty : (term,int) Binarymap.dict = Binarymap.mkDict compare;

  fun member (m : (term,int) Binarymap.dict) t =
    Option.isSome (Binarymap.peek (m, t));

  fun harvest_terms acc [] = acc
    | harvest_terms acc (Leaf (tm,_) :: l) = harvest_terms (tm :: acc) l
    | harvest_terms acc (Branch (_,a,b) :: l) = harvest_terms acc (a :: b :: l);

  fun finalize (set : (term,int) Binarymap.dict) =
    let
      fun f (Leaf (tm,th)) = Leaf (Binarymap.find (set,tm), th)
        | f (Branch (c,a,b)) = Branch (c, f a, f b)
      fun g acc [] = acc
        | g acc ((i,t,a,c) :: r) = g ((i, t, a, f c) :: acc) r
    in
      g []
    end;

  fun initial r =
    let
      val ty = (hd o snd o dest_type o type_of) r
      val e = inst [alpha |-> ty] initial_regexp2na_tm
      val t =
        mk_comb (e, r)
        handle HOL_ERR _ =>
          raise Fail
            ("export_nfa.initial.mk_comb: " ^
             " e = " ^ type_to_string (type_of e) ^
             ", r = " ^ type_to_string (type_of r))
      val res = rhs (concl (EVAL t))
    in
      listSyntax.mk_list ([res], numSyntax.num)
    end;

  fun accept r s =
    let
      val ty = (hd o snd o dest_type o type_of) r
      val e = inst [alpha |-> ty] eval_accepts_tm
      val t =
        list_mk_comb (e, [r, s])
        handle HOL_ERR _ => raise Fail "export_nfa.accept.list_mk_comb"
      val th = EVAL t
      val res = rhs (concl th)
      val _ =
        res = T orelse res = F orelse
        raise ERR "export_nfa.accept" "couldn't reduce eval_accepts"
    in
      (res = T, th)
    end;

  fun simp tm =
    let val th = CONV_RULE EVAL (ASSUME tm)
    in CONV_RULE (RAND_CONV (SIMP_CONV boolSimps.bool_ss [th]))
    end;

  fun mk_condition (m,d,gen) =
    let
      fun g bs = GEN s o SPEC s o gen o DISCH_CONJ (rev bs)

      fun f bs th =
        let val (_,tm) = dest_eq (concl th) in
          case total (dest_cond o find_term is_cond) tm of
            NONE => Leaf (tm, g bs th)
          | SOME (c,_,_) =>
            let
              val () = if not (chatting 3) then ()
                       else chat 3 ("extract_dfa.mk_condition: th =\n" ^
                                    thm_to_string th ^ "\n")
              val t = find_term (can d) c
              val v = d t
              val s = #Name (dest_thy_const v)
              val tm = m v
              val tm' = mk_neg tm
            in
              Branch (s, f (tm :: bs) (simp tm th), f (tm' :: bs) (simp tm' th))
            end
        end
    in
      f []
    end;

  fun trans alph r s =
    let
      val ty = (hd o snd o dest_type o type_of) r
      val x = genvar ty
      fun mvar t = pred_setSyntax.mk_in (t,x)
      fun dvar t =
        let val (a,b) = dest_in t
        in if b = x then alph a else raise ERR "term_to_bexp.var" "not a var"
        end
      val gen = GEN x
      val e = inst [alpha |-> ty] eval_transitions_tm
      val t =
        list_mk_comb (e, [r, s, x])
        handle HOL_ERR _ =>
          raise Fail
            ("export_nfa.trans.list_mk_comb:" ^
             " e = " ^ type_to_string (type_of e) ^
             ", r = " ^ type_to_string (type_of r) ^
             ", s = " ^ type_to_string (type_of s) ^
             ", x = " ^ type_to_string (type_of x))
      val th = EVAL t
      val () = if not (chatting 3) then ()
               else chat 3 ("extract_dfa.trans: th =\n"^thm_to_string th^"\n")
    in
      mk_condition (mvar,dvar,gen) th
    end;

  fun export _ _ _ set acc [] = finalize set acc
    | export alph r trans set acc (tm :: rest) =
    if member set tm then export alph r trans set acc rest else
      let
        val i = Binarymap.numItems set
        val set = Binarymap.insert (set, tm, i)
        val a = accept r tm
        val c = trans alph r tm
        val rest = harvest_terms rest [c]
        val acc = (i, tm, a, c) :: acc
      in
        export alph r trans set acc rest
      end;
in
  fun extract_dfa alph r =
    export (mk_alph alph) r trans empty [] [initial r];
end;

local
  fun separator s =
    let
      val seps = !LINE_LENGTH - 4 - (size s + 2)
      val m = seps div 2 - 3
      val n = seps - m
    in
      chs #"-" m ^ " " ^ s ^ " " ^ chs #"-" n
    end;

  fun claim r = PP.pp_to_string (!LINE_LENGTH - 3) pp_term r;

  fun comment s =
    String.concat
    (map (fn x => "// " ^ x ^ "\n") (String.fields (fn c => c = #"\n") s));
in
  fun header n r = comment (separator n ^ "\n" ^ claim r);
end;

local
  fun log2 n =
    Int.toString (Real.ceil (Math.ln (Real.fromInt n) / Math.ln 2.0) - 1);

  fun width l = "[" ^ log2 (length l) ^ ":0]";

  open PP;

  fun pp_alphs _ _ [] = raise ERR "verilog_dfa" "empty alphabet"
    | pp_alphs s pp (h :: t) =
    (add_string pp h;
     app (fn a => (add_string pp s; add_break pp (1,0); add_string pp a)) t);

  fun pp_condition pp (Leaf (i,_)) =
    add_string pp ("state = " ^ Int.toString i ^ ";")
    | pp_condition pp (Branch (c,a,b)) =
    (begin_block pp CONSISTENT 0;
     begin_block pp CONSISTENT 2;
     add_string pp ("if (" ^ c ^ ")");
     add_break pp (1,0);
     pp_condition pp a;
     end_block pp;
     add_newline pp;
     begin_block pp CONSISTENT 2;
     add_string pp "else";
     add_break pp (1,0);
     pp_condition pp b;
     end_block pp;
     end_block pp);

  fun pp_case pp name (i,_,(a,_),t) =
    (begin_block pp CONSISTENT 2;
     add_string pp (Int.toString i ^ ":");
     add_break pp (1,0);
     if a then
       add_string pp
         ("begin $display (\"" ^ name ^
          ": property violated!\"); $finish; end")
     else pp_condition pp t;
     end_block pp;
     add_newline pp;
     add_newline pp)

  fun pp_module pp (name,alph,table) =
    (begin_block pp CONSISTENT 0;

     begin_block pp INCONSISTENT (size ("module " ^ name ^ " ("));
     add_string pp ("module " ^ name ^ " (");
     pp_alphs "," pp (alph (*@ ["state"]*));
     add_string pp ");";
     end_block pp;
     add_newline pp;
     add_newline pp;

     begin_block pp INCONSISTENT (size "output" + size (width table) + 2);
     add_string pp ("input" ^ chs #" " (size (width table) + 3));
     pp_alphs "," pp alph;
     add_string pp ";";
     end_block pp;
     add_newline pp;

(*
     add_string pp ("output " ^ width table ^ " state;");
     add_newline pp;
*)
     add_string pp ("reg    " ^ width table ^ " state;");
     add_newline pp;
     add_newline pp;

     add_string pp "initial state = 0;";
     add_newline pp;
     add_newline pp;

     begin_block pp INCONSISTENT (size "always @ (");
     add_string pp "always @ (";
     pp_alphs " or" pp alph;
     add_string pp ")";
     end_block pp;
     add_newline pp;
     begin_block pp INCONSISTENT 2;
     add_string pp "begin";
     add_newline pp;
     add_string pp ("$display (\"" ^ name ^ ": state = %0d\", state);");
     add_newline pp;
     begin_block pp INCONSISTENT 2;
     add_string pp "case (state)";
     add_newline pp;
     app (pp_case pp name) table;
     add_string pp
       ("default: begin $display (\"" ^ name ^
        ": unknown state\"); $finish; end");
     end_block pp;
     add_newline pp;
     add_string pp "endcase";
     end_block pp;
     add_newline pp;
     add_string pp "end";
     add_newline pp;
     add_newline pp;

     add_string pp "endmodule";
     add_newline pp;

     end_block pp);
in
  fun module n a r =
    pp_to_string (!LINE_LENGTH) pp_module
      (n, map (#Name o dest_thy_const) a, extract_dfa a r);
end;

fun verilog_dfa {name = n, alphabet = a, regexp = r} =
  header n r ^ "\n" ^ module n a r;

end