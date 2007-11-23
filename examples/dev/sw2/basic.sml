structure basic :> basic =
struct

open HolKernel Parse boolSyntax boolLib bossLib pairSyntax wordsSyntax;

(*---------------------------------------------------------------------------*)
(* Common used data structures and functions                                 *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* (Atomic) Variables and Operators                                          *)
(*---------------------------------------------------------------------------*)

(* Is the term a word? *)
fun is_word_literal tm = 
 case total dest_n2w tm
  of NONE => false
   | SOME (ntm,wty) => numSyntax.is_numeral ntm;

(* Is the term a word or num literal? *)
fun is_literal tm =
 is_word_literal tm orelse numSyntax.is_numeral tm

fun is_8bit_literal tm =
 is_word_literal tm andalso numSyntax.int_of_term (#2 (dest_comb tm)) < 256

(* Is the term an atomic term? *)
fun is_atomic t =
    is_var t orelse is_word_literal t orelse 
    numSyntax.is_numeral t orelse is_const t orelse
    is_neg t  (* ~x is considered to be an atom *)
    ;

fun OR test [] = false
  | OR test (h::t) = test h orelse OR test t;

(*---------------------------------------------------------------------------*)
(* Is the operator a binary arithmetic operator?                             *)
(*---------------------------------------------------------------------------*)

fun is_num_arithop op0 =
 let open numSyntax
 in 
    OR (same_const op0) [plus_tm,minus_tm,mult_tm,exp_tm]
 end;

(*---------------------------------------------------------------------------*)
(* Is the operator an arithmetic comparison operator?                        *)
(*---------------------------------------------------------------------------*)

fun is_num_cmpop op0 =
 let open numSyntax
     val equality = inst [alpha |-> num] boolSyntax.equality
 in
    OR (same_const op0) [greater_tm, geq_tm,less_tm,equality,leq_tm]
 end;

(*---------------------------------------------------------------------------*)
(* Is the operator an arithmetic word operator?                              *)
(*---------------------------------------------------------------------------*)

fun is_word_arithop op0 =
  let open wordsSyntax
  in 
    OR (same_const op0) [word_add_tm,word_sub_tm,word_mul_tm]
  end;

(*---------------------------------------------------------------------------*)
(* Is the operator a multiplication operator?                                *)
(*---------------------------------------------------------------------------*)

fun is_mult_op op0 =
  (op0 = numSyntax.mult_tm) orelse
  (#1 (dest_const(wordsSyntax.word_mul_tm)) = #1 (dest_const op0) 
   handle _ => false);

(*---------------------------------------------------------------------------*)
(* Is the operator a word comparison operator? Includes equality             *)
(* comparisons.                                                              *)
(*---------------------------------------------------------------------------*)

val is_word_equality = 
   Lib.can (match_term (mk_const("=",``:'a word -> 'a word -> bool``)));

fun is_word_cmpop op0 =
 let open wordsSyntax
 in
    is_word_equality op0 orelse
    OR (same_const op0) [word_lt_tm,word_le_tm,word_gt_tm,word_ge_tm, 
      word_hi_tm, word_hs_tm, word_lo_tm, word_ls_tm]
 end;

(*---------------------------------------------------------------------------*)
(* Is the operator a bitwise word operator?                                  *)
(*---------------------------------------------------------------------------*)

fun is_word_shiftop op0 =
 let open wordsSyntax
 in
    OR (same_const op0) 
        [word_ror_tm,word_rol_tm,word_lsl_tm,word_lsr_tm,word_asr_tm]
 end;

(*---------------------------------------------------------------------------*)
(* Is the operator a bitwise word operator?                                  *)
(*---------------------------------------------------------------------------*)

fun is_word_bitwiseop op0 =
 let open wordsSyntax
 in
    OR (same_const op0) [word_xor_tm,word_and_tm,word_or_tm]
 end;


(*---------------------------------------------------------------------------*)
(* Is the operator a logical operator?                                       *)
(*---------------------------------------------------------------------------*)

fun is_relop op0 = 
 let open boolSyntax
 in
    OR (same_const op0) [conjunction,disjunction]
 end;

fun is_binop opr = 
  is_relop opr orelse 
  is_word_bitwiseop opr orelse
  is_num_arithop opr orelse
  is_word_arithop opr orelse
  is_num_cmpop opr orelse
  is_word_cmpop opr orelse
  is_word_shiftop opr;


(*---------------------------------------------------------------------------*)
(* Is the expression in a conditional test an (atomic) comparison?           *)
(*---------------------------------------------------------------------------*)

fun is_atom_cond tm =
    is_comb tm andalso
    let val (op0,_) = strip_comb tm 
    in
      is_num_cmpop op0 orelse is_word_cmpop op0
    end;

(*---------------------------------------------------------------------------*)
(* Last Expression                                                           *)
(*---------------------------------------------------------------------------*)

fun last_exp exp = 
  if is_let exp then
     last_exp (#3 (dest_plet exp))
  else exp;

(*---------------------------------------------------------------------------*)
(* Term manipulating functions                                               *)
(*---------------------------------------------------------------------------*)

(* substitute variables in an expression *) 
fun subst_exp rule exp = 
  if is_plet exp then
     let val (v, M, N) = dest_plet exp
     in
         mk_plet (v, subst_exp rule M, subst_exp rule N)
     end
  else if is_cond exp then
     let val (c,t,f) = dest_cond exp
     in
         mk_cond (subst_exp rule c, subst_exp rule t, subst_exp rule f)
     end
  else if is_pair exp then
     let val (t1,t2) = dest_pair exp
     in  mk_pair (subst_exp rule t1, subst_exp rule t2)
     end
  else subst rule exp

(* Term t1 occurs in t2? *)
fun occurs_in t1 t2 = can (find_term (aconv t1)) t2;

(* Convert a function definition into a lamba format *)
fun abs_fun def = 
  let 
      val t0 = concl (SPEC_ALL def)
      val (fname, args) = dest_comb (lhs t0)
      val body = rhs t0
      val th1 = prove (mk_eq (fname, mk_pabs(args,body)), 
        SIMP_TAC std_ss [FUN_EQ_THM, pairTheory.FORALL_PROD, Once def])
  in
    th1
  end
  handle HOL_ERR _ => def           (* already an abstraction *)

(*---------------------------------------------------------------------------*)
(* Find the ouput of a term.                                                 *)
(*---------------------------------------------------------------------------*)

fun identify_output t = 
 let
  fun trav t =
      if is_let t then
        let val (v,M,N) = dest_plet t
        in trav N end
      else if is_cond t then
             let val (J, M1, M2) = dest_cond t
                 val t1 = trav M1
                 val t2 = trav M2
             in if t1 = t2 then t1
                else case t1 of 
                     SOME x => (case t2 of 
                                   SOME y => raise Fail "the outputs of two branches are different!"
                                 | NONE => SOME x
                               )
                 |  NONE => t1
             end 
      else if is_pabs t then
           let val (M,N) = dest_pabs t in trav N end
      else if is_comb t then
           NONE
      else if is_pair t orelse is_atomic t then
           SOME t
      else NONE
 in
   valOf (trav t)
 end

(*---------------------------------------------------------------------------*)
(* Sanity check of the source program.                                       *)
(*---------------------------------------------------------------------------*)

fun pre_check (args,body) = 
  let
    val fv = free_vars (mk_pair(args,body))
    val var_type = type_of (hd (fv))
                   handle _ =>  (* no argument *)
                     let fun trav M =
                           if is_plet M then trav (#1 (dest_plet M))
                           else if is_comb M then trav (#2 (dest_comb M))
                           else if is_pair M then trav (#1 (dest_pair M))
                           else type_of M
                     in trav body end
    val sane = List.all (fn x => type_of x = var_type) fv
  in
    (sane, var_type)
  end

(*---------------------------------------------------------------------------*)


end (* struct *)
