structure basic :> basic =
struct

open HolKernel Parse boolSyntax boolLib bossLib pairSyntax;

(*---------------------------------------------------------------------------*)
(* Common used data structures and functions                                 *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* (Atomtic) Variables and Operators                                         *)
(*---------------------------------------------------------------------------*)

(* Is the term a word? *)
fun is_word_literal tm =
  ((is_comb tm) andalso
  let val (c,args) = strip_comb tm
      val {Name,Thy,Ty} = dest_thy_const c
  in Name = "n2w" andalso numSyntax.is_numeral (hd args)
  end)
  handle HOL_ERR _ => false
  ;

(* Is the term an atomic term? *)
fun is_atom t =
    is_var t orelse is_word_literal t orelse 
    numSyntax.is_numeral t orelse is_const t orelse
    is_neg t  (* ~x is considered to be an atom *)
    ;

(* Is the operator a binary arithmetic operator? *)
fun is_binop op0 =
    same_const op0 (Term `$+`) orelse same_const op0 (Term `$-`) orelse
    same_const op0 (Term `$*`) orelse same_const op0 (Term `$**`)
  ;

(* Is the operator a comparison operator? *)
fun is_cmpop op0 =
    same_const op0 (Term `$>`) orelse same_const op0 (Term `$>=`) orelse
    same_const op0 (Term `$=`) orelse same_const op0 (Term `$<=`) orelse
    same_const op0 (Term `$<`);

(* Is the operator a logical operator? *)
fun is_relop op0 = 
    same_const op0 boolSyntax.conjunction orelse 
    same_const op0 boolSyntax.disjunction;

(* Is the the expression in a condition operator an (atomic) comparison expression? *)
fun is_atom_cond tm =
    is_comb tm andalso
    let val (op0,_) = strip_comb tm in
      is_cmpop op0
    end;

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


end (* struct *)
