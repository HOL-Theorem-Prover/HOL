(* =====================================================================*)
(* FILE          : gen_funs.sig                                         *)
(* DESCRIPTION   : This file defines two rules that translate existence *)
(*                 theorems to existence theorems, without using        *)
(*                 the Hilbert Choice operator.                         *)
(*                                                                      *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories               *)
(* DATE          : 92.08.01                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)


structure ExistsFuns :> ExistsFuns =
struct

open utilsLib HolKernel Parse basicHol90Lib;
infix THEN THENL THENC |->;

type term = Term.term;
type thm = Thm.thm;

fun ExistsFun_ERR {function, message} =
    HOL_ERR {message= message,
             origin_function = function,
             origin_structure = "ExistsFuns"}

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q
fun == q x = Type q;

val lemma1 = TAC_PROOF
    (([],
      --`!P:'a -> bool Q. (?x. P x) ==> (!x. (P x ==> Q x)) ==> ?x. Q x`--),
        (REPEAT STRIP_TAC) THEN (EXISTS_TAC (--`x:'a`--)) THEN
        (MP_TAC (Q.ASSUME `P (x:'a)`)) THEN
        (ASM_REWRITE_TAC []));

(*
   exists_thm =                 forall_imp_thm =
     A |- ?x1...xn. P x1...xn     B |- !x1...xn. P x1...xn ==> Q x1...xn
    ---------------------------------------------------------------------
                      A u B |- ?x1...xn. Q x1...xn
*)

val lambdaQ = (--`\x:'a. Q x:bool`--)
(*
val exists_thm =
    ASSUME (--`?(x1:num)(x2:num)(x3:'a). P(((\z.z)x1),((\y.(y,x3))x2))`--)
val forall_imp_thm =
    ASSUME (--`!(a1:num)(a2:num)(a3:'a). P(((\m.m)a1),((\n.(n,a3))a2)) ==>
                 (\z. Q a3 z a2)a1`--)
val thm = EXISTS_FROM_EXISTS_RULE {exists_thm = exists_thm,
                                   forall_imp_thm = forall_imp_thm}
*)

fun EXISTS_FROM_EXISTS_RULE {exists_thm, forall_imp_thm} =
    if is_imp (concl forall_imp_thm)
        then MP forall_imp_thm exists_thm
    else
    let
        val P = rand (concl exists_thm)
        val {Bvar = x, Body = Pbody} = dest_abs P
        val Pbody_thm = ASSUME Pbody
        val PimpQ_thm = SPEC x forall_imp_thm
        val Qbody_thm =
            EXISTS_FROM_EXISTS_RULE {exists_thm = Pbody_thm,
                                     forall_imp_thm = PimpQ_thm}
        val Q = mk_abs {Bvar = x, Body = concl Qbody_thm}
        val all_x_Pbody_imp_Qbody_thm =
            (GEN x (DISCH Pbody Qbody_thm))
    in
        MP
        (MP
         (CONV_RULE (ONCE_DEPTH_CONV BETA_CONV)
          (ISPECL [P, Q]
           (PURE_ONCE_REWRITE_RULE
            [(ALPHA_CONV (mk_var {Name = #Name (dest_var x),
                                  Ty = Type.alpha}) lambdaQ)]
            lemma1)))
         exists_thm)
        all_x_Pbody_imp_Qbody_thm
    end



val lemma2 = TAC_PROOF
    (([],
      --`!f P Q.(?x:'a. P x) ==> (!x. (P x ==> Q (f x))) ==> ?y:'b. Q y`--),
     (REPEAT STRIP_TAC THEN EXISTS_TAC (--`(f:'a -> 'b)(x:'a)`--) THEN
      FIRST_ASSUM MATCH_MP_IMP_TAC THEN FIRST_ASSUM ACCEPT_TAC));

(*
   exists_thm =                 forall_imp_thm =
     A |- ?x1...xn. P x1...xn    B |- !x1...xn. P x1...xn ==>
                                        Q (f1 x1)...(fn xn)
    ---------------------------------------------------------------------
                      A u B |- ?y1...yn. Q y1...yn
*)

val lambdaQ2 = (--`\y:'b.((Q y):bool)`--)
(*
val exists_thm =
    ASSUME (--`?(x1:num)(x2:num)(x3:'a). P(((\z.z)x1),((\y.(y,x3))x2))`--)
val forall_imp_thm =
    ASSUME (--`!(a1:num)(a2:num)(a3:'a). P(((\m.m)a1),((\n.(n,a3))a2)) ==>
                 (\z. Q ((f3:'a -> 'b) a3) z (((\x.f2 x)a2):bool))
                 ((f1:num -> ind) a1)`--)
val thm = GEN_EXISTS_FROM_EXISTS_RULE {exists_thm = exists_thm,
                                       coercion_funs =
                                       [(--`f1:num -> ind`--),
                                        (--`(\y.(\x.f2 x)y):num -> bool`--),
                                        (--`f3:'a -> 'b`--)],
                                       forall_imp_thm = forall_imp_thm}
*)

fun GEN_EXISTS_FROM_EXISTS_RULE {exists_thm,
                                 forall_imp_thm,
                                 coercion_funs = []} =
    if is_imp (concl forall_imp_thm)
        then MP forall_imp_thm exists_thm
    else raise ExistsFun_ERR {function = "GEN_EXISTS_FROM_EXISTS_RULE",
                              message = "coercion_funs and forall_imp_thm" ^
                                        " don't match"}
  | GEN_EXISTS_FROM_EXISTS_RULE {exists_thm,
                                 forall_imp_thm,
                                 coercion_funs = (f::fs)} =
    let
        val P = rand (concl exists_thm)
        val {Bvar = x, Body = Pbody} = dest_abs P
        val Pbody_thm = ASSUME Pbody
        val PimpQ_thm = SPEC x forall_imp_thm
        val Qbody_thm =
            GEN_EXISTS_FROM_EXISTS_RULE {exists_thm = Pbody_thm,
                                         forall_imp_thm = PimpQ_thm,
                                         coercion_funs = fs}
        val Qbody = concl Qbody_thm  (* Q (f x) *)
        val fx = mk_comb{Rator = f, Rand = x}
        val fx_red = if is_abs f then beta_conv fx else fx
        val y = variant
                ((free_vars P) @ (free_vars Qbody))
                (mk_var{Name = #Name (dest_var x),
                        Ty = hd(tl(#Args(dest_type(type_of f))))})
        val Q = mk_abs {Bvar = y,    (* \y.Q y *)
                        Body = subst [fx |-> y, fx_red |-> y] Qbody}
        val all_x_Pbody_imp_Qbody_thm = GEN x (DISCH Pbody Qbody_thm)
        val speced_lemma2 = ISPECL [f,P,Q] lemma2
        val conv_thm = CONV_RULE
            ((RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV BETA_CONV)))) THENC
             (RAND_CONV
              ((RATOR_CONV (RAND_CONV (RAND_CONV
              (ABS_CONV
               ((RATOR_CONV (RAND_CONV BETA_CONV)) THENC
                (RAND_CONV (DEPTH_CONV BETA_CONV))))))) THENC
               (RAND_CONV (RAND_CONV (ABS_CONV BETA_CONV)))))) speced_lemma2
        val imp_exists_y_Qy =
            CONV_RULE (RATOR_CONV (RAND_CONV (RAND_CONV (ABS_CONV
            (RAND_CONV (DEPTH_CONV BETA_CONV))))))
            (MP conv_thm exists_thm)
        val red_all_x_Pbody_imp_Qbody_thm = CONV_RULE
            (RAND_CONV(ABS_CONV(RAND_CONV (DEPTH_CONV BETA_CONV))))
            all_x_Pbody_imp_Qbody_thm

    in
        MP imp_exists_y_Qy red_all_x_Pbody_imp_Qbody_thm
    end  handle e as HOL_ERR {message=message,
                              origin_function = funt,
                              origin_structure = str} =>
        case funt of "GEN_EXISTS_FROM_EXISTS_RULE" => raise e
                   | _ =>
        raise ExistsFun_ERR {function = "GEN_EXISTS_FROM_EXISTS_RULE",
                             message = str^"."^funt^": "^message}
end;
