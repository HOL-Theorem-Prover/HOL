(* ===================================================================== *)
(* FILE          : barendregt.sml                                        *)
(* VERSION       : 1.0                                                   *)
(* DESCRIPTION   : Tactics for working with substitutions naively.       *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : September 3, 2000                                     *)
(* COPYRIGHT     : Copyright (c) 2000 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


structure barendregt :> barendregt =
struct

open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;

(*
type term = Term.term
type thm = Thm.thm;
*)



local


(* In interactive sessions, do:

app load ["pairTheory",
          "listLib", "numTheory", "Num_induct",
          "pred_setTheory", "pred_setLib",
          "mutualLib", "ind_defLib", "bossLib",
          "ind_rel", "dep_rewrite",
          "more_listTheory", "more_setTheory", "variableTheory",
          "termTheory", "alphaTheory", "liftTheory"
         ];

*)


open pred_setTheory more_setTheory;
open listTheory;
open liftTheory;
open dep_rewrite;
open Rsyntax;


val LIST_INDUCT_TAC =
    INDUCT_THEN list_induction ASSUME_TAC;

val REWRITE_THM = fn th => REWRITE_TAC[th];
val UNDISCH_LAST_TAC = POP_ASSUM MP_TAC;

fun REWRITE_ASSUM_TAC rths :tactic =
    RULE_ASSUM_TAC (REWRITE_RULE rths);

fun REWRITE_ALL_TAC rths :tactic =
    REWRITE_TAC rths  THEN
    REWRITE_ASSUM_TAC rths;

val REWRITE_ALL_THM = fn th => REWRITE_ALL_TAC[th];



(*
val (asl,gl) = top_goal();
*)


fun TACTIC_ERR{function,message} =
    Feedback.mk_HOL_ERR "Tactic" function message

fun failwith function =
   ( (* if debug_fail then
         print_string ("Failure in Cond_rewrite: "^function^"\n")
     else (); *)
    raise TACTIC_ERR{function = function,message = ""});


fun mk_subst l = map (fn (residue:'a, redex:'b) =>
                         {redex=redex,residue=residue}) l;
val INST_TY_TERM = (Drule.INST_TY_TERM) o (mk_subst##mk_subst);
fun dest_subst l = map (fn {residue,redex} => (residue:'a, redex:'b)) l;



val get_shift_matches = (dest_subst##dest_subst) o
                        (Term.match_term “Lam x t :'a term”);
(*
val get_shift_matches = Psyntax.match_term “Lam x t :'a term”;
*)

(* SEARCH_matches applies the function f to every subterm of the
   given term tm, except to variables or constants, for which
   SEARCH_matches always raises an exception.
   The return value is a list of 'a objects, as produced by f
   for every subterm of tm, all collected into one list.
*)
fun SEARCH_matches (f:term->'a list) tm =
   ( (* if debug_matches then (print_string "SEARCH_matches: ";
                    print_term tm; print_newline()) else (); *)
    if is_comb tm then
       (let val {Rator,Rand} = Rsyntax.dest_comb tm
            val m1 = (f Rator handle _ => [])
            val m2 = (f Rand  handle _ => [])
         in  append m1 m2
        end)
    else
    if is_abs tm then
       let val {Bvar,Body} = Rsyntax.dest_abs tm in
           (f Body handle _ => [])
       end
    else failwith "SEARCH_matches");

(*
fun SUB_matches (f:term->'a) tm =
   ( (* if debug_matches then (print_string "SUB_matches: ";
                    print_term tm; print_newline()) else (); *)
    if is_comb tm then
       (let val {Rator,Rand} = Rsyntax.dest_comb tm in
        (f Rator handle _ => f Rand)
        end)
    else
    if is_abs tm then
       let val {Bvar,Body} = Rsyntax.dest_abs tm in
           f Body
       end
    else failwith "SUB_matches");

fun ONCE_DEPTH_matches (f:term->'a) tm =
     ( (* if debug_matches then
        (print_string "ONCE_DEPTH_matches: "; print_term tm; print_newline())
      else (); *)
       (f tm handle _ => (SUB_matches (ONCE_DEPTH_matches f) tm)));
*)

fun ALL_DEPTH_matches (f:term->'a) tm =
     ( (* if debug_matches then
        (print_string "ONCE_DEPTH_matches: "; print_term tm; print_newline())
      else (); *)
       ([f tm] handle _ => (SEARCH_matches (ALL_DEPTH_matches f) tm)));


fun remove_s_matches matches =
    let val (terms_list,types_list) = matches;
        val nsterms = filter (fn (f,s) => not (#Name(dest_var s) = "s"))
                             terms_list
    in
        (nsterms,([]:(hol_type * hol_type) list))
    end;


(* ------------------------------------------------------------------ *)
(* Need to group together matches which have the same "x" match;      *)
(* for each such group, we should compute a variant of the x once,    *)
(* and then use the same variant x' for each of the new shifted       *)
(* bodies of the SIGMA expressions.  This ensures that SIGMA        *)
(* expressions which had identical bound variables before, still      *)
(* have identical bound variables afterwards.  This is important.     *)
(* ------------------------------------------------------------------ *)

fun find_x (match::matches) =
    let val (l,r) = match in
      if r ~~ “x:var” then l else find_x matches
    end
  | find_x [] = “x:var”;

fun find_t (match::matches) =
    let val (l,r) = match in
      if r ~~ “t:'a term” then l else find_t matches
    end
  | find_t [] = “t:'a term”;

fun sort_matches matchesl =
    let val (mtermsl,_) = split matchesl
        val xtms = map find_x mtermsl
        val dist_xtms = op_mk_set aconv xtms
        val xs_termsl = zip xtms mtermsl
        val xmgroups = map (fn dx => filter (fn (x,matches) => (x ~~ dx))
                                            xs_termsl)
                           dist_xtms
        val mgroups = map (map snd) xmgroups
        val t's = map (map find_t) mgroups
        val mtygroups = map (map (fn tms =>
                                     (tms, ([]:(hol_type * hol_type) list))))
                            mgroups
        val tmgroups = zip (zip dist_xtms t's) mtygroups
    in
        tmgroups
    end;



val EVERY_LENGTH_LEMMA = TAC_PROOF(([],
    “!os (a:'a) as.
         (LENGTH os = LENGTH (CONS a as)) ==>
         (?(o':'b) os'. (LENGTH os' = LENGTH as) /\ (os = CONS o' os'))”),
    LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,arithmeticTheory.SUC_NOT]
    THEN REWRITE_TAC[prim_recTheory.INV_SUC_EQ,CONS_11]
    THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN EXISTS_TAC “h:'b”
    THEN EXISTS_TAC “os:'b list”
    THEN ASM_REWRITE_TAC[]
   );

val NIL_LENGTH_LEMMA = TAC_PROOF(([],
    “!os:'b list.
         (LENGTH os = LENGTH ([]:'a list)) ==>
         (os = [])”),
    REWRITE_TAC[LENGTH,LENGTH_NIL]
   );

fun REPEAT_N 0 tac = ALL_TAC
  | REPEAT_N n tac = (tac THEN REPEAT_N (n-1) tac);



fun make_new_objects thm =
    let val cn = concl thm
        val rhs = #rhs(dest_eq cn)
        val lst = #Rand(dest_comb rhs)
        fun length_list lst =
             if lst ~~ “[]:obj list” then 0
             else  1 + length_list (#Rand(dest_comb lst))
        val n = length_list lst
        fun make_one 0 thm = thm
          | make_one n thm = thm
    in
        (make_one n thm; n)
    end;


(*
fun MAKE_CLEAN_VAR_THM free_vrs matches =
    let val (terms_list,types_list) = matches;
        val ftm = foldr (fn (x,s) =>
                           if type_of x = (==`:var`==)
                             then “^x INSERT ^s”
                           else if type_of x = (==`:var list`==)
                             then “SL ^x UNION ^s”
                           else if type_of x = (==`:var set`==)
                             then “^x UNION ^s”
                           else if type_of x = (==`:'a term`==)
                             then “(FV ^x) UNION ^s”
                           else s)
                         “{}:var set”
                         free_vrs;
        val sterms = (ftm, “s:var set”)::terms_list;
        val smatches = (sterms,([]:(hol_type * hol_type) list));
        val sigma_thm = INST_TY_TERM smatches (SPEC_ALL SIGMA_CLEAN_VAR);
    in
        REWRITE_RULE[FINITE_EMPTY,FINITE_INSERT,FINITE_UNION,
                     FINITE_FV_object,IN,IN_UNION,DE_MORGAN_THM]
                   sigma_thm
    end;
*)


fun MAKE_LIST_CLEAN_VAR_THM free_vrs (x, os) =
    let val ftm = foldr (fn (x,s) =>
                           if type_of x = (==`:var`==)
                             then “^x INSERT ^s”
                           else if type_of x = (==`:var list`==)
                             then “SL ^x UNION ^s”
                           else if type_of x = (==`:var set`==)
                             then “^x UNION ^s”
                           else if type_of x = (==`:'a term`==)
                             then “(FV ^x) UNION ^s”
                           else s)
                         “{}:var set”
                         free_vrs;
         val mk_term_list = foldr (fn (a,os) => “CONS ^a ^os”)
                                 “[]:'a term list”
         val os_tm = mk_term_list os
         val lambda_thm = SPECL[ftm,x,os_tm] LAMBDA_LIST_CLEAN_VAR
         val exists_list_thm =
                REWRITE_RULE[FINITE_EMPTY,FINITE_INSERT,FINITE_UNION,
                             FINITE_FV,IN,IN_UNION,DE_MORGAN_THM]
                           lambda_thm
         val os' = foldr (fn (v,l) => (Term.variant (l @ free_vrs) v)::l)
                         [] os
         val os'_tm = mk_term_list os'
         val {Bvar=zvar, Body=body1} = dest_exists (concl exists_list_thm)
         val {Rator=exists_binder, Rand=body2} = dest_comb body1
         val os'_vr = #Bvar(dest_abs body2)
         val exists_tm1 = beta_conv (mk_comb{Rator=body2, Rand=os'_tm})
         val exists_tm2 = foldr (fn (o1,tm) => mk_exists{Bvar=o1, Body=tm})
                                exists_tm1  os'
         val exists_tm  = mk_exists{Bvar=zvar, Body=exists_tm2}
         val exists_thm = TAC_PROOF (([],exists_tm),
               STRIP_ASSUME_TAC exists_list_thm
               THEN ASSUM_LIST (fn asl1 =>
                      EXISTS_TAC (#Rand (dest_comb (#Rator(dest_comb
                            (#Rand(dest_comb (concl (hd (rev asl1))))))))))
               THEN REPEAT
                     (POP_ASSUM (fn lth =>
                         STRIP_ASSUME_TAC (MATCH_MP EVERY_LENGTH_LEMMA lth))
                      THEN FIRST_ASSUM (fn eth =>
                           EXISTS_TAC
                             (#Rand (dest_comb (#Rator(dest_comb
                                  (#rhs(dest_eq (concl eth))))))))
                      THEN POP_ASSUM REWRITE_ALL_THM)
               THEN POP_ASSUM (REWRITE_ALL_THM o MATCH_MP NIL_LENGTH_LEMMA)
               THEN ASM_REWRITE_TAC[LENGTH]
          )
    in
         BETA_RULE (REWRITE_RULE[EVERY_DEF,MAP2,combinTheory.I_THM] exists_thm)
    end;


val MAKE_SIMPLE_SUBST_TAC =
    DEP_REWRITE_TAC[LAMBDA_SUBST_SIMPLE]
    THEN CONJ_TAC
    THENL
      [ ASM_REWRITE_TAC[termTheory.BV_subst_def,pairTheory.FST,IN]
        THEN REPEAT (CHANGED_TAC
               (ASM_REWRITE_TAC[IN_DIFF,IN,FV_term,FV_term_subst]
                THEN DEP_REWRITE_TAC[NOT_IN_FV_subst,NOT_IN_FV_subst2]))
        THEN ASM_REWRITE_TAC[],

        ALL_TAC
      ];


(*
val SHIFT_LAMBDA_TAC :tactic = fn (asl,gl) =>
    let val matches = ONCE_DEPTH_matches get_shift_matches gl;
        val free_vrs = mk_set (append (free_vars gl)
                                      (flatten (map free_vars asl)));
        val lambda_thm = MAKE_CLEAN_VAR_THM free_vrs matches
    in
        (STRIP_ASSUME_TAC lambda_thm
         THEN FIRST_ASSUM REWRITE_THM
         THEN UNDISCH_LAST_TAC
         THEN FIRST_ASSUM (fn hght => EVERY_ASSUM (fn th =>
                             ASSUME_TAC (MATCH_MP th hght)
                             handle _ => ALL_TAC))
         THEN DISCH_TAC) (asl,gl)
    end;
*)
val SHIFT_LAMBDAS_TAC :tactic = fn (asl,gl) =>
    let
      val meq = pair_eq (list_eq (pair_eq aconv aconv)) equal
      val matchesl = op_mk_set meq (ALL_DEPTH_matches get_shift_matches gl);
        val match_groups = sort_matches matchesl
        val (tags,groups) = split match_groups
        (* val (xs,bodies) = split tags *)
        val free_vrs = op_mk_set aconv
                                 (append (free_vars gl)
                                         (flatten (map free_vars asl)));
        val lambda_thms = map (MAKE_LIST_CLEAN_VAR_THM free_vrs) tags
        val t_lambda_thms = zip tags lambda_thms
      (*  val lambda_thm = map (MAKE_CLEAN_VAR_THM free_vrs) matchesl *)
    in
       if null matchesl then ONCE_REWRITE_TAC[SUB_term] (asl,gl)
       else
       (EVERY (map (fn ((x,os),lambda_thm) =>
         let val n = length os in
          STRIP_ASSUME_TAC lambda_thm
          THEN POP_ASSUM (fn th => ALL_TAC)
          THEN REPEAT_N n
                  (FIRST_ASSUM REWRITE_THM THEN UNDISCH_LAST_TAC)
          THEN REPEAT_N n UNDISCH_LAST_TAC (* the HEIGHT = HEIGHT asms *)
          THEN REPEAT_N n
                  (DISCH_THEN (fn hght =>
                                 EVERY_ASSUM (fn th =>
                                    ASSUME_TAC (MATCH_MP th hght)
                                     handle _ => ALL_TAC)
                                 THEN ASSUME_TAC hght))
          THEN REPEAT_N n DISCH_TAC
         end)
                   t_lambda_thms) )
       (* above is tactic, applied to: *)
       (asl,gl)
    end;


(* ================================================================== *)
(* End of local declarations.                                         *)
(* Beginning of exported declarations.                                *)
(* ================================================================== *)

in


val SHIFT_LAMBDAS_TAC = SHIFT_LAMBDAS_TAC;


val MAKE_SIMPLE_SUBST_TAC = MAKE_SIMPLE_SUBST_TAC;

val SIMPLE_SUBST_TAC =
        SHIFT_LAMBDAS_TAC THEN MAKE_SIMPLE_SUBST_TAC;


end (* of local declaration block *)

end;  (* of structure barendregt *)


(* TEST EXAMPLES:

load "MutualIndThen";
open MutualIndThen;

(* Barendregt's Substitution Lemma, 2.1.16, page 27: *)

val BARENDREGT_SUBSTITUTION_LEMMA = TAC_PROOF
   (([],
    “!(M:'a term) N L x y.
          ~(x = y) /\ ~(x IN FV L) ==>
          (((M <[ [x,N]) <[ [y,L]) =
           ((M <[ [y,L]) <[ [x, (N <[ [y,L])]))”),
    MUTUAL_INDUCT_THEN term_height_induct ASSUME_TAC
    THENL
      [ (* Con case *)
        REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term,SUB],

        (* Var case *)
        REPEAT STRIP_TAC
        THEN REWRITE_TAC[SUB_term,SUB]
        THEN COND_CASES_TAC
        THENL
          [ ASM_REWRITE_TAC[SUB_term,SUB],

            REWRITE_TAC[SUB_term,SUB]
            THEN COND_CASES_TAC
            THENL
              [ IMP_RES_THEN REWRITE_THM subst_EMPTY,

                ASM_REWRITE_TAC[SUB_term,SUB]
              ]
          ],

        (* App case *)
        REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[SUB_term],

        (* Lam case *)
        REPEAT STRIP_TAC
        THEN SIMPLE_SUBST_TAC
        THEN DEP_ASM_REWRITE_TAC[]
      ]
   );

*)
