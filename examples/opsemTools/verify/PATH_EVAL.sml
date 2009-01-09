
(* Stuff needed when running interactively
quietdec := true; (* turn off printing *)
app load ["newOpsemTheory","pairSyntax", "intLib","Omega","intSimps",
          "computeLib", "finite_mapTheory",
          "relationTheory", "stringLib"];
open newOpsemTheory bossLib pairSyntax intLib Omega
     computeLib finite_mapTheory relationTheory stringLib;
quietdec := false; (* turn printing back on *)
*)

open HolKernel Parse boolLib
     newOpsemTheory bossLib pairSyntax intLib Omega intSimps
     computeLib finite_mapTheory relationTheory stringLib;

val _ =
 add_funs
  [outcome_case_def,
   outcome_case_if,
   pair_case_if,
   CONS_if,
   ScalarOf_if,
   RUN,
   STEP1,
   FUPDATE_LIST_THM,
   DOMSUB_FUPDATE_THM,
   DOMSUB_FAPPLY_THM,
   FUPDATE_EQ,
   DOMSUB_FEMPTY,
   FDOM_FUPDATE,
   FAPPLY_FUPDATE_THM,
   FDOM_FEMPTY,
   pred_setTheory.IN_INSERT,
   pred_setTheory.NOT_IN_EMPTY,
   ACC_STEP,
   integerTheory.NUM_OF_INT
  ];

(* 
EVAL_ASSUME tm applies EVAL to tm to create |- tm = tm', 
assumes tm' and then returns |- tm
*)
fun EVAL_ASSUME tm =
 let val eval_th = EVAL tm
     val tm' = rhs(concl eval_th)
 in
  EQ_MP (SYM eval_th) (ASSUME tm')
 end;

(*
EVAL_DISCH asm (|- tm) applies EVAL to asm to create |- asm = asm',
discharges asm' to get |- asm' ==> tm and then returns |- asm => tm
*)
fun EVAL_DISCH asm th =
 let val eval_th = EVAL asm
     val asm' = rhs(concl eval_th)
 in
  CONV_RULE 
   (RATOR_CONV(RAND_CONV(REWR_CONV(SYM eval_th))))
   (DISCH asm' th)
 end;


(********************************************************************


SYM_RUN solv (|- P s) ``l`` 

Repeatedly applies STEP1 symbolically starting with the configuration
``(l,s)`` and returning a theorem |- TC SMALL_EVAL (l,s) ([],s'),
where s' may be a conditional term if there are conditions not
resolved by the solver (see below).

The conclusion of the second theorem argument to SYM_RUN should be a
term of the form ``P s`` where pre is a predicate and s a state.
For example, ASSUME ``(P:state->bool) s`` will work.

The precondition P is carried forward and augmented with additional
terms representing the effects of assignments and the branches of
conditionals entered.

Whenever a conditional with test b is encountered the solver is called
on ``P' ==> b`` and if that fails on ``P' ==> ~b`` where P' is the
accumulated precondition.  If the solver can resolve such a condition
then only the corresponding arm of the conditional is executed. If the
solver fails then both arms of the conditional are symbolically
executed and the results combined. 

The solver solv should be a function that maps a term to an equational
theorem whose left hand side is the supplied term (i.e. a conversion
in HOL jargon). If tm is a term that can be solved then solv tm should
return |- tm = T. If tm is a term that can't be solved then solv tm
can return |- tm = tm' for any tm' not equal to T (e.g. tm' = tm).

SYM_RUN was quite tricky to program and it may well still have bugs
(these can't cause false theorems to be proved, but they might cause
it to fail unexpectedly). There is some tracing infrastructure for
debugging remaining in the code below (switched off by
default). Executing init_trace() switches on tracing and clears the ML
reference history. After executing SYM_RUN, a list of the arguments it
was invoked on is recorded in history (most recent first).

********************************************************************)
val sym_run_trace = ref false;                    (* For debugging *)
val sym_run_history = ref([]:(thm*term) list);    (* For debugging *)
fun init_trace () =                               (* For debugging *)
 (sym_run_trace   := true;                        (* For debugging *)
  sym_run_history := ([]:(thm*term) list));       (* For debugging *)

fun SYM_RUN solv pre_th l =
(if (!sym_run_trace)                              (* For debugging *)
  then sym_run_history                            (* For debugging *)
        := (pre_th,l) :: (!sym_run_history)       (* For debugging *)
  else ();                                        (* For debugging *)
 if is_const l andalso (fst(dest_const l) = "NIL")
  then (print "Can't execute an empty list of commands.\n";
        print_thm SMALL_EVAL_NIL;
        print "\n";
        fail())
  else
   let val (pre,s) = dest_comb(concl pre_th)
       val step1_th = EVAL ``STEP1 (^l,^s)``
       val ls' = rhs(concl step1_th)
   in 
    if is_cond ls'
     then
      let val bexp = hd(snd(strip_comb(rand(rator l))))
          val (b,x,y) = dest_cond ls'
          val eval_pre_th = EVAL_RULE pre_th
          val eval_pre = concl eval_pre_th
          val solv_tm = mk_imp(concl eval_pre_th, b)
          val solv_T_th = solv solv_tm          
      in
       if rhs(concl solv_T_th) = ``T``
        then 
         let val solv_asm_th = EQT_INTRO(MP (EQT_ELIM solv_T_th) eval_pre_th)
             val step1_T_th = LIST_MP[eval_pre_th,solv_T_th,step1_th](SPECL[eval_pre,b,l,s,x,y]STEP1_T)
             val (l'_T,res_T) = dest_pair(rand(concl step1_T_th))
             val s' = rand res_T 
             val small_eval_T_th = EQ_MP (SPECL[l,s,l'_T,s']STEP1_SMALL_EVAL) step1_T_th
             val tc_small_eval_T_th = 
                  MP 
                   (SPECL[mk_pair(l,s),mk_pair(l'_T,s')]SMALL_EVAL_TC_SMALL_EVAL) 
                   small_eval_T_th
             val safe_var = mk_var("%s%", type_of s)
             val pre_T = ``\safe_var. ^pre safe_var /\ beval ^bexp safe_var``
             val pre_T_th = EQT_ELIM
                            ((BETA_CONV 
                              THENC RATOR_CONV(RAND_CONV(REWRITE_CONV[pre_th]))
                              THENC REWR_CONV LEFT_T_ELIM
                              THENC EVAL
                              THENC REWR_CONV solv_asm_th)
                            ``^pre_T ^s``)
             val sym_run_T_th = SYM_RUN solv pre_T_th l'_T
         in
          MATCH_MP (MATCH_MP TC_SMALL_EVAL_TRANS tc_small_eval_T_th) sym_run_T_th
         end 
        else 
         let val solv_F_th = solv ``^(concl eval_pre_th) ==> ~^b``
         in
          if rhs(concl solv_F_th) = ``T``
           then
            let val solv_asm_th = MP (EQT_ELIM solv_F_th) eval_pre_th
                val solv_asm_F_th = MATCH_MP NOT_EQ_F solv_asm_th
                val step1_F_th = LIST_MP[eval_pre_th,solv_F_th,step1_th](SPECL[eval_pre,b,l,s,x,y]STEP1_F)
                val (l'_F,res_F) = dest_pair(rand(concl step1_F_th))
                val s' = rand res_F
                val small_eval_F_th = EQ_MP (SPECL[l,s,l'_F,s']STEP1_SMALL_EVAL) step1_F_th
                val tc_small_eval_F_th = 
                     MP 
                      (SPECL[mk_pair(l,s),mk_pair(l'_F,s')]SMALL_EVAL_TC_SMALL_EVAL) 
                      small_eval_F_th
                val safe_var = mk_var("%s%", type_of s)
                val pre_F = ``\^safe_var. ^pre ^safe_var /\ ~(beval ^bexp ^safe_var)``
                val pre_F_th = EQT_ELIM
                               ((BETA_CONV 
                                 THENC RATOR_CONV(RAND_CONV(REWRITE_CONV[pre_th]))
                                 THENC REWR_CONV LEFT_T_ELIM
                                 THENC RAND_CONV EVAL
                                 THENC REWR_CONV(EQT_INTRO solv_asm_th))
                               ``^pre_F ^s``)
                val sym_run_F_th = SYM_RUN solv pre_F_th l'_F
            in
             MATCH_MP (MATCH_MP TC_SMALL_EVAL_TRANS tc_small_eval_F_th) sym_run_F_th
            end
           else 
            let val asm_b_T_th = EQT_INTRO(EVAL_ASSUME b)
                val asm_b_F_th = MP (SPEC b NOT_IMP_EQ_F) (EVAL_ASSUME(mk_neg b))
                val step1_T_th = CONV_RULE
                                  (RHS_CONV
                                    (RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV asm_b_T_th)))
                                     THENC COND_CONV)) step1_th
                val step1_F_th = CONV_RULE
                                  (RHS_CONV
                                    (RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV asm_b_F_th)))
                                     THENC COND_CONV)) step1_th
                val bexp_T_th = EVAL ``beval ^bexp ^s``
                val bexp_F_th = RAND_CONV EVAL ``~(beval ^bexp ^s)``
                val safe_var = mk_var("%s%", type_of s)
                val pre_T = ``\safe_var. ^pre safe_var /\ beval ^bexp safe_var``
                val pre_F = ``\safe_var. ^pre safe_var /\ ~(beval ^bexp safe_var)``
                val bexp_T_asm_th = CONV_RULE
                                     (RAND_CONV(REWR_CONV(EQT_INTRO(EVAL_ASSUME b)))) 
                                     bexp_T_th
                val bexp_F_asm_th = CONV_RULE
                                     (RAND_CONV(REWR_CONV(EQT_INTRO(EVAL_ASSUME(mk_neg b))))) 
                                     bexp_F_th
                val (l'_T,res_T) = dest_pair x
                val (l'_F,res_F) = dest_pair y
                val _ = if aconv res_T res_F
                         then ()
                         else (print "result in true branch:\n";
                               print_term res_T;
                               print "\nshould be same as result in false branch:\n";
                               print_term res_F;
                               fail())
                val s' = rand res_T
                val pre_T_th = 
                     LIST_MP[pre_th,bexp_T_asm_th](SPECL[pre,``beval ^bexp``,s]ABS_T_CONJ)
                val pre_F_th = 
                     LIST_MP[pre_th,bexp_F_asm_th](SPECL[pre,``beval ^bexp``,s]ABS_F_CONJ)
                val sym_run_T_th = SYM_RUN solv pre_T_th l'_T
                val sym_run_F_th = SYM_RUN solv pre_F_th l'_F
                val small_eval_T_th = EQ_MP (SPECL[l,s,l'_T,s']STEP1_SMALL_EVAL) step1_T_th
                val tc_small_eval_T_th = 
                     MP 
                      (SPECL[mk_pair(l,s),mk_pair(l'_T,s')]SMALL_EVAL_TC_SMALL_EVAL) 
                      small_eval_T_th
                val small_eval_F_th = EQ_MP (SPECL[l,s,l'_F,s']STEP1_SMALL_EVAL) step1_F_th
                val tc_small_eval_F_th = 
                     MP 
                      (SPECL[mk_pair(l,s),mk_pair(l'_F,s')]SMALL_EVAL_TC_SMALL_EVAL) 
                      small_eval_F_th
                val tc_small_eval_trans_T_th  =
                     MATCH_MP (MATCH_MP TC_SMALL_EVAL_TRANS tc_small_eval_T_th) sym_run_T_th
                val tc_small_eval_trans_F_th  =
                     MATCH_MP (MATCH_MP TC_SMALL_EVAL_TRANS tc_small_eval_F_th) sym_run_F_th
            in
             MATCH_MP 
               TC_SMALL_EVAL_IF 
                (CONJ
                  (EVAL_DISCH b tc_small_eval_trans_T_th)
                  (EVAL_DISCH (mk_neg b) tc_small_eval_trans_F_th))
            end
         end 
      end
     else 
      let val (l',res) = dest_pair ls'
          val s' = rand res
          val small_eval_th = EQ_MP (SPECL[l,s,l',s']STEP1_SMALL_EVAL) step1_th
           val tc_small_eval_th = 
               MP 
                 (SPECL[mk_pair(l,s),mk_pair(l',s')]SMALL_EVAL_TC_SMALL_EVAL) 
                small_eval_th
       in
       if is_const l' andalso (fst(dest_const l') = "NIL")
          then tc_small_eval_th
         else 
           let val c = rand(rator l)
               val acc_th = EVAL ``ACC_PRED ^pre ^c ^s``
               val renamed_acc_th = 
                   CONV_RULE 
                     (RHS_CONV(ALPHA_CONV ``s:state``) ORELSEC ALL_CONV) 
                    acc_th 
               val (l',res) = dest_pair ls'
               val (resop,s') = dest_comb res
               val step1_acc_th = 
                  LIST_MP[pre_th,step1_th](SPECL[c, pre, rand l, l', s, s']STEP1_ACC_PRED)
               val pre_th' = SUBS [renamed_acc_th] step1_acc_th
               val tc_small_eval_th' = SYM_RUN solv pre_th' l'
           in
           MATCH_MP
             (MATCH_MP TC_SMALL_EVAL_TRANS tc_small_eval_th)
            tc_small_eval_th'
           end
      end
   end);


(********************************************************************

"SYMBOLIC_EVAL solv pre c" proves |- EVAL c s s' by invoking
SYM_RUN and then using the theorem EVAL_SMALL_EVAL:

|- !c s1 s2. EVAL c s1 s2 = TC SMALL_EVAL ([c],s1) ([],s2) 

********************************************************************)

fun SYMBOLIC_EVAL solv pre c = 
 PURE_REWRITE_RULE
  [GSYM EVAL_SMALL_EVAL] 
  (SYM_RUN solv (EVAL_ASSUME ``^pre ^(bvar pre)``) ``[^c]``);

(* =======================================================================
Turn a formula into a predicate on states. Examples:

 formToPred "s" ``EMPTY`` =
  ``\s. T``

 formToPred "s" ``(i < j ==> (Result = 1))`` =
  ``\s.
      ScalarOf (s ' "i") < ScalarOf (s ' "j") ==>
      (ScalarOf (s ' "Result") = 1)``

Note: things will go wrong if "s" is a variable in a program.

======================================================================= *)
local
(* Local auxiliary function for making body of lambda-abstraction *)
fun formToPredBody svar tm =
 if is_var tm
  then ``ScalarOf(^svar ' ^(stringLib.fromMLstring(fst(dest_var tm))))`` else
 if is_const tm
  then (if fst(dest_const tm) = "EMPTY" then ``T`` else tm) else
 if is_comb tm 
  then mk_comb
        (formToPredBody svar (rator tm), formToPredBody svar (rand tm))
  else (print_term tm; 
        print "\n precondition cannot contain an abstraction\n"; 
        fail())
in
(* Exported function *)
fun formToPred s tm =
 let val svar = mk_var(s,``:string|->value``)
 in
  ``\^svar. ^(formToPredBody svar tm)``
 end
end;


(* Get set of variables read in a numerical expression (nexp) *)
fun nexp_vars nex =
 let val (opr,args) = strip_comb nex  (* syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Var","Arr","Const","Plus","Times","Sub"])
              then (print name; 
                    print " is not an nexp constructor\n"; 
                    fail())
              else ()
 in
  case name of
    "Var"      => [nex]
  | "Arr"      => insert (rator nex) (nexp_vars(rand nex))
  | "Const"    => []
  | "Plus"     => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "Times"    => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "Sub"      => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | _          => (print "BUG in nexp_vars! "; print name; fail())
 end;

(* Get set of variables read in a boolean expression (bexp) *)
fun bexp_vars bex =
 let val (opr,args) = strip_comb bex  (* syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Equal","Less","LessEq","And","Or","Not"])
              then (print name; 
                    print " is not a bexp constructor\n"; 
                    fail())
              else ()
 in
  case name of
    "Equal"    => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "Less"     => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "LessEq"   => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "And"      => union (bexp_vars(el 1 args)) (bexp_vars(el 2 args))
  | "Or"       => union (bexp_vars(el 1 args)) (bexp_vars(el 2 args))
  | "Not"      => bexp_vars(el 1 args)
  | _          => (print "BUG in bexp_vars! "; print name; fail())
 end;
 

(* Get set of variables read or assigned to in a program *)
fun program_vars c =
 let val (opr,args) = strip_comb c  (* N.B. syntax error if "op" instead of "opr" *)
     val _ = if not(is_const opr)
              then (print_term opr; 
                    print " is not a constant\n"; 
                    fail())
              else ()
     val name = fst(dest_const opr)
     val _ = if not(mem name ["Skip","Assign","ArrayAssign","Dispose",
                              "Seq", "Cond","While","Local","Assert"])
              then (print name; 
                    print " is not a program constructor\n"; 
                    fail())
              else ()
 in
  case name of
    "Skip"        => []
  | "Assign"      => insert 
                      (mk_comb(``Var``, el 1 args)) 
                      (nexp_vars(el 2 args))
  | "ArrayAssign" => insert 
                      (mk_comb(``Arr``, el 1 args))
                      (union
                       (nexp_vars(el 2 args))
                       (nexp_vars(el 3 args)))
  | "Dispose"     => []
  | "Seq"         => union
                      (program_vars(el 1 args)) 
                      (program_vars(el 2 args))
  | "Cond"        => union
                      (bexp_vars(el 1 args))
                      (union
                        (program_vars(el 2 args))
                        (program_vars(el 3 args)))
  | "While"       => union (bexp_vars(el 1 args)) (program_vars(el 2 args))
  | "Local"       => []
  | "Assert"      => []
  | _             => (print "BUG in program_vars! "; print name; fail())
 end;

(* 
Construct: FEMPTY |++ [("v1",v1);...;("vn",vn)]
where v1,...,vn are the variables read or written in c
*)


fun MAKE_STATE_LIST_FROM_VARS vars =
 let val pairs = 
      map
       (fn tm => 
         if aconv (rator tm) ``Var``
          then ``(^(rand tm), Scalar ^(mk_var(fromHOLstring (rand tm),``:int``)))`` else
         if aconv (rator tm) ``Arr``
          then ``(^(rand tm), Array ^(mk_var(fromHOLstring (rand tm),``:(num |-> int)``)))``
          else (print "BUG in MAKE_STATE_LIST_FROM_VARS! "; print_term tm; fail()))
       vars
 in
  listSyntax.mk_list(pairs,``:string#value``)
 end;

fun MAKE_STATE_LIST c = MAKE_STATE_LIST_FROM_VARS(program_vars c);

fun MAKE_STATE c = ``FEMPTY |++ ^(MAKE_STATE_LIST_FROM_VARS(program_vars c))``;

(*
fun MAKE_STATE_FROM_VARS vars =
 let val pairs = map 
                  (fn tm => ``(^tm, Scalar ^(mk_var(fromHOLstring tm,``:int``)))``)
                  vars
 in
  ``FEMPTY |++ ^(listSyntax.mk_list(pairs,``:string#value``))``
 end;

fun MAKE_STATE c = MAKE_STATE_FROM_VARS(program_vars c);
*)


(*
Construct a theorem by assuming

 ``^(formToPred pre) (FEMPTY |+ ("v1",v1) |+ ... |+ ("vn",vn))``

where v1,...,vn are the variables read or written in c,
and pre is a precondition on v1,...,vn.
*)

fun MAKE_PRE asm c =
 let val var_names = program_vars c
     val vars = map (fn t => mk_var(fromHOLstring t, ``:value``)) var_names
     val svar = variant vars ``s:state``
     val svar_name = fst(dest_var svar)
     val pre = formToPred svar_name asm
     val pre_s = mk_comb(pre, rhs(concl(PURE_REWRITE_CONV[FUPDATE_LIST_THM](MAKE_STATE c))))
     val th = EVAL pre_s
 in
  EQ_MP (GSYM th) (EVAL_ASSUME(rhs(concl th)))
 end;

(* Basic solver that uses SIMP_CONV (srw_ss()) [] 
fun simpSolv tm =
 let val () = (print "\nTrying to solve:\n"; print_term tm; print "\n... ")
     val th = time (EVAL THENC SIMP_CONV (srw_ss()) []) tm handle _ => REFL tm
     val () = if rhs(concl th) = ``T`` 
               then (print "Solved:\n"; print_thm th; print "\n")
               else print "Failure :-(\n\n"
 in
  th
 end;
*)


(* Basic solver that uses SIMP_CONV int_ss [] *)
fun simpSolv conv tm =
 let val () = (print "\nTrying to solve:\n"; print_term tm; print "\n... ")
     val th = time (EVAL THENC SIMP_CONV (srw_ss()) [] THENC conv) tm handle _ => REFL tm
     val () = if rhs(concl th) = ``T`` 
               then (print "Solved:\n"; print_thm th; print "\n")
               else print "Failure :-(\n\n"
 in
  th
 end;

(* 
Solver that calls a SAT solver.  Invoking satSolv sat tm where tm has
the form ``p ==> ~b`` invokes sat on the existential quantification
?x1 ... xn. p /\ b, where x1 ... xn are the free variables in p
and b. If sat then returns:

 |- (?x1 ... xn. p /\ b) = F

then satSolv sat ``p ==> ~b`` returns:

 |- (p ==> ~b) = T

In all other cases satSolv sat tm returns |- tm = tm.
*)

fun satSolv sat tm =
 if is_imp tm andalso
    is_neg(snd(dest_imp tm))
  then
   let val tm_frees = free_vars tm
       val (p,conc) = dest_imp tm
       val b = dest_neg conc
       val equant_tm = list_mk_exists(tm_frees,mk_conj(p,b))
       val sat_th = sat equant_tm
       val sat_th_concl = concl sat_th
   in
    if is_eq sat_th_concl                        andalso
       is_const(rhs sat_th_concl)                andalso
       (fst(dest_const(rhs sat_th_concl)) = "F") andalso
       aconv (lhs sat_th_concl) equant_tm
     then MP
           (SPECL[p,b] NOT_CONJ_IMP_F)
           (foldl 
             (fn (v,th) => SPEC v (CONV_RULE NOT_EXISTS_CONV th))
             (EQF_ELIM sat_th)
             tm_frees)
     else  REFL tm
   end
  else REFL tm;

(* 
Basic SAT solver inside HOL for testing: hol_sat tm returns the result
of applying a conversion conv to tm, or |- tm = tm if that fails. The msg argument
is printed.
*)

fun hol_sat (conv,msg) tm =
 let val () = (print "\nApplying "; print msg; print " to:\n"; 
               print_term tm; 
               print "\n... ")
     val th = time conv tm handle _ => REFL tm
     val () = if rhs(concl th) = ``T``
                then (print "Satisfiable:\n"; print_thm th; print "\n") else
              if rhs(concl th) = ``F``
               then (print "Unsatisfiable:\n"; print_thm th; print "\n")
               else print "Failure :-(\n\n"
 in
  th
 end;

(* SYMBOLIC_EVAL_PROVE solv pre c post *)

(* Rearrangement lemma used in SYMBOLIC_EVAL_PROVE 
val EVAL_SPEC_THM =
 prove
  (``!A P c Q f. 
      (!s. A s ==> P s ==> (EVAL c s (f s) /\ (Q(f s) = T))) 
      ==> 
      SPEC (\s. P s /\ A s) c Q``,
   RW_TAC std_ss [SPEC_def]
    THEN RES_TAC
    THEN IMP_RES_TAC EVAL_DETERMINISTIC
    THEN RW_TAC std_ss []);
*)

(* SYMBOLIC_EVAL_PROVE solv pre c post *)

fun SYMBOLIC_EVAL_PROVE solv asm c post_condition =
 let val var_names = program_vars c
     val vars = map (fn t => mk_var(fromHOLstring t, ``:value``)) var_names
     val svar = variant vars ``s:state``
     val svar_name = fst(dest_var svar)
     val pre = formToPred svar_name asm
     val pre_ap_svar = mk_comb(pre,svar)
     val sym_th = SYMBOLIC_EVAL solv pre c 
     val tm = concl sym_th
     val (opr,args) = strip_comb tm
     val _ = if is_const opr andalso fst(dest_const opr) = "EVAL"
              then ()
              else (print "Error in execution of SYMBOLIC_EVAL_PROVE:\n"; 
                    print_term tm)
     val post_state = last args
     val post_state_fn = mk_abs(svar,post_state)
     val post_state_fn_ap_svar = mk_comb(post_state_fn,svar)
     val post_state_eq_th = GSYM(BETA_CONV post_state_fn_ap_svar)
     val sym_th1 = CONV_RULE (RAND_CONV(REWR_CONV post_state_eq_th)) sym_th
     val post = formToPred svar_name  post_condition
     val post_ap_svar = mk_comb(post,post_state_fn_ap_svar)
     val post_th = EVAL post_ap_svar
     val post_th_rhs = rhs(concl post_th)
     val post_th1 = if (post_th_rhs = ``T``)
                     then post_th
                     else CONV_RULE
                           (RHS_CONV(REWR_CONV(EQT_INTRO(EVAL_ASSUME post_th_rhs)))) 
                           post_th
     val vc_fn = mk_abs(svar,post_th_rhs)
     val post_th_rhs_fn = mk_abs(svar,post_th_rhs)
     val post_th_rhs_fn_ap_svar = mk_comb(post_th_rhs_fn,svar)
     val post_th_rhs_eq_th = GSYM(BETA_CONV post_th_rhs_fn_ap_svar)
     val post_th2 = EVAL_DISCH post_th_rhs (EVAL_DISCH pre_ap_svar (CONJ sym_th1 post_th1))
     val post_th3 = CONV_RULE (RATOR_CONV(RAND_CONV(REWR_CONV post_th_rhs_eq_th))) post_th2
     val post_th4 = GEN svar post_th3
 in
  MP (SPECL[vc_fn,pre,c,post,post_state_fn]EVAL_SPEC_THM) post_th4
 end;

(* State simplifying conversions *)

(*

val fm = ``FEMPTY |+ ("k",Scalar k) |+ ("result",Scalar result) |+
               ("i",Scalar i) |+ ("j",Scalar j) |+ ("result",Scalar 0) |+
               ("k",Scalar 1) |+ ("result",Scalar (j - i))``;

*)

(* Test if a term is FEMPTY or of the form FEMPTY |+ (x1,y1) .... |+ (xn,yn) *)
fun is_finite_map fm =
 (is_const fm andalso fst(dest_const fm) = "FEMPTY")
 orelse (let val (opr,args) = strip_comb fm
         in
          is_const opr 
          andalso fst(dest_const opr) = "FUPDATE"
          andalso (length args = 2)
          andalso is_finite_map(el 1 args)
          andalso is_pair(el 2 args)
         end);

(* 
 ``FEMPTY |+ (x1,y1) .... |+ (xn,yn)`` 
  --> 
  [(``xn``,``yn``),...,(``x1``,``y1``)]
*)
fun dest_finite_map fm =
 if is_const fm andalso fst(dest_const fm) = "FEMPTY"
  then []
  else dest_pair(rand fm) :: dest_finite_map (rand(rator fm));

(* Remove overwritten variables *)

(* |- !f x y. f |+ (x,y) = f \\ x |+ (x,y)
val FUPDATE_PRUNE_LEMMA =
 Q.GEN `f` 
  (Q.GEN `x` 
    (Q.GEN `y`
     (GSYM
       (CONV_RULE 
         EVAL 
         (Q.SPEC `x` (Q.SPEC `f |+ (x,y)` FUPDATE_DOMSUB))))));

val FUPDATE_PRUNE =
 prove
  (``!f p. f |+ p = f \\ (FST p) |+ p``,
   RW_TAC std_ss []
    THEN Cases_on `p`
    THEN RW_TAC std_ss []
    THEN METIS_TAC [FUPDATE_PRUNE_LEMMA]);
*)

(* Remove overwritten entries in a finite map *)
fun PRUNE_FINITE_MAP_CONV fm =
 if not(is_finite_map fm) orelse 
    (is_const fm andalso fst(dest_const fm) = "FEMPTY")
  then REFL fm
  else (REWR_CONV FUPDATE_PRUNE 
         THENC RATOR_CONV(RAND_CONV(EVAL THENC PRUNE_FINITE_MAP_CONV)))
       fm;

(*
``FEMPTY |+ ... |+ (v,x1) ... |+ (v,x2)``
-->
|- (FEMPTY |+ ... |+ (v,x1) ... |+ (v,x2) = FEMPTY |+ ... |+ (v,x2) ...
*)

fun PERCOLATE_UPDATE fm =
 let val (rest1,update1) = dest_comb fm
     val (op1,fm1) = dest_comb rest1
     val _ = if is_const op1 andalso (fst(dest_const op1) = "FUPDATE")
              then ()
              else (print_term op1; print " should be FUPDATE\n"; fail())
     val (v1,x1) = dest_pair update1
     val _ = if is_const fm1 andalso (fst(dest_const fm1) = "FEMPTY")
              then (print_term v1; print " unbound\n"; fail())
              else ()
     val (rest2,update2) = dest_comb fm1
     val (op2,fm2) = dest_comb rest2
     val _ = if is_const op2 andalso (fst(dest_const op2) = "FUPDATE")
              then ()
              else (print_term op2; print " should be FUPDATE\n"; fail())
     val _ = if aconv op1 op2 
              then () 
              else  (print_term op1; print " and "; print_term op2; 
                     print " should be the same\n"; fail())
     val (v2,x2) = dest_pair update2
 in
  if aconv v1 v2
   then ISPECL[fm2,v1,x2,x1]FUPDATE_EQ
   else let val eqth = EQF_ELIM(bossLib.EVAL (mk_eq(v2,v1)))
            val commth = MP (ISPECL[fm2,v2,x2,v1,x1]FUPDATE_COMMUTES) eqth
            val fm3 = rhs(concl commth)
            val (rest3,update3) = dest_comb fm3
            val (_,fm4) = dest_comb rest3
            val recsubmapth = PERCOLATE_UPDATE fm4
            val recth = AP_THM(AP_TERM op1 recsubmapth)update3
        in
         TRANS commth recth
        end
 end;


(*
val FUPDATE_LIST_FOLD_LEMMA =
 prove
  (``!f p. f |+ p = f |++ [p]``,
   RW_TAC list_ss [FUPDATE_LIST_THM]);
*)

val FUPDATE_LIST_FOLD_CONV =
 REWR_CONV FUPDATE_LIST_FOLD_LEMMA
  THENC REWRITE_CONV [GSYM(el 2 (CONJUNCTS(SPEC_ALL  FUPDATE_LIST_THM)))];

(* Call SYMBOLIC_EVAL and then compress states in final result *)
fun PATH_EVAL solv pre c =
 let val COMPRESS_STATE_CONV = 
      ONCE_DEPTH_CONV(CHANGED_CONV PRUNE_FINITE_MAP_CONV)
 in
  CONV_RULE
   (RATOR_CONV(RAND_CONV COMPRESS_STATE_CONV)
     THENC RAND_CONV COMPRESS_STATE_CONV)
   (SYMBOLIC_EVAL solv pre c)
 end;

(* Replace occurrences of ``ScalarOf(s ' "x")`` by ``x`` *)
fun elim_state_apps s tm =
 if is_comb tm
     andalso is_const(rator tm)                                                                                                                   
     andalso fst(dest_const(rator tm)) = "ScalarOf"
     andalso is_comb (rand tm)                                                                                                                    
     andalso is_comb(rator (rand tm))
     andalso is_const(rator(rator (rand tm)))                                                                                                     
     andalso fst(dest_const(rator(rator (rand tm)))) = "FAPPLY"
     andalso rand(rator (rand tm)) = s
     andalso is_string(rand (rand tm))
  then mk_var(fromHOLstring(rand (rand tm)),``:int``) else
 if is_var tm orelse is_const tm
  then tm else
 if is_comb tm
  then mk_comb(elim_state_apps s (rator tm),elim_state_apps s (rand tm))
  else (print_term (rand tm);
        print "\nbad term (abstraction) to elim_state_apps\n"; fail()); 

(*
Replace occurrences of ``ScalarOf(s ' "x")`` by ``x``, then call a
conversion, then replace occurrences of ``x`` by ``ScalarOf(s ' "x")``
in the resulting theorem
*)

fun elim_state_apps_CONV conv tm =
 let val vars = free_vars tm
     val s = if (length vars = 1)               andalso 
                (type_of(hd vars) = ``:state``) andalso 
                is_var(hd vars)
              then hd vars
              else (print "Bad argument to elim_state_apps_CONV:\n";
                    print_term tm; print "\n"; fail())
     val elim_tm = elim_state_apps s tm
     val new_vars = free_vars elim_tm
     val elim_th = conv elim_tm (*  handle UNCHANGED => REFL elim_tm *)
 in
  INST
   (map 
     (fn v => {redex = v, residue = ``ScalarOf(^s ' ^(fromMLstring(fst(dest_var v))))``})
     (subtract new_vars [s]))
   elim_th
 end;

(* Apply elim_state_apps_CONV conv inside a forall, if necessary *)
fun elim_state_CONV conv tm =
 if is_forall tm
  then (QUANT_CONV(elim_state_apps_CONV conv) THENC REWR_CONV FORALL_SIMP) tm
  else elim_state_apps_CONV conv tm;

fun holSolv conv = elim_state_CONV(simpSolv conv);

(*
Generalise a goal by replacing occurrences of ``ScalarOf(s ' "x")`` by
``x``.  The validation instantiates occurrences of ``x`` by
``ScalarOf(s ' "x")`` in the theorem solving the generalised goal.
*)

fun elim_state_apps_TAC (asl,tm) =
 let val vars = free_vars tm
     val s = if (length vars = 1)               andalso 
                (type_of(hd vars) = ``:state``) andalso 
                is_var(hd vars)
              then hd vars
              else fail()
     val elim_tm = elim_state_apps s tm
     val new_vars = free_vars elim_tm
     val _ = if null(intersect new_vars (free_varsl asl)) then () else fail()
 in
  ([(asl, elim_tm)],
   fn thl =>
    INST
     (map 
       (fn v => {redex = v, residue = ``ScalarOf(^s ' ^(fromMLstring(fst(dest_var v))))``})
       (subtract new_vars [s]))
     (hd thl))
 end;

val elim_state_TAC = 
 EVAL_TAC 
  THEN SIMP_TAC (srw_ss()) [] 
  THEN TRY GEN_TAC 
  THEN elim_state_apps_TAC;

(*
     [t1,...,tn] |- t
 ------------------------
 |- t1 /\ ... /\ tn ==> t
*)

fun CONJ_DISCH_ALL th =
 let val (asms,conc) = dest_thm th
 in
  if null asms
   then th else
  if null(tl asms)
   then DISCH (hd asms) th 
   else EQ_MP
         (SPECL [list_mk_conj(tl asms),hd asms,conc] CONJ_DISCH_ALL_THM)
         (CONJ_DISCH_ALL (DISCH (hd asms) th))
 end;


(*
                    [a1,...,an] |- EVAL c s1 s2
 ------------------------------------------------------------------
 |- !P R. 
     (!s. (P ==> a1 /\ ... /\ an) /\ (a1 /\ ... /\ an ==> R s1 s2))
     ==>
     RSPEC P c R
*)
fun EVAL_RSPEC_INTRO th =
 let val disch_th = CONJ_DISCH_ALL th
     val disch_tm = concl disch_th
     val sl = filter (fn v => type_of v = ``:state``) (free_vars disch_tm)
     val svar = if length sl = 1
                 then hd sl
                 else (print "More than on state variable in:\n";
                       print_thm th; print "\n";fail())
     val (ante,conc) =
          if is_imp disch_tm then dest_imp(disch_tm) else (T,disch_tm)
     val A = mk_abs(svar,ante)
     val A_th = BETA_CONV(mk_comb(A,svar))
     val _ = if aconv ante (rhs(concl A_th))
              then ()
              else (print "Error in EVAL_RSPEC_INTRO (1):\n"; print_term disch_tm;
                    print "\nshould be the same as:\n";
                    print_term(rhs(concl A_th));
                    print "\n";fail())
     val (_,args) = strip_comb conc
     val c = el 1 args
     val svar' = el 2 args
     val s2 = el 3 args
     val _ = if aconv svar svar'
              then ()
              else (print "Error in EVAL_RSPEC_INTRO (2):\n"; print_term svar;
                    print "\nshould be the same as:\n";
                    print_term svar';
                    print "\n";fail())
     val f = mk_abs(svar,s2)
     val f_th = BETA_CONV(mk_comb(f,svar))
     val _ = if aconv s2 (rhs(concl f_th))
              then ()
              else (print "Error in EVAL_RSPEC_INTRO (3):\n"; print_term s2;
                    print "\nshould be the same as:\n";
                    print_term(rhs(concl f_th));
                    print "\n";fail())
     val th1 = SPECL [A,c,f] EVAL_RSPEC
(*
     val th2 = CONV_RULE
                (RATOR_CONV
                 (RAND_CONV
                  (QUANT_CONV
                   (RATOR_CONV(RAND_CONV BETA_CONV)
                    THENC RAND_CONV(RAND_CONV BETA_CONV)))))
                th1
     val th2 = BETA_RULE th1
     val q_disch_th = GEN svar disch_th)

*)
     val th2 = PURE_REWRITE_RULE[IMP_CLAUSES](BETA_RULE th1)
     val q_disch_th = PURE_REWRITE_RULE[IMP_CLAUSES](GEN svar disch_th)
     val _ = if aconv (concl q_disch_th) (rand(rator(concl th2)))
              then ()
              else (print "Error in EVAL_RSPEC_INTRO (4):\n"; print_term(concl q_disch_th);
                    print "\nshould be the same as:\n";
                    print_term(rand(rator(concl th2)));
                    print "\n";fail())
 in
  MP th2 q_disch_th
 end;

fun EVAL_IMP_INTRO th =
 CONV_RULE
  (STRIP_QUANT_CONV(RAND_CONV(REWR_CONV IMP_INTRO_THM)))
  (EVAL_RSPEC_INTRO th);

(* 
Use EVAL_IMP_INTRO to prove IMP P R c
by calling SYM_EVAL on c with precondition P
to prove [a1,...,an] |- EVAL c s1 s2
*)
fun IMP_EVAL_SOLV solv tm =
 let val (opr,args) = strip_comb tm
     val _ = if aconv opr ``IMP`` andalso is_abs(el 1 args) andalso is_abs(el 2 args)
              then () 
              else fail()
     val pre = el 1 args
     val post = el 2 args
     val svar = bvar pre
(*   val eval_th = PATH_EVAL solv pre (rhs(concl(EVAL(el 3 args)))) *)
     val eval_th = PATH_EVAL solv pre (el 3 args)
     val gen_imp_th = EVAL_IMP_INTRO eval_th
     val imp_th = BETA_RULE (SPECL [pre,post] gen_imp_th)
     val (ante,conc) = dest_imp(concl imp_th)
     val ante_th = EQT_ELIM(solv ante)
 in
  MP imp_th ante_th
 end;

(*
                    [a1,...,an] |- EVAL c s1 s2
 ------------------------------------------------------------------
 |- !P R. 
     (!s. (P ==> a1 /\ ... /\ an) /\ (a1 /\ ... /\ an ==> R s1 s2))
     ==>
     IMP P R c
*)
fun IMP_EVAL_TAC solv (asl : term list,tm) =
 let val (opr,args) = strip_comb tm
     val _ = if aconv opr ``IMP`` andalso is_abs(el 1 args) andalso is_abs(el 2 args)
              then () 
              else fail()
     val pre = el 1 args
     val post = el 2 args
     val svar = bvar pre
     val eval_th = PATH_EVAL solv pre (el 3 args)
     val gen_imp_th = EVAL_IMP_INTRO eval_th
     val imp_th = BETA_RULE (SPECL [pre,post] gen_imp_th)
     val (ante,conc) = dest_imp(concl imp_th)
 in
  ([(asl,ante)], 
   fn thl => if length thl = 1 
              then MP imp_th (hd thl) 
              else (print "Error in IMP_EVAL_TAC\n"; fail()))
 end;

(* Prove ``VARS_IN c l`` *)
fun VARS_IN_CONV t =
 let val th1 =  EVAL t
     val th2 = EQT_INTRO(prove(rhs(concl th1), REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]));
 in
  TRANS th1 th2
 end;

(* Prove |- EVAL c (FEMPTY |++ l) (FEMPTY |++ STRAIGHT_RUN c l) *)
fun STRAIGHT_EVAL_SYM c =
let val l = MAKE_STATE_LIST c
    val STRAIGHT_th = EQT_ELIM(print "\nSTRAIGHT:     "; time EVAL ``STRAIGHT ^c``)
    val VARS_IN_th =  EQT_ELIM(print "VARS_IN:      "; time VARS_IN_CONV ``VARS_IN ^c ^l``)
    val DISTINCT_th = EQT_ELIM(print "DISTINCT:     "; time EVAL ``DISTINCT_VARS ^l``)
    val STRAIGHT_RUN_th = (print "STRAIGHT_RUN: "; time EVAL ``STRAIGHT_RUN ^c ^l``)
    val STRAIGHT_RUN_EVAL_th1 = SPECL [c,l] STRAIGHT_RUN_EVAL
    val STRAIGHT_RUN_EVAL_th2 = LIST_MP [STRAIGHT_th,VARS_IN_th,DISTINCT_th] STRAIGHT_RUN_EVAL_th1 
in
 CONV_RULE (RAND_CONV(RAND_CONV(REWR_CONV STRAIGHT_RUN_th))) STRAIGHT_RUN_EVAL_th2
end;
