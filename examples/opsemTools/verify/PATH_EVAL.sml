
(* Stuff needed when running interactively
quietdec := true; (* turn off printing *)
app load ["newOpsemTheory","pairSyntax", "intLib","Omega","intSimps",
          "computeLib", "finite_mapTheory","pred_setTheory",
          "relationTheory", "stringLib"];
open newOpsemTheory bossLib pairSyntax intLib Omega
     computeLib finite_mapTheory pred_setTheory relationTheory 
     combinTheory stringLib;
quietdec := false; (* turn printing back on *)
*)

open HolKernel Parse boolLib
     newOpsemTheory bossLib pairSyntax intLib Omega intSimps
     computeLib finite_mapTheory pred_setTheory relationTheory 
     combinTheory stringLib;

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
     val _ = if not(mem name ["Equal","Less","LessEq","Greater","GreaterEq","And","Or","Not"])
              then (print name; 
                    print " is not a bexp constructor\n"; 
                    fail())
              else ()
 in
  case name of
    "Equal"     => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "Less"      => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "LessEq"    => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "Greater"   => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "GreaterEq" => union (nexp_vars(el 1 args)) (nexp_vars(el 2 args))
  | "And"       => union (bexp_vars(el 1 args)) (bexp_vars(el 2 args))
  | "Or"        => union (bexp_vars(el 1 args)) (bexp_vars(el 2 args))
  | "Not"       => bexp_vars(el 1 args)
  | _           => (print "BUG in bexp_vars! "; print name; fail())
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
                              "Seq", "Cond","AnWhile","Local","Proc"])
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
  | "AnWhile"     => union (bexp_vars(el 1 args)) 
                           (union
     (* invariant hack *)   (bexp_vars(rand(el 2 args)) handle _ => [])
                            (program_vars(el 3 args)))
  | "Local"       => subtract (program_vars(el 2 args)) [``Var ^(el 1 args)``]
  | "Proc"        => []
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

(* Replace occurrences of ``ScalarOf((FEMPTY |++ l) ' "x")`` by ``x`` *)
fun elim_state_list_apps l tm =
 if is_comb tm
     andalso is_const(rator tm)                                                                                                                   
     andalso fst(dest_const(rator tm)) = "ScalarOf"
     andalso is_comb (rand tm)                                                                                                                    
     andalso is_comb(rator (rand tm))
     andalso is_const(rator(rator (rand tm)))                                                                                                     
     andalso fst(dest_const(rator(rator (rand tm)))) = "FAPPLY"
     andalso rand(rator (rand tm)) = ``FEMPTY |++ ^l``
     andalso is_string(rand (rand tm))
  then mk_var(fromHOLstring(rand (rand tm)),``:int``) else
 if is_var tm orelse is_const tm
  then tm else
 if is_comb tm
  then mk_comb(elim_state_list_apps l (rator tm),elim_state_list_apps l (rand tm))
  else (print_term (rand tm);
        print "\nbad term (abstraction) to elim_state_list_apps\n"; fail()); 

(*
Replace occurrences of ``ScalarOf((FEMPTY |++ l) ' "x")`` by ``x``, then call a
conversion, then replace occurrences of ``x`` by ``ScalarOf((FEMPTY |++ l) ' "x")``
in the resulting theorem
*)

fun elim_state_list_apps_CONV conv tm =
 let val vars = free_vars tm
     val l = if (length vars = 1)                            andalso 
                (type_of(hd vars) = ``:(string#value)list``) andalso 
                is_var(hd vars)
              then hd vars
              else (print "Bad argument to elim_state_list_apps_CONV:\n";
                    print_term tm; print "\n"; fail())
     val elim_tm = elim_state_list_apps l tm
     val new_vars = free_vars elim_tm
     val elim_th = conv elim_tm (* handle UNCHANGED => REFL elim_tm *)
 in
  INST
   (map 
     (fn v => {redex = v, residue = ``ScalarOf((FEMPTY |++ ^l) ' ^(fromMLstring(fst(dest_var v))))``})
     (subtract new_vars [l]))
   elim_th
 end;

(* Apply elim_state_list_apps_CONV conv inside a forall, if necessary *)
fun elim_state_list_CONV conv tm =
 if is_forall tm
  then (QUANT_CONV(elim_state_list_apps_CONV conv) THENC REWR_CONV FORALL_SIMP) tm
  else elim_state_list_apps_CONV conv tm;



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
by calling PATH_EVAL on c with precondition P
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

(* Used case statement instead
fun isCommand name c =
 (is_const c andalso (fst(dest_const c) = name))
 orelse
 (is_comb c                   andalso
  is_const(fst(strip_comb c)) andalso
  (fst(dest_const(fst(strip_comb c))) = name));

val isSkip      = isCommand "Skip"
and isGenAssign = isCommand "GenAssign"
and isSeq       = isCommand "Seq"
and isCond      = isCommand "Cond";

val PRE_T =
 save_thm("PRE_T", METIS_PROVE [] ``!p b : bool. (p ==> b = T) ==> (p ==> (b = T))``);

val PRE_F =
 save_thm("PRE_F", METIS_PROVE [] ``!p b : bool. (p ==> b = F) ==> (p ==> (b = F))``);

val NOT_PRE_T =
 save_thm("NOT_PRE_T", METIS_PROVE [] ``!p b : bool. (p ==> ~b = T) ==> (p ==> (b = F))``);

val NOT_PRE_F =
 save_thm("NOT_PRE_F", METIS_PROVE [] ``!p b : bool. (p ==> ~b = F) ==> (p ==> (b = T))``);

*)

(*
Try to solve a conditional branch: BRANCH_SOLV conv pre_th l test 
evaluates b in l to get 

  |- beval test l = tm

If pre_th  is a theorem

  asl |- pre

then the conversion conv is first applied to pre ==> tm to prove

  |- (pre ==> tm) = tv

if tv = T then the following is derived

  asl |- beval test l = T

if tv = F then the following is derived

  asl |- beval test l = F

otherwise conv is applied to pre ==> ~tm to prove

 |- (pre ==> ~tm) = tv

if tv = T then the following is derived

  asl |- beval test l = F

if tv = F then the following is derived

  asl |- beval test l = T

otherwise beval test l = tm is returned
*)

fun BRANCH_SOLVE conv pre_th l test =
 let val test_th = EVAL ``beval ^test (FEMPTY |++ ^l)``
     val tm = rhs(concl test_th)
     val pre = concl pre_th
     val T_tm = mk_imp(pre,tm)
     val T_th = (conv ORELSEC REFL) T_tm
 in
  if rhs(concl T_th) = ``T``
   then CONV_RULE 
         (RHS_CONV (REWR_CONV (MP (MP (SPECL[pre,tm]PRE_T) T_th) pre_th)))
         test_th else
  if rhs(concl T_th) = ``F``
   then CONV_RULE 
         (RHS_CONV (REWR_CONV (MP (MP (SPECL[pre,tm]PRE_F) T_th) pre_th)))
         test_th else
   let val F_tm = mk_imp(pre, mk_neg tm)
       val F_th = (conv ORELSEC REFL) F_tm
   in
    if rhs(concl F_th) = ``T``
     then CONV_RULE 
           (RHS_CONV (REWR_CONV (MP (MP (SPECL[pre,tm]NOT_PRE_T) F_th) pre_th)))
           test_th else
    if rhs(concl F_th) = ``F``
     then CONV_RULE 
           (RHS_CONV (REWR_CONV (MP (MP (SPECL[pre,tm]NOT_PRE_F) F_th) pre_th)))
           test_th else
     test_th
   end
 end;

(********************************************************************
The "state" of symbolic simulation is a theorem

 |- STRAIGHT_RUN_CONT c con l = tm

and a single step is performed by proving |- tm = tm' and hence

 |- STRAIGHT_RUN_CONT c con l = tm'
********************************************************************)

(* Single step of a symbolic simulation *)
fun SYM_STEP_CONV conv pre_th tm =
 if is_comb tm andalso is_abs(rator tm)
  then BETA_CONV tm
  else
  let val (opr,args) = strip_comb tm
      val _ = if is_const opr 
                  andalso (fst(dest_const opr) = "STRAIGHT_RUN_CONT")
                  andalso (length args = 3 )
               then ()
               else (print "SYM_STEP_CONV Error 1\n";
                     print_term tm; print "\n";
                     fail())
      val c    = el 1 args
      val cont = el 2 args
      val l    = el 3 args
      val (cmd,params) = strip_comb c
  in
   case fst(dest_const cmd) of
     "Skip"        
       =>  REWR_CONV (el 1 (CONJUNCTS STRAIGHT_RUN_CONT)) tm
  |  "GenAssign"   
       =>  (REWR_CONV (el 2 (CONJUNCTS STRAIGHT_RUN_CONT)) 
             THENC RAND_CONV EVAL) tm
   | "Assign"      
       =>  (REWR_CONV (el 3 (CONJUNCTS STRAIGHT_RUN_CONT))
             THENC RAND_CONV EVAL) tm
   | "ArrayAssign" 
       =>  (REWR_CONV (el 4 (CONJUNCTS STRAIGHT_RUN_CONT))
            THENC RAND_CONV EVAL ) tm
   | "Seq"         
       =>  REWR_CONV (el 5 (CONJUNCTS STRAIGHT_RUN_CONT)) tm
   | "Cond"         
       =>  let val testtm = el 1 params
               val thentm = el 2 params
               val elsetm = el 3 params
               val testth = BRANCH_SOLVE conv pre_th l testtm
               val branchtm = rhs(concl testth)
           in
            if not((branchtm = ``T``) orelse (branchtm = ``F``))
(*
            then (REWR_CONV (el 6 (CONJUNCTS STRAIGHT_RUN_CONT)) 
                   THENC RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV testth)))))
                 tm	   
*)
             then REWRITE_CONV [testth,el 6 (CONJUNCTS STRAIGHT_RUN_CONT)] tm
             else
             let val STRAIGHT_th1 = EQT_ELIM(EVAL ``STRAIGHT ^thentm``)
                 val STRAIGHT_th2 = EQT_ELIM(EVAL ``STRAIGHT ^elsetm``)
                 val VARS_IN_th1 =  EQT_ELIM(VARS_IN_CONV ``VARS_IN ^thentm ^l``)
                 val VARS_IN_th2 =  EQT_ELIM(VARS_IN_CONV ``VARS_IN ^elsetm ^l``)
             in
              if branchtm = ``T``
               then LIST_MP 
                     [testth,STRAIGHT_th1,STRAIGHT_th2,VARS_IN_th1,VARS_IN_th2]
                     (ISPECL [cont,l,testtm,thentm,elsetm] (el 7 (CONJUNCTS STRAIGHT_RUN_CONT)))
               else LIST_MP 
                     [testth,STRAIGHT_th1,STRAIGHT_th2,VARS_IN_th1,VARS_IN_th2]
                     (ISPECL [cont,l,testtm,thentm,elsetm] (el 8 (CONJUNCTS STRAIGHT_RUN_CONT)))
             end
           end
   | _ => fail()
   end;

(* Iterate until continuation ``I`` is reached *)
fun SYM_RUN_CONV conv pre_th tm =
 if is_comb tm 
     andalso is_const(rator tm) 
     andalso (fst(dest_const(rator tm)) = "I")
  then REWR_CONV I_THM tm
  else (SYM_STEP_CONV conv pre_th THENC SYM_RUN_CONV conv pre_th) tm;

(* 
Some test data:
use "PATH_EVAL_Examples.ml";
val c = TritypeProg;
val c = AbsMinusProg;
val l = MAKE_STATE_LIST c;
val STRAIGHT_th = EQT_ELIM(print "\nSTRAIGHT:     "; time EVAL ``STRAIGHT ^c``);
val VARS_IN_th =  EQT_ELIM(print "VARS_IN:      "; time VARS_IN_CONV ``VARS_IN ^c ^l``);
val DISTINCT_th = EQT_ELIM(print "DISTINCT:     "; time EVAL ``DISTINCT_VARS ^l``);
val cont = ``I : (string # value) list -> (string # value) list``;
val tm = ``STRAIGHT_RUN_CONT ^c ^cont ^l``;
val conv = OMEGA_CONV;
val conv = SIMP_CONV arith_ss [];
val pre_th = ASSUME ``i:int < j``;
val pre_th = TRUTH;

val th0  = REFL tm;
val th1  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th0;
val th2  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th1;
val th3  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th2;
val th4  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th3;
val th5  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th4;
val th6  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th5;
val th7  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th6;
val th8  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th7;  (* BETA *)
val th9  = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th8;
val th10 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th9;
val th11 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th10;
val th12 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th11; (* BETA *)
val th13 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th12;
val th14 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th13; (* BETA *)
val th15 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th14; 
val th16 = CONV_RULE (RHS_CONV (SYM_STEP_CONV  conv pre_th)) th15; 

val MultBody =
    ``(Seq
       (GenAssign "result" (INL(V"result" + V"n")))
       (GenAssign "count"  (INL(V"count" + C 1))))``;


val MultBody =
    ``(Seq
       (Assign "result" (V"result" + V"n"))
       (Assign "count"  (V"count" + C 1)))``;

val Mult =
    ``AnWhile (V"count" < V"m") R
       (Seq
         (Assign "result" (V"result" + V"n"))
         (Assign "count"  (V"count" + C 1)))``;
  

BETA_RULE
 (ISPECL 
   [MultBody,
    ``V"count" < V"m"``,
    ``\s. ScalarOf(s ' "n") * ScalarOf(s ' "count") = ScalarOf(s ' "result")``,
    ``\s. (ScalarOf(s ' "result") = 0) /\ (ScalarOf(s ' "count") = 0)``] 
   (el 6 (CONJUNCTS SVC_def)));

*)


(* Tool to prove SPEC P c Q by symbolic execution *)

(* Test data

val MultProg =                                                 (* [("n",n); ("m",m); ("count",count); ("Result",Result); ("result",result)] /\ (m > 0) /\ (n > 0) *)
 ``"result" ::= C 0;;                                          (* [("n",n); ("m",m); ("count",count); ("Result",Result); ("result",0)]      /\ (m > 0) /\ (n > 0) *)
   "count" ::= C 0;;                                           (* [("n",n); ("m",m); ("count",0);     ("Result",Result); ("result",0)]      /\ (m > 0) /\ (n > 0) *)
   AnWhile (V"count" < V"m") 
    (beval ((C n * V"count" = V"result") /\ V"count" <= C m))
    ("result" ::= (V"result" + V"n");;
     "count" ::= (V"count" + C 1));;                           (* [("n",n'); ("m",m'); ("count",count'); ("Result",Result'); ("result",result')] /\ (n*count'=result') /\ count' <= m /\ ~(count'<m) /\ (m > 0) /\ (n > 0) *)
   "count" ::= C 0;;                                           (* [("n",n'); ("m",m'); ("count",0);      ("Result",Result'); ("result",result')] /\ (n*count'=result') /\ count' <= m /\ ~(count'<m) /\ (m > 0) /\ (n > 0) *) 
   "Result" ::= V"result"``;                                   (* [("n",n'); ("m",m'); ("count",0);      ("Result",result'); ("result",result')] /\ (n*count'=result') /\ count' <= m /\ ~(count'<m) /\ (m > 0) /\ (n > 0) *) 

val MultGoal =
 ``SPEC
    (beval ((V"m" = C m) /\ (V"n" = C n) /\ C m > C 0 /\ C n > C 0))
    ^MultProg
    (beval (V"Result" = C m * C n))``;

val pre_vars  = bexp_vars ``((V"m" = C m) /\ (V"n" = C n) /\ C m > C 0 /\ C n > C 0)``;
val prog_vars = program_vars MultProg;
val post_vars = bexp_vars ``V"Result" = C m * C n``;
val vars      = union pre_vars (union prog_vars post_vars);

val tm =
 ``XP ["m";"n";"count";"result";"Result"]
    (\s. ?Result result count n' m'.
          beval ((C n * V"count" = V"result") /\ V"count" <= C m) (FEMPTY |++ [("m",m');("n",n');("count",count);("result",result);("Result",Result)])
          /\
          (s = FEMPTY |++ I [("m",m');("n",n');("count",count);("result",result);("Result",Result)]))
    ^MultProg``;

val l = MAKE_STATE_LIST_FROM_VARS vars;
val xl = rhs(concl(EVAL ``MAP FST ^l``));

val simp_th = EVAL ``SIMPLE ^MultProg``;

val th1 = SPECL [MultProg,l] XP_FVC_SPEC_COR;

val th2 = EVAL_RULE th1;

val spec_tm = MultGoal;

val c = MultProg;
val P = ``beval ((V"m" = C m) /\ (V"n" = C n) /\ C m > C 0 /\ C n > C 0)``;
val l = MAKE_STATE_LIST_FROM_VARS (union (bexp_vars(rand P)) (program_vars c));

val c3 =
 ``AnWhile (V "count" < V "m")
    (beval ((V "n" * V "count" = V "result") /\ V "count" <= V "n"))
    ("result" ::= V "result" + V "n" ;; "count" ::= V "count" + C 1)`` :

EVAL ``XP P (GenAssign v1 e1;; AnWhile b R c;; GenAssign v2 e2)``;
SIMP_RULE std_ss [GSPEC SPEC_def] (EVAL ``FVC P (GenAssign v1 e1;; AnWhile b R c;; GenAssign v2 e2)``);

*)

(*
MAP_FST_CONV ``(?l. (MAP FST l = ["x1";...;"xn"]) /\ P l)``
-->
|- (?l. (MAP FST l = ["x1";...;"xn"]) /\ P l)) = ?xn ... x1. P([("x1",x1);...;("xn",xn)])

val tm = ``(?(l:(string#value)list). (MAP FST l = ["x1";"x2";"x3"]) /\ P l)``;
val tm = ``?l:(string#value)list. (MAP FST l = ["x1";"x2";"x3";"x4";"x5";"x6";"x7";"x8";"x9";"x10";"x11";"x12"]) /\ P l``;
*)


(* Version below intended to be fast, but actually slower than the
   naive version using SIMP_CONV!

fun MAP_FST_CONV tm =
 let val (l,bdy) = dest_exists tm
     val (tm1,tm2) = dest_conj bdy
     val (map_tm,xl) = dest_eq tm1
 in
  if aconv xl ``[]:string list``
   then CONV_RULE EVAL (SPEC (mk_abs(l,tm2)) MAP_FST_EXPAND_NIL)
   else 
    let val v = mk_var(fromHOLstring(hd(fst(listSyntax.dest_list xl))),``:value``)
    in
     CONV_RULE 
      (EVAL THENC RHS_CONV(QUANT_CONV(RAND_CONV(GEN_ALPHA_CONV v)) THENC MAP_FST_CONV))
      (SPECL [mk_abs(l,tm2), ``HD ^xl``, ``TL ^xl``] MAP_FST_EXPAND)
    end
 end;
*)

(* Rename a multiple quantification *)
fun GEN_ALPHAL_CONV [] = ALL_CONV
 |  GEN_ALPHAL_CONV (v::vl) = GEN_ALPHA_CONV v THENC QUANT_CONV(GEN_ALPHAL_CONV vl); 

fun MAP_FST_CONV tm =
 let val xl = snd(dest_eq(fst(dest_conj(snd(dest_exists tm)))))
     fun string2var x = mk_var(fromHOLstring x, ``:value``)
     val vars = map string2var (fst(listSyntax.dest_list xl))
     val ex_th = SIMP_CONV pure_ss [MAP_FST_EXPAND,MAP_FST_EXPAND_NIL] tm
 in
  CONV_RULE (RHS_CONV(GEN_ALPHAL_CONV(rev vars))) ex_th
 end;

(*
MAP_FST_FORALL_CONV ``(!l. (MAP FST l = ["x1";...;"xn"]) ==> P l)``
-->
|- (!l. (MAP FST l = ["x1";...;"xn"]) ==> P l)) = !xn ... x1. P([("x1",x1);...;("xn",xn)])

val tm = ``!(l:(string#value)list). (MAP FST l = ["x1";"x2";"x3"]) ==> P l``;
val tm = ``!l:(string#value)list. (MAP FST l = ["x1";"x2";"x3";"x4";"x5";"x6";"x7";"x8";"x9";"x10";"x11";"x12"]) ==> P l``;
*)

fun MAP_FST_FORALL_CONV tm =
 let val xl = snd(dest_eq(fst(dest_imp(snd(dest_forall tm)))))
     fun string2var x = mk_var(fromHOLstring x, ``:value``)
     val vars = map string2var (fst(listSyntax.dest_list xl))
     val ex_th = SIMP_CONV pure_ss [MAP_FST_FORALL_EXPAND,MAP_FST_FORALL_EXPAND_NIL] tm
 in
  CONV_RULE (RHS_CONV(GEN_ALPHAL_CONV(rev vars))) ex_th
 end;


(*
XP_ARG_CONV ``\s. ?l. (MAP FST l = ["x1";...;"xn"]) /\ P(FEMPTY |++ l) /\ (s = FEMPTY |++ (f l))``
-->
|- (\s. ?l. (MAP FST l = ["x1";...;"xn"]) /\ P(FEMPTY |++ l) /\ (s = FEMPTY |++ (f l))) = 
   (\s. ?xn ... x1. P([("x1",x1);...;("xn",xn)]) /\ (s = FEMPTY (f[("x1",x1);...;("xn",xn)]))
*)

val XP_ARG_CONV = ABS_CONV MAP_FST_CONV;

(* 
 XP_CONV 
  ``XP xl (\s. ?xn...x1. 
                 P[("x1",x1);...;("xn",xn)] 
                 /\ 
                 (s = FEMPTY |++ (f[("x1",x1);...;("xn",xn)]))) c``
 -->
 |- XP xl (\s. ?xn...x1. 
                 P[("x1",x1);...;("xn",xn)])
                 /\ 
                 (s = FEMPTY |++ (f[("x1",x1);...;("xn",xn)]))) c =
          (\s. ?xn...x1. 
                 P[("x1",x1);...;("xn",xn)] 
                 /\ 
                 (s = FEMPTY |++ (f'[("x1",x1);...;("xn",xn)]))

|- (?l. (MAP FST l = ["x1";...;"xn"]) /\ P l)) = ?xn ... x1. P([("x1",x1);...;("xn",xn)])
*)


(* Apply MAP_FST_CONV to the existential quantifications 
   in the LHS and RHS of a theorem of the form:

 |- XP xl (\s. ?l. ...) c = \s. ?l. ...
*)

val EXPAND_EXISTS =
 CONV_RULE                                                                                                                                                                                                                          
  (LHS_CONV(RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV))) THENC                                                                                                                                                                      
   RHS_CONV(ABS_CONV MAP_FST_CONV));

(*
val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              ("y" ::= V"x" + C y)``;

val tm = ``XP ["x";"y";"z"] 
              (\s. ?z y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y);("z",z)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y);("z",z)])))
              ("y" ::= V"x" + C y)``;


val tm = ``XP ["x";"y";"z"] 
              (\s. ?z y x'. R[("x", x');("y", y);("z",z)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y);("z",z)])))
              ("y" ::= V"x" + C y)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. P[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              ("y" ::= V"x" + C y)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              (AnWhile b R c)``;

val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x'.
             (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
             /\
             (s =
              FEMPTY |++ (ASSIGN_FUN "x" (C 0) o I) [("x",x'); ("y",y)]))
        ("y" ::= V "x" + C y)``

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              ("x" ::= C 0;; "y" ::= V"x" + C y)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ ([("x", x');("y", y)])))
              ("x" ::= C 0;; "y" ::= V"x" + C y;; "x" ::= V"y" + C 1;; "y" ::= (V"x" + V"y") + C 2)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              ("x" ::= C 0;; AnWhile b R c)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ ( [("x", x');("y", y)])))
              (AnWhile b R c;; "x" ::= V"y" + C 1)``;


val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              (AnWhile b R c)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ ( [("x", x');("y", y)])))
              ("x" ::= C 0;; "y" ::= V"x" + C y;; "x" ::= V"y" + C 1;; AnWhile b R c;; "y" ::= (V"x" + V"y") + C 2;; "y" ::= V"x" + C y;; "x" ::= V"y" + C 1)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ (I [("x", x');("y", y)])))
              (AnWhile b R c;; "y" ::= (V"x" + V"y") + C 2)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\
                          (s = FEMPTY |++ ( [("x", x');("y", y)])))
              (GenAssign v1 e1 ;; AnWhile b R c ;; GenAssign v2 e2)``;

*)



(*

Goal:

SPEC
 (\s. beval ((C n * V "count" = V "result") /\ V "count" <= C m) s /\ beval (V "count" < C m) s /\ beval (V "n" = C n) s)
 (GenAssign "result" (INL (V "result" + V "n")) ;; GenAssign "count" (INL (V "count" + C 1)))
 (beval ((C n * V "count" = V "result") /\ V "count" <= C m)) 

val xl = ``["m";"n";"count";"result";"Result"]``;

val pre_tm = ``(\s. beval ((C n * V "count" = V "result") /\ V "count" <= C m) s /\ beval (V "count" < C m) s /\ beval (V "n" = C n) s) o ($|++ FEMPTY)``;

val pre_th =
 XP_ARG_CONV
  ``\s. ?l. (MAP FST l = ^xl) /\ ^pre_tm  l /\ (s = FEMPTY |++ I l)``;

val fvc_tm =
``FVC ^xl
   ^(rhs(concl pre_th))
   (GenAssign "result" (INL (V "result" + V "n")) ;; GenAssign "count" (INL (V "count" + C 1)))``;

val fvc_th = SIMP_CONV std_ss [FVC_def,Assign_def] fvc_tm;

val lp_tm =
``XP ^xl
   ^(rhs(concl pre_th))
   (GenAssign "result" (INL (V "result" + V "n")) ;; GenAssign "count" (INL (V "count" + C 1)))``;

val lp_th = XP_CONV lp_tm;

val lp_fvc_th1 =
 SPECL 
  [``["m";"n";"count";"result";"Result"]``, 
   ``I : (string # value) list -> (string # value) list``,
   pre_tm,
   ``GenAssign "result" (INL (V "result" + V "n")) ;; GenAssign "count" (INL (V "count" + C 1))``]
  XP_FVC_SPEC_COR;

val lp_fvc_th2 = CONV_RULE (DEPTH_CONV MAP_FST_CONV) lp_fvc_th1;

val lp_fvc_th3 = PURE_REWRITE_RULE [fvc_th,lp_th] lp_fvc_th2;

val lp_fvc_th4 = SIMP_RULE std_ss [SIMPLE_def,VARS_def,UNION_SUBSET,listTheory.LIST_TO_SET_THM,SUBSET_DEF,IN_UNION,IN_SING,IN_INSERT] lp_fvc_th3;

val lp_fvc_th5 = CONV_RULE (RATOR_CONV(RAND_CONV(EQT_INTRO o METIS_PROVE[])) THENC SIMP_CONV std_ss []) lp_fvc_th4;

val goal =
 prove
  (``^(rand(concl lp_fvc_th5)) s ==>  beval ((C n * V "count" = V "result") /\ V "count" <= C m) s``,
   CONV_TAC EVAL
    THEN RW_TAC std_ss []
    THEN CONV_TAC EVAL
    THEN RW_TAC arith_ss [integerTheory.INT_LDISTRIB,integerTheory.INT_MUL_RID]
    THEN Cooper.COOPER_TAC);

       


computeLib.del_consts[``SPEC``];

val MultProg =
 ``"result" ::= C 0;;
   "count" ::= C 0;; 
   AnWhile (V"count" < V"m") 
    (beval ((C n * V"count" = V"result") /\ V"count" <= C m))
    ("result" ::= (V"result" + V"n");;
     "count" ::= (V"count" + C 1));;
   "count" ::= C 0;;                
   "Result" ::= V"result"``;        

val MultProgPre =
 ``(\s. ?Result result count n' m'.
         beval ((C n * V"count" = V"result") /\ C 0 <= C m /\ V"count" <= C m) (FEMPTY |++ [("m",m');("n",n');("count",count);("result",result);("Result",Result)])
         /\
         (s = FEMPTY |++ [("m",m');("n",n');("count",count);("result",result);("Result",Result)]))``;


val MultProgPre =
 ``(\s. ?Result result count n' m'.
         (beval ((C n * V"count" = V"result") /\ C 0 <= C m /\ V"count" <= C m) o ($|++ FEMPTY)) [("m",m');("n",n');("count",count);("result",result);("Result",Result)]
         /\
         (s = FEMPTY |++ [("m",m');("n",n');("count",count);("result",result);("Result",Result)]))``;

val xl = ``["m";"n";"count";"result";"Result"]``;

val ftm = ``FVC ^xl ^MultProgPre ^MultProg``;
val tm  = ``XP  ^xl ^MultProgPre ^MultProg``;

val MultProgFVC =
 CONV_RULE 
  (DEPTH_CONV XP_CONV THENC SIMP_CONV std_ss [] THENC RHS_CONV EVAL) 
  (PURE_REWRITE_CONV [FVC_def,Assign_def] ftm);

val MultWhileFVC_THM =
 prove
  (rhs(concl MultProgFVC),
   RW_TAC std_ss []
    THEN CONV_TAC EVAL
    THEN RW_TAC arith_ss []

val tm = 
 ``XP ["m"; "n"; "count"; "result"; "Result"]
             (\s.
                ?Result result count n' m'.
                  beval ((C n * V "count" = V "result") /\ V "count" <= C m)
                    (FEMPTY |++
                     [("m",m'); ("n",n'); ("count",count);
                      ("result",result); ("Result",Result)]) /\
                  (s =
                   FEMPTY |++
                   (GEN_ASSIGN_FUN "result" (INL (C 0)) o I)
                     [("m",m'); ("n",n'); ("count",count);
                      ("result",result); ("Result",Result)]))
             (GenAssign "count" (INL (C 0)))``;


val tm =
    ``XP ["m"; "n"; "count"; "result"; "Result"]
        (XP ["m"; "n"; "count"; "result"; "Result"]
           (\s.
              ?Result result count n' m'.
                beval ((C n * V "count" = V "result") /\ V "count" <= C m)
                  (FEMPTY |++
                   I
                     [("m",m'); ("n",n'); ("count",count);
                      ("result",result); ("Result",Result)]) /\
                (s =
                 FEMPTY |++
                 I
                   [("m",m'); ("n",n'); ("count",count); ("result",result);
                    ("Result",Result)])) ("result" ::= C 0))
        ("count" ::= C 0)`` ;

*)


(*

val tm = ``XP ["x";"y"] 
              (\s. ?y x. (beval (V"x" < V"y") o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x. (beval (V"x" > V"y") o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ( [("x", x);("y", y)])))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x. (beval (V"x" = V"x") o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x. ((\s. T) o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x. ((\s. T) o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              ("x" ::= C x)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x. ((\s. T) o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
       (\s.
          ?y x.
            ((\s. T) o $|++ FEMPTY) [("x",x); ("y",y)] /\
            (s =
             FEMPTY |++
             (\l.
                ZIP_LIST (beval (V "x" <= V "y") (FEMPTY |++ I l))
                  ((ASSIGN_FUN "x" (C 0) o I) l)
                  ((ASSIGN_FUN "y" (C 0) o I) l)) [("x",x); ("y",y)]))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x. ((\s. T) o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              (("x" ::= C x);; Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;


val tm = ``XP ["x";"y"] 
              (\s. ?y x. ((\s. (x0 = 0)) o ($|++ FEMPTY)) [("x", x);("y", y)]
                         /\ 
                         (s = FEMPTY |++ ([("x", x);("y", y)])))
              ("x" ::= C x0)``;

val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. x0 = 0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. T) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0))``;

val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. x0 = 0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              (Cond (V"x" <= V"y") ("x" ::= C 0) ("y" ::= C 0);; "x" ::= C 1)``;


val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. x0 = 0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              ("x" ::= C x0;; "y" ::= C x0;; Cond (V"x" <= V"y") ("x" ::= C 1) ("y" ::= C 2);; "x" ::= C 3)``;


val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. x0 = 0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              (Cond (V"x" <= V"y") ("x" ::= C 1) (AnWhile b R ("x" ::= V"y"));; "x" ::= C 3)``;


val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. x0 = 0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              ("x" ::= C x0;; "y" ::= C x0;; (Cond (V"x" <= V"y") ("x" ::= C 1) (AnWhile b R Skip));; "x" ::= C 3)``;

val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x : value.
                   ((\s. T) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              ("x" ::= C x0;; "y" ::= C x0;; (Cond (V"x" < V"y") ("x" ::= C 1) (AnWhile b R Skip));; "x" ::= C 3)``;


val tm = ``XP ["x";"y"] 
              (\s.
                 ?y x.
                   ((\s. T) o $|++ FEMPTY) [("x",x); ("y",y)] /\
                   (s = FEMPTY |++ [("x",Scalar x0); ("y",y)]))
              ((Cond (V"x" < V"y") ("x" ::= C 1) (AnWhile b R Skip));; "x" ::= C 3)``;

val EXISTS_SIMPLE =
 store_thm
  ("EXISTS_SIMPLE",
   ``?f. !n:num. SIMPLE(f n)``,
   Q.EXISTS_TAC `\n. Skip`
    THEN CONV_TAC EVAL
    THEN METIS_TAC[]);

val MK_SIMPLE_def =
 new_specification("MK_SIMPLE_def", ["MK_SIMPLE"], EXISTS_SIMPLE);

val MK_SIMPLE =
 store_thm
  ("MK_SIMPLE",
   ``SIMPLE(MK_SIMPLE n) = T``,
   METIS_TAC[MK_SIMPLE_def]);

val _ = computeLib.add_funs[MK_SIMPLE];

val c_simple_def = Define `c_simple = MK_SIMPLE 0`;

val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x:value.
             (P o $|++ FEMPTY) [("x",x); ("y",y)] /\
             (s = FEMPTY |++ [("x",x); ("y",y)]))
        (AnWhile b R c_simple)``;


val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x:value.
             ((\s. T) o $|++ FEMPTY) [("x",x); ("y",y)] /\
             (s = FEMPTY |++ [("x",Scalar x0); ("y",Scalar x0)]))
        (if V "x" <= V "y" then "x" ::= C 1 else AnWhile b R c_simple)``;

val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x:value.
             ((\s. x0 = 0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
             (s = FEMPTY |++ [("x",Scalar x0); ("y",Scalar x0)]))
        ((if V "x" <= V "y" then "x" ::= C 1 else AnWhile b R c_simple) ;;
         "x" ::= C 3)``;

val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x:value.
             ((\s. x0 <= y0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
             (s = FEMPTY |++ [("x",Scalar x0); ("y",Scalar y0)]))
        ((if V "x" <= V "y" then "x" ::= C 1 else AnWhile b R c_simple) ;;
         "x" ::= C 3)``;


val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x:value.
             ((\s. x0 > y0) o $|++ FEMPTY) [("x",x); ("y",y)] /\
             (s = FEMPTY |++ [("x",Scalar x0); ("y",Scalar y0)]))
        ((if V "x" <= V "y" then "x" ::= C 1 else AnWhile b R c_simple) ;;
         "x" ::= C 3)``;

val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y x:value.
             ((\s. T) o $|++ FEMPTY) [("x",x); ("y",y)] /\
             (s = FEMPTY |++ [("x",Scalar x0); ("y",Scalar y0)]))
        ((if V "x" <= V "y" then "x" ::= C 1 else AnWhile b R c_simple) ;;
         "x" ::= C 3)``;


*)

(*
makefun ``[("x1",x1);...;("xn",xn)]`` tm 
-->
``\l.(\x1 ... xn. tm) (LOOKUP "x1" l) ... (LOOKUP "xn" l)``

If variables in e1,...,en are included in ``x1``,...,``xn``, 
then should have:

 |- (makefun [("x1",x1);...;("xn",xn)] [("x1",e1);...;("xn",en)])
     [("x1",x1);...;("xn",xn)] 
     = [("x1",e1);...;("xn",en)]
*)

fun makefun l tm =
 let val l_list = map dest_pair (fst(listSyntax.dest_list l))
     val l_vars = map snd l_list
     val lvar = ``l:(string#value)list``
 in
  mk_abs(lvar,list_mk_comb(list_mk_abs(l_vars,tm), map (fn x => ``LOOKUP ^x ^lvar``)(map fst l_list)))
 end;


(*
Simplify if 

 fconv ``f [("x1",x1);...;("xn",xn)]`` = |- f [("x1",x1);...;("xn",xn)] = [("x1",x1');...;("xn",xn')] 

then 

 XP_RESULT_CONV
  ``\s. ?xn...x1. P(...) /\ (s = FEMPTY (f [("x1",x1);...;("xn",xn)]))``
 
  = |-  (\s. ?xn...x1. P(...) /\ (s = FEMPTY (f [("x1",x1);...;("xn",xn)]))) =
         \s. ?xn...x1. P(...) /\ (s = [("x1",x1');...;("xn",xn')]))
*)


(* tm --> |- tm = I tm 
fun I_INTRO_CONV tm = SYM(ISPEC tm I_THM);
*)

fun XP_RESULT_CONV fconv =
 ABS_CONV(STRIP_QUANT_CONV(RAND_CONV(RHS_CONV(RAND_CONV(fconv (* THENC I_INTRO_CONV *) )))));

(* Hit and equation for XP with XP_RESULT_CONV EVAL on LHS and RHS *)
val XP_EVAL_RULE =
 CONV_RULE 
  (LHS_CONV(RATOR_CONV(RAND_CONV(XP_RESULT_CONV EVAL)))
    THENC RHS_CONV(XP_RESULT_CONV EVAL));

val conv = EVAL 
            THENC SIMP_CONV arith_ss [] 
            THENC (elim_state_CONV(Cooper.COOPER_CONV ORELSEC ALL_CONV)
                   ORELSEC ALL_CONV);

fun PROVE_T_CONV tm =
 prove
  (``^tm = T``,
   RW_TAC arith_ss []
    THEN Cooper.COOPER_TAC);

fun PROVE_F_CONV tm =
 prove
  (``^tm = F``,
   RW_TAC arith_ss []
    THEN Cooper.COOPER_TAC);

val conv = EVAL 
            THENC SIMP_CONV arith_ss [] 
            THENC (PROVE_T_CONV ORELSEC PROVE_F_CONV ORELSEC ALL_CONV);

datatype cond_eval = TestTrue of thm | TestFalse of thm | Unresolved;

(* 

CondTest conv p b evaluates ``p ==> b`` and if this is unresolved then ``p ==> ~b``:

 1. if conv ``p ==> b`` = |- (p ==> b) = T then TestTrue(|- p ==> b) returned

 2. if conv ``p ==> b`` = |- (p ==> b) = F then TestFalse(|- p ==> ~b) returned

 3. if conv ``p ==> b`` = |- (p ==> b) = tm (tm not T or F) then

    3.1 if conv ``p ==> ~b`` = |- (p ==> ~b) = T then TestFalse(|- p ==> ~b) returned
    3.2 if conv ``p ==> ~b`` = |- (p ==> ~b) = F then TestTrue(|- p ==> ~b) returned

 4. if neither conv ``p ==> b`` nor conv ``p ==> ~b`` are resolved, Unresolved is returned

*)

(*
fun CondTest conv xl f p b =
 let val p_imp_b = ``!l. (MAP FST l = ^xl) ==> ^p l ==> beval ^b (FEMPTY |++ ^f l)``
     val th1 = (MAP_FST_FORALL_CONV THENC conv) p_imp_b
     val b_res = rhs(concl th1)
 in
  if b_res = T
   then TestTrue(EQT_ELIM th1) else
  if b_res = F
   then TestFalse(MATCH_MP TEST_F th1)
   else
    let val p_imp_not_b = ``!l. (MAP FST l = ^xl) ==> ^p l ==> ~(beval ^b (FEMPTY |++ ^f l))``
        val th2 = (MAP_FST_FORALL_CONV THENC conv) p_imp_not_b
        val not_b_res = rhs(concl th2)
    in
     if not_b_res = T
      then TestFalse(EQT_ELIM th2) else
     if not_b_res = F
      then TestTrue(MATCH_MP NOT_TEST_F th2)
      else Unresolved
    end
 end;
*)

fun CondTest conv xl f p b =
 let val p_imp_b = ``!l. (MAP FST l = ^xl) ==> ^p l ==> beval ^b (FEMPTY |++ ^f l)``
     val th1 = (MAP_FST_FORALL_CONV THENC conv) p_imp_b
     val b_res = rhs(concl th1)
 in
  if b_res = T
   then TestTrue(EQT_ELIM th1) 
   else
    let val p_imp_not_b = ``!l. (MAP FST l = ^xl) ==> ^p l ==> ~(beval ^b (FEMPTY |++ ^f l))``
        val th2 = (MAP_FST_FORALL_CONV THENC conv) p_imp_not_b
        val not_b_res = rhs(concl th2)
    in
     if not_b_res = T
      then TestFalse(EQT_ELIM th2)
      else Unresolved
    end
 end;

val trace_ref = ref(``T``,``F``);

fun TRACE (conv:term->thm) tm =
 let val th = conv tm 
 in
  if aconv tm (lhs(concl th))
   then th
   else (print "Argument:\n"; print_term tm; 
         print "\nnot equal to lhs of theorem generated by XP_CONV\n";
         print_term(lhs(concl th));print "\n\n";
         trace_ref := (tm, lhs(concl th));
         th)
 end;



(* 
 XP_CONV 
  ``XP xl (\s. ?xn...x1. 
                 P[("x1",x1);...;("xn",xn)] 
                 /\ 
                 (s = FEMPTY |++ [("x1",e1);...;("xn",en)])) c``
 -->
 |- XP xl (\s. ?xn...x1. 
                 P[("x1",x1);...;("xn",xn)])
                 /\ 
                 (s = FEMPTY |++ [("x1",e1);...;("xn",en)])) c =
           \s. ?xn...x1. 
                 P[("x1",x1);...;("xn",xn)] 
                 /\ 
                 (s = FEMPTY |++ [("x1",e1');...;("xn",en')])

|- (?l. (MAP FST l = ["x1";...;"xn"]) /\ P l)) = ?xn ... x1. P([("x1",x1);...;("xn",xn)])
*)


(*

val tm =
 ``XP ["x"; "y"]
        (\s.
           ?y x'.
             (beval (C x > C 0) o $|++ FEMPTY) [("x",x'); ("y",y)] /\
             (s = FEMPTY |++ [("x",x'); ("y",y)])) ("y" ::= V "x" + C y)``;

val tm =
    ``XP ["x"; "y"]
        (\s.
           ?y' x'.
             (beval (C x > C 0) o $|++ FEMPTY) [("x",x'); ("y",y')] /\
             (s = FEMPTY |++ [("x",x'); ("y",Scalar (ScalarOf x' + y))]))
        ("x" ::= V "y" + C x)``;

val tm =
 ``XP ["x"; "y"]
        (\s.
           ?y x'.
             (beval (C x > C 0) o $|++ FEMPTY) [("x",x'); ("y",y)] /\
             (s = FEMPTY |++ [("x",x'); ("y",y)])) 
        (("x" ::= V "y" + C x) ;; ("y" ::= V "x" + C y))``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ [("x", x');("y", y)]))
              ("x" ::= C 0;; "y" ::= V"x" + C y;; "x" ::= V"y" + C 1;; "y" ::= (V"x" + V"y") + C 2)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ [("x", x');("y", y)]))
              (AnWhile b R c)``;

val tm = ``XP ["x";"y"] 
              (\s. ?y x'. (beval (C x > C 0) o ($|++ FEMPTY))[("x", x');("y", y)]
                          /\ 
                          (s = FEMPTY |++ [("x", x');("y", y)]))
              ("x" ::= C 0;; "y" ::= V"x" + C y;; "x" ::= V"y" + C 1;; AnWhile b1 R1 c1;; "y" ::= (V"x" + V"y") + C 2 ;; AnWhile b2 R2 c2;; "y" ::= V"x" + C y;; "x" ::= V"y" + C 1)``;

val MultProg =
 ``"result" ::= C 0;;
   "count" ::= C 0;; 
   AnWhile (V"count" < V"m") 
    (beval ((C n * V"count" = V"result") /\ V"count" <= C m))
    ("result" ::= (V"result" + V"n");;
     "count" ::= (V"count" + C 1));;
   "count" ::= C 0;;                
   "Result" ::= V"result"``; 

val MultProgPre =
 ``(\s. ?Result result count n' m'.
         (beval ((C n * V"count" = V"result") /\ C 0 <= C m /\ V"count" <= C m) o ($|++ FEMPTY))[("m",m');("n",n');("count",count);("result",result);("Result",Result)]
         /\
         (s = FEMPTY |++ [("m",m');("n",n');("count",count);("result",result);("Result",Result)]))``;

val xl = ``["m";"n";"count";"result";"Result"]``;

val tm = ``XP ^xl ^MultProgPre ^MultProg``;

val MultProgTh = XP_CONV conv tm;

CONV_RULE (RHS_CONV(ABS_CONV(STRIP_QUANT_CONV(RATOR_CONV EVAL))
                     THENC DEPTH_CONV MAP_FST_CONV 
                     THENC DEPTH_CONV STATE_EQ_EVAL_CONV)) MultProgTh;

val xl = ``["k"; "result"; "i"; "j"]``;

val absMinus =
    ``"result" ::= C 0 ;; "k" ::= C 0 ;;
      (if V "i" <= V "j" then "k" ::= V "k" + C 1 else Skip) ;;
      (if (V "k" = C 1) /\ ~(V "i" = V "j") then
         "result" ::= V "j" - V "i"
       else
         "result" ::= V "i" - V "j")``;

val absMinusPre1 =
 ``\s. ?j i result k.
         (beval (V"i" < V"j") o ($|++ FEMPTY))[("k", k); ("result", result); ("i", i); ("j",j)]
         /\
         (s = FEMPTY |++ [("k", k); ("result", result); ("i", i); ("j",j)])``;

val tm1 = ``XP ^xl ^absMinusPre1 ^absMinus``;

val absMinusTh1 = XP_CONV conv tm1;

CONV_RULE (RHS_CONV EVAL) absMinusTh1;


val absMinusPre2 =
 ``\s. ?j i result k.
         (beval (V"i" > V"j") o ($|++ FEMPTY))[("k", k); ("result", result); ("i", i); ("j",j)]
         /\
         (s = FEMPTY |++ [("k", k); ("result", result); ("i", i); ("j",j)])``;

val tm2 = ``XP ^xl ^absMinusPre2 ^absMinus``;

val absMinusTh2 = XP_CONV conv tm2;

CONV_RULE (RHS_CONV EVAL) absMinusTh2;


val absMinusPre3 =
 ``\s. ?j i result k.
         ((\s:state. T) o ($|++ FEMPTY))[("k", k); ("result", result); ("i", i); ("j",j)]
         /\
         (s = FEMPTY |++ [("k", k); ("result", result); ("i", i); ("j",j)])``;

val tm3 = ``XP ^xl ^absMinusPre3 ^absMinus``;

val absMinusTh3 = XP_CONV conv tm3;

CONV_RULE (RHS_CONV EVAL) absMinusTh3;


> val it =
    ``XP ["k"; "result"; "i"; "j"]
        (\s.
           ?j i result k.
             (beval (V "i" > V "j") o $|++ FEMPTY)
               [("k",k); ("result",result); ("i",i); ("j",j)] /\
             (s =
              FEMPTY |++
              [("k",Scalar 0); ("result",Scalar 0); ("i",i); ("j",j)]))
        (if V "i" <= V "j" then "k" ::= V "k" + C 1 else Skip)`` : term
- XP_CONV conv it;
Argument:
XP ["k"; "result"; "i"; "j"]
  (\s.
     ?j i result k.
       (beval (V "i" > V "j") o $|++ FEMPTY)
         [("k",k); ("result",result); ("i",i); ("j",j)] /\
       (s =
        FEMPTY |++
        [("k",Scalar 0); ("result",Scalar 0); ("i",i); ("j",j)])) Skip
not equal to lhs of theorem generated by XP_CONV
XP ["k"; "result"; "i"; "j"]
  (\s.
     ?j i result k.
       (beval (V "i" > V "j") o $|++ FEMPTY)
         [("k",k); ("result",result); ("i",i); ("j",j)] /\
       (s =
        FEMPTY |++
        (\l.
           (\k result i j.
              [("k",Scalar 0); ("result",Scalar 0); ("i",i); ("j",j)])
             (LOOKUP "k" l) (LOOKUP "result" l) (LOOKUP "i" l)
             (LOOKUP "j" l))
          [("k",k); ("result",result); ("i",i); ("j",j)])) Skip

! Uncaught exception:
! HOL_ERR
- 




*)

(* EVAL LOOKUP applications *)

fun LOOKUP_EVAL_CONV tm =
 let val (opr,args) = strip_comb tm
 in
  if is_const opr andalso (fst(dest_const opr) = "LOOKUP") 
     andalso (length args = 2) andalso listSyntax.is_list (el 2 args)
  then EVAL tm
  else NO_CONV tm
 end;

(* Simplify ANWHILE_PRED xl P R b  *)

fun ANWHILE_PRED_EVAL_CONV tm =
 let val (opr,args) = strip_comb tm
 in
  if is_const opr andalso (fst(dest_const opr) = "ANWHILE_PRED") andalso 
     (length args = 4) andalso listSyntax.is_list (el 1 args) 
   then EVAL tm
   else NO_CONV tm
 end;


(* EVAL ZIP_LIST applications *)

fun ZIP_LIST_EVAL_CONV tm =
 let val (opr,args) = strip_comb tm
 in
  if is_const opr andalso (fst(dest_const opr) = "ZIP_LIST") andalso 
     (length args = 3) andalso listSyntax.is_list (el 2 args) 
     andalso listSyntax.is_list (el 3 args)
  then EVAL tm
  else NO_CONV tm
 end;

(* EVAL tm in ``(s = FEMPTY |++ tm)`` *)
fun STATE_EQ_EVAL_CONV tm =
 if is_eq tm andalso is_comb(rhs tm) andalso
     (aconv ``$|++ FEMPTY : (string#value)list -> state`` (rator(rhs tm))) andalso
     not(listSyntax.is_list(rand(rhs tm)))
 then RHS_CONV(RAND_CONV EVAL) tm
 else NO_CONV tm;

fun XP_CONV (conv:term->thm) tm =
 let val (lp_op, lp_args) = strip_comb tm
     val _ = if is_const lp_op andalso (fst(dest_const lp_op) = "XP")
              then ()
              else fail()
     val _ = if length lp_args = 3 then () else (fail())
     val (xl,lp_abs,c) = (el 1 lp_args, el 2 lp_args, el 3 lp_args)
     val _ = if is_abs lp_abs
              then ()
              else (print "Bad abs:\n"; print_term lp_abs; print "\n"; fail())
     val (svar,bdy) = dest_abs lp_abs
     val _ = if is_exists bdy
              then ()
              else (print "Bad exists:\n"; print_term bdy; print "\n"; fail())
     val (e_vars,e_body) = strip_exists bdy
     val _ = if all (fn v => type_of v = ``:value``) e_vars
              then ()
              else (print "\nBad type of an existentially quantified variable in:\n";
                    print_term bdy; print "\n")
     val x_vars = map 
                   (fn x => mk_var(fromHOLstring x,``:value``)) 
                   (rev(fst(listSyntax.dest_list xl)))
     val _ = if is_conj e_body
              then ()
              else (print "Bad conj:\n"; print_term e_body; print "\n"; fail())
     val (p_tm,s_tm) = dest_conj e_body
     val _ = if is_comb p_tm
              then ()
              else (print "Bad p-comb:\n"; print_term p_tm; print "\n"; fail())
     val (p,p_arg) = dest_comb p_tm
     val _ = if listSyntax.is_list p_arg
              then ()
              else (print "Bad p_arg -- not a list:\n"; print_term p_arg; print "\n"; fail())
     val _ = if is_eq s_tm andalso is_comb (rhs s_tm)
              then ()
              else (print "Bad s-equation:\n"; print_term s_tm; print "\n"; fail())
     val s_update_list = rand(rhs s_tm)
     val f = makefun p_arg s_update_list 
     val (cmd, cmd_args) = strip_comb c
 in
  case fst(dest_const cmd) of
    "Skip"      => let val lp_skip_th1 = EXPAND_EXISTS(SPECL [xl,f,p] XP_EXEC_SKIP)
                       val lp_skip_th2 = CONV_RULE (RHS_CONV(DEPTH_CONV STATE_EQ_EVAL_CONV)) lp_skip_th1
                       val lp_skip_th3 = CONV_RULE (LHS_CONV(DEPTH_CONV STATE_EQ_EVAL_CONV)) lp_skip_th2
                   in
                    lp_skip_th3
                   end 

  | "GenAssign" => let val all_distinct_th = EVAL ``ALL_DISTINCT ^xl``
                       val map_f_th = 
                        prove
                         (``!l. (MAP FST l = ^xl) ==> (MAP FST (^f l) = ^xl)``,
                          SIMP_TAC list_ss [I_o_ID,MAP_ASSIGN_FUN,MAP_GEN_ASSIGN_FUN])
                         handle e => (print "\nProof failed\n"; print "Term: \n";
                                      print_term tm; print "\nGoal:\n";
                                      print_term ``!l. (MAP FST l = ^xl) ==> (MAP FST (^f l) = ^xl)``;
                                      Raise e)
                       val lp_gen_assign_th1 = SPECL [xl,f,p,el 1 cmd_args,el 2 cmd_args]XP_EXEC_GEN_ASSIGN
                       val lp_gen_assign_th2 = MP (MP lp_gen_assign_th1 (EQT_ELIM all_distinct_th)) map_f_th
                       val lp_gen_assign_th3 = EXPAND_EXISTS lp_gen_assign_th2
                   in 
                    XP_EVAL_RULE lp_gen_assign_th3
                   end

  | "Assign"    => let val all_distinct_th = EVAL ``ALL_DISTINCT ^xl``
                       val map_f_th = 
                        prove
                         (``!l. (MAP FST l = ^xl) ==> (MAP FST (^f l) = ^xl)``,
                          SIMP_TAC list_ss [I_o_ID,MAP_ASSIGN_FUN,MAP_GEN_ASSIGN_FUN])
                         handle e => (print "\nProof failed\n"; print "Term: \n";
                                      print_term tm; print "\nGoal:\n";
                                      print_term ``!l. (MAP FST l = ^xl) ==> (MAP FST (^f l) = ^xl)``;
                                      Raise e)
                       val lp_assign_th1 = SPECL [xl,f,p,el 1 cmd_args,el 2 cmd_args]XP_EXEC_ASSIGN
                       val lp_assign_th2 = MP (MP lp_assign_th1 (EQT_ELIM all_distinct_th)) map_f_th
                       val lp_assign_th3 = EXPAND_EXISTS lp_assign_th2
                   in 
                    XP_EVAL_RULE lp_assign_th3
                   end

  | "Seq"       => let val (c1,c2) = (el 1 cmd_args, el 2 cmd_args) 
                       val lp_seq_th1 = SPECL [xl,f,p,c1,c2] XP_EXEC_SEQ
                       val lp_seq_th2 = CONV_RULE (DEPTH_CONV MAP_FST_CONV) lp_seq_th1
                       val lp_seq_th3 = CONV_RULE (LHS_CONV(RATOR_CONV(RAND_CONV(XP_RESULT_CONV EVAL)))) lp_seq_th2
                       val lp_seq_th4 = CONV_RULE (RHS_CONV(RATOR_CONV(RAND_CONV(RATOR_CONV(RAND_CONV(XP_RESULT_CONV EVAL)))))) lp_seq_th3
                       val c1_th = TRACE(XP_CONV conv) ``XP ^xl ^lp_abs ^c1``
                       val lp_seq_th5 = CONV_RULE (RHS_CONV(RATOR_CONV(RAND_CONV(REWR_CONV c1_th)))) lp_seq_th4
                       val c2_simple_th = EVAL ``SIMPLE ^c2``
                       val lp_orf_th = REWRITE_RULE[c2_simple_th](SPECL [c2,xl] XP_ORF)
                       val lp_seq_th6 = REWRITE_RULE [lp_orf_th] lp_seq_th5 
                   in
                    CONV_RULE (RHS_CONV(DEPTH_CONV(TRACE(XP_CONV conv)))) lp_seq_th6
                   end

  | "Cond"      => let val (b,c1,c2) = (el 1 cmd_args, el 2 cmd_args, el 3 cmd_args)
                   in
                    case CondTest conv xl f p b
                    of TestTrue th  =>
                        let
                         val simple_c2_th = EQT_ELIM(EVAL ``SIMPLE ^c2``) 
                                             handle e => (print "\nCan't prove SIMPLE(";print_term c2; print")\n"; Raise e)
                         val c1_th1 = SPECL [xl,f,p,b,c1,c2] XP_EXEC_IF_T
                         val c1_th2 = MP (MP c1_th1 simple_c2_th) th
                         val c1_th3 = CONV_RULE (RHS_CONV(RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV)))) c1_th2
                         val c1_th4 = CONV_RULE (LHS_CONV(RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV)))) c1_th3
                         val c1_th5 = CONV_RULE (DEPTH_CONV LOOKUP_EVAL_CONV) (BETA_RULE c1_th4)
                        in
                         CONV_RULE (RHS_CONV(TRACE(XP_CONV conv))) c1_th5
                        end
                    |  TestFalse th  =>
                        let
                         val simple_c1_th = EQT_ELIM(EVAL ``SIMPLE ^c1``)
                                             handle e => (print "\nCan't prove SIMPLE(";print_term c1; print")\n"; Raise e)
                         val c2_th1 = SPECL [xl,f,p,b,c1,c2] XP_EXEC_IF_F
                         val c2_th2 = MP (MP c2_th1 simple_c1_th) th
                         val c2_th3 = CONV_RULE (RHS_CONV(RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV)))) c2_th2
                         val c2_th4 = CONV_RULE (LHS_CONV(RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV)))) c2_th3
                         val c2_th5 = CONV_RULE (DEPTH_CONV LOOKUP_EVAL_CONV) (BETA_RULE c2_th4)
                        in
                         CONV_RULE (RHS_CONV(TRACE(XP_CONV conv))) c2_th5
                        end
                    |  Unresolved   =>
                        let
                         val c1_tm1 = ``XP ^xl (\s. ?l. (MAP FST l = ^xl) /\ 
                                               (\l. ^p l /\ beval ^b (FEMPTY |++ (^f l))) l /\ 
                                               (s = FEMPTY |++ ^f l)) ^c1``
                         val c1_th1 = CONV_RULE (DEPTH_CONV STATE_EQ_EVAL_CONV) (RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV)) c1_tm1)
                         val c1_th2 = XP_CONV conv (rhs(concl c1_th1))
                         val c1_th3 = CONV_RULE (DEPTH_CONV LOOKUP_EVAL_CONV) (BETA_RULE c1_th2)
                         val p1 = rator(rand(rator(snd(dest_abs(rator(rand(rator(snd(strip_exists(body(rhs(concl c1_th2))))))))))))
                         val s_update_list1 = rand(rand(rand(snd(strip_exists(body(rhs(concl c1_th2)))))))
                         val f1 =  makefun p_arg s_update_list1
                         val map_f1_th = 
                          prove
                           (``!l. (MAP FST l = ^xl) ==> (MAP FST (^f1 l) = ^xl)``,
                            SIMP_TAC list_ss [I_o_ID,MAP_ASSIGN_FUN,MAP_GEN_ASSIGN_FUN])
                           handle e => (print "\nProof failed\n"; print "Term: \n";
                                        print_term tm; print "\nGoal:\n";
                                        print_term ``!l. (MAP FST l = ^xl) ==> (MAP FST (^f1 l) = ^xl)``;
                                        Raise e)
                         val c2_tm1 = ``XP ^xl (\s. ?l. (MAP FST l = ^xl) /\ 
                                               (\l. ^p l /\ ~(beval ^b (FEMPTY |++ (^f l)))) l /\
                                               (s = FEMPTY |++ ^f l)) ^c2``
                         val c2_th1 = CONV_RULE (DEPTH_CONV STATE_EQ_EVAL_CONV) (RATOR_CONV(RAND_CONV(ABS_CONV MAP_FST_CONV)) c2_tm1)
                         val c2_th2 = XP_CONV conv (rhs(concl c2_th1))
                         val c2_th3 = CONV_RULE (DEPTH_CONV LOOKUP_EVAL_CONV) (BETA_RULE c2_th2)
                         val p2 = rator(rand(rator(snd(dest_abs(rator(rand(rator(snd(strip_exists(body(rhs(concl c2_th2))))))))))))
                         val s_update_list2 = rand(rand(rand(snd(strip_exists(body(rhs(concl c2_th2)))))))
                         val f2 =  makefun p_arg s_update_list2
                         val map_f2_th = 
                          prove
                           (``!l. (MAP FST l = ^xl) ==> (MAP FST (^f2 l) = ^xl)``,
                            SIMP_TAC list_ss [I_o_ID,MAP_ASSIGN_FUN,MAP_GEN_ASSIGN_FUN])
                           handle e => (print "\nProof failed\n"; print "Term: \n";
                                        print_term tm; print "\nGoal:\n";
                                        print_term ``!l. (MAP FST l = ^xl) ==> (MAP FST (^f2 l) = ^xl)``;
                                        Raise e)

                         val lp_if_th1 = SPECL [xl,f,f1,f2,p,p1,p2,b,c1,c2]XP_EXEC_IF_ZIP
                         val lp_if_th2 = MP (MP lp_if_th1 map_f1_th) map_f2_th
                         val lp_if_th3 = CONV_RULE (DEPTH_CONV MAP_FST_CONV) lp_if_th2
                         val lp_if_th4 = CONV_RULE (DEPTH_CONV LOOKUP_EVAL_CONV) (BETA_RULE lp_if_th3)
                         val lp_if_th5 = MP (MP lp_if_th4 c1_th3) c2_th3
                        in
                         CONV_RULE (RHS_CONV(DEPTH_CONV ZIP_LIST_EVAL_CONV)) lp_if_th5
                        end
(*
                    |  Unresolved   =>
                        let
                         val lp_if_th1 = SPECL [xl,f,p,b,c1,c2]XP_EXEC_IF
                         val lp_if_th2 = CONV_RULE (DEPTH_CONV MAP_FST_CONV) lp_if_th1
                         val lp_if_th3 = CONV_RULE (DEPTH_CONV STATE_EQ_EVAL_CONV) lp_if_th2
                         val lp_if_th4 = CONV_RULE (RHS_CONV(RATOR_CONV(RAND_CONV(XP_CONV conv)))) lp_if_th3
                         val lp_if_th5 = CONV_RULE (RHS_CONV(RAND_CONV(XP_CONV conv))) lp_if_th4
                        in
                         lp_if_th5
                        end
*)
                   end

  | "AnWhile"   => let val (b,R,while_body) = (el 1 cmd_args, el 2 cmd_args, el 3 cmd_args)
                       val all_distinct_th = EVAL ``ALL_DISTINCT ^xl``
                       val lp_anwhile_th1 = SPECL [xl,f,p,while_body,R,b] XP_EXEC_ANWHILE
                       val lp_anwhile_th2 = MP lp_anwhile_th1 (EQT_ELIM all_distinct_th)
                       val lp_anwhile_th3 = EXPAND_EXISTS lp_anwhile_th2
                       val lp_anwhile_th4 = XP_EVAL_RULE lp_anwhile_th3
                   in
                    CONV_RULE (ONCE_DEPTH_CONV ANWHILE_PRED_EVAL_CONV) lp_anwhile_th4
                   end

  | _           => (print "\nBad case: "; print(fst(dest_const cmd)); print"\n";fail())
                        
 end;

val XP_CONV = TRACE o XP_CONV;

