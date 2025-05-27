structure ARM_prover_extLib :> ARM_prover_extLib =
struct

(*********************************************************************************)
(*         A Tool To Reason On ARM Model (privilaged mode constraints)           *)
(*                    Narges                       *)
(*********************************************************************************)

open  Abbrev HolKernel boolLib bossLib Parse;
open tacticsLib proofManagerLib arm_seq_monadTheory List;
(*open arm_parserLib arm_encoderLib arm_disassemblerLib;*)


exception not_matched_pattern;

fun proof_progress s = if !Globals.interactive then TextIO.print s else ();
val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val words_ss = simpLib.mk_simpset [wordsLib.WORD_ss];
val simplist = ref [];

fun decompose_term a =
    let val (opr, acs) =
            case dest_term a of
                (LAMB (b,c)) =>
                strip_comb c
              | (* (COMB (b,c)) *) _ =>
                                   strip_comb a
    in
        if (length acs < 2) then
            (opr,opr,opr)
        else
            let val l = List.nth(acs,0)
                val r = List.nth(acs,1)
            in
                if (same_const opr  (``$>>=``))
                then
                    let val (_,r_body) = pairLib.dest_pabs r
                    in
                        (l,r,r_body)
                    end
                else
                    if (same_const opr ``$|||``)
                    then
                        (l,r,r)
                    else (opr,opr,opr)
            end
    end;

(*******should be defined as local *************)
val mk_spec_list =
 fn a =>
    [``(SND (SND (SND (SND ^a)))):CP15sctlr``,
     ``(FST (SND (SND (SND ^a)))):CP15scr``,
     ``(FST (^a)):word32``,
     ``(FST (SND (SND (^a)))):ARMpsr``,
     ``FST (SND ^a):word32``
    ];
val mk_spec_list2 =
 fn a =>
    [``(SND (SND (SND (SND ^a)))):CP15sctlr``,
     ``(FST (SND (SND (SND (^a))))):CP15scr``,
     ``(FST (SND (SND (^a)))):ARMpsr``,
     ``FST (SND ^a):word32``,
     ``(FST (^a)):word32``
    ];

val mk_spec_list3 =
 fn a =>
    [``(SND (SND (SND (SND (SND ^a))))):CP15sctlr``,
     ``(FST (SND (SND (SND (SND ^a))))):CP15scr``,
     ``(FST (^a)):word32``,
     ``(FST (SND (SND (^a)))):bool``,
     ``(FST (SND (SND (SND (^a))))):ARMpsr``,
     ``(FST (SND ^a)):word32``
    ];

val mk_spec_list4 =
 fn a =>
    [``(SND (SND (SND (SND (SND ^a))))):CP15sctlr``,
     ``(FST (SND (SND (SND (SND ^a))))):CP15scr``,
     ``(FST (SND (SND (SND (^a))))):ARMpsr``,
     ``(FST (SND (SND (^a)))):bool``,
     ``(FST (SND ^a)):word32``,
     ``(FST (^a)):word32``
    ];


fun mode_changing_comp_list_rec lst opr = case lst of
                                              (x::rlst) => (same_const opr x) orelse mode_changing_comp_list_rec rlst opr
                                            | _ => false;

fun generate_uncurry_abs a =
    case dest_term a of
        (COMB (c,b))  =>
        if (same_const c ``UNCURRY``) then
            let val (d,e) =
                    case  dest_term b of
                        (LAMB(d,e)) => (d,e)
                      | _ => Raise not_matched_pattern
                val (e_abs,e_trm) = generate_uncurry_abs  e
            in
                (List.concat [[d],e_abs], e_trm)
            end
        else
            ([], b)
      | (LAMB(c,b))  =>
        ([c] , b)
      | _ => ([], a);


fun get_monad_type tp =
    let val (str , fst , snd) =
            case dest_type (tp) of
                (str , [fst , snd]) => (str , fst , snd)
              | _ => Raise not_matched_pattern
        val (str , tp_type, b) =
            case dest_type snd of
                (str , [tp_type, b]) => (str , tp_type, b)
              | _ => Raise not_matched_pattern
    in
        tp_type
    end;
fun generate_uncurry_abs_from_abs a =
    case dest_term a of
        (LAMB (d,e))  =>
        let val (e_abs,e_trm) = generate_uncurry_abs_from_abs  e
        in
            (List.concat [[d],e_abs], e_trm)
        end
      | _  =>
        ([] , a) ;

fun get_action_from_goal g =
    let val (asm ,con) = g
        val (c1,d1) = strip_comb con
    (* val (c2,d2) = strip_comb (List.nth(d1,1)) *)
    (* val (b,c) = if (is_comb (List.nth(d1,0)))  *)
    (*      then  *)
    (*          strip_comb  (List.nth(d1,0)) *)
    (*      else  *)
    (*              strip_comb (List.nth(d1,0)) *)
    in
        List.nth(d1,0)
    end

fun prove_simple_action opr a expr postfix =
    let

        val thrm = SPEC (List.nth(expr,0)) (DB.fetch  (current_theory()) ((Hol_pp.term_to_string (opr)) ^ postfix))

        val _ =  proof_progress ("\nTheorem " ^ (term_to_string opr) ^ postfix ^"thm is applied!\n ")

        val tacs = RW_TAC (srw_ss()) [thrm] THEN
                          (ASSUME_TAC thrm THEN
                                      UNDISCH_ALL_TAC THEN
                                      RW_TAC (srw_ss()) [])

        val _ = e (tacs)
        val proved_a = top_thm()
        val _ = proofManagerLib.drop()

        val _ = proof_progress ("\nProof of theorem: " ^ (term_to_string a) ^ " is completed!\n ")
    in
        (proved_a , tacs)
    end;


fun exists_theorem thy x =
    let val thms = theorems thy
        val thm = List.find (fn (s,t) => (s=x)) thms
    in
        case thm of
            SOME (p,q) => true
          | NONE => false
    end;

fun find_theorem x =
    let val _ = proof_progress ("Searching for the theorem " ^ (x) ^ "\n")
        val db_x = DB.find x
        val res = List.find (fn ((s,t),p) => (t=x)) db_x
    in
      case  res of
          SOME (_,(p,_,_)) =>
          let val _ = proof_progress ("The theorem " ^ x ^ " was found\n ") in
            p
          end
         |NONE =>
          let val _ = proof_progress ("The theorem " ^ x ^ " was not found\n ")
          in
            ASSUME ``T``
          end
    end;


fun decompose a postfix =
    let val (opr, acs) =
            case dest_term a of
                (LAMB (b,c)) =>
                strip_comb c
              | (* (COMB (b,c)) *) _ =>
                                   strip_comb a

        val thm_exists = (* if (* ((* !global_mode = ``16w:bool[5]`` andalso  *)(term_eq src_inv trg_inv)) orelse *) *)
            (*    ((same_const opr ``write_cpsr``) ) *)
            (* then *)
            exists_theorem (current_theory()) (term_to_string opr ^ postfix )
        (* else *)
        (*     exists_theorem (current_theory()) (term_to_string opr ^ "_comb" ^ postfix) *)

        val flag = ((same_const opr ``$>>=``) orelse
                    (same_const opr ``$|||``) orelse
                    (same_const opr ``constT``) orelse
                    (same_const opr ``COND``) orelse
                    (same_const opr ``condT``) orelse
                    (same_const opr ``forT``) orelse
                    (TypeBase.is_case a ) orelse
                    thm_exists)
    in
        if (length acs < 2) then
            (flag,opr,opr,opr)
        else
            let val l = List.nth(acs,0)
                val r = List.nth(acs,1)
            in
                if (same_const opr  (``$>>=``))
                then (flag,l,r,opr)
                else
                    if (same_const opr ``$|||``) then
                        (flag,l,r,opr)
                    else (flag,opr,opr,opr)
            end
    end;


(*TODO: use some sort of pattern mathiching instead of list lenght!!!*)
fun get_uncurried_theorem thm l =
    let val (asm,con) = dest_thm thm
    in
        if( l = 1)
        then
            thm
        else
            let
                val con = concl thm
                val res_thm1 = PairRules.SWAP_PFORALL_CONV con
                val res_thm2 = REWRITE_RULE [res_thm1] thm
                val con1 = concl res_thm1
                val (a,b) = dest_eq con1
                val res_thm3 = PairRules.UNCURRY_FORALL_CONV  b
                val res_thm = REWRITE_RULE [res_thm3] res_thm2
            in
                get_uncurried_theorem res_thm (l-1)
            end
    end;

fun generalize_theorem thm a =
    let
        val (a_abs,a_body) = pairLib.dest_pabs a
        val (abs_args, abs_body)  = generate_uncurry_abs a
        val generalized_curried_thm =  PairRules.PGENL (List.rev(abs_args)) thm
        val generalized_uncurried_thm =
            get_uncurried_theorem generalized_curried_thm (List.length(abs_args))
        val abs_type = type_of a_abs
        val gen_var = (mk_var("y", abs_type))
        val spec_thm= PairRules.PSPEC gen_var generalized_uncurried_thm
        val generalized_thm = GEN  gen_var spec_thm
    in
        generalized_thm
    end;

(* for types of form k->pM, if i=true then returns k otherwise p*)
val get_type_inst =
 fn (t, i) =>
    case dest_type (t) of
        (str , [fst , snd]) =>
        if(i)
        then
            fst
        else
            snd
      |_ => Raise not_matched_pattern;



fun prove_const a pred expr cm postfix thms =
    let

        val prove_COND_action =
         fn (if_part,else_part,condition,a,pred,expr,cm,postfix,thms) =>
            let val _ = proof_progress ("A Conditional action\n\n\n")

                val (if_part_thm,tc) = prove_const if_part pred expr cm postfix thms;
                val (else_part_thm,tc') = prove_const else_part pred expr cm postfix thms;
                val tacs =  (ASSUME_TAC if_part_thm)
                                THEN (ASSUME_TAC else_part_thm)
                                THEN (IF_CASES_TAC )
                                THEN (FULL_SIMP_TAC (srw_ss()) [])
                                THEN (FULL_SIMP_TAC (srw_ss()) [])
                val _ = e (tacs)
                val proved_b = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_b, tacs)
            end


        val prove_composite_action =
         fn (l, r, opr, a,pred,expr, cm,postfix,thms) =>
            let val _ = proof_progress ("\n\nProof of the compositional action:\n"^(term_to_string a)^"\n\n")
                (* val (left_hand_thm , tc) =   prove l  pred expr cm postfix *)
                (* val tacs =  (ASSUME_TAC left_hand_thm)  *)
                (* val _ = e (tacs) *)

                (* proof of the right part*)


                (* combining the left and right parts    *)
                val l_type = get_monad_type(type_of(l));
                val snd = type_of(r);

                val (part , comb_thm) =
                    if (same_const  opr ``$>>=``)
                    then
                        let
                            val (_,r_body) = pairLib.dest_pabs r
                            val (_,_,_,oprr) = decompose r_body "";
                        in
                            if (same_const oprr ``constT``)
                            then
                                (l , SPECL [l,List.nth(expr,0)]
                                           (List.nth(thms, 6)))
                            else
                                (r , SPECL [ r, l, List.nth(expr,0)]
                                           (INST_TYPE [alpha |-> l_type,
                                                       beta  |-> get_monad_type(get_type_inst(snd , false))]
                                                      (List.nth(thms, 1))))
                        end
                    else
                        (r , SPECL [ r,l, List.nth(expr,0)]
                                   (INST_TYPE [alpha |-> get_monad_type(snd),
                                               beta  |-> l_type]
                                              (List.nth(thms, 2))))
                val (right_hand_thm, tc) = prove_const part pred expr cm postfix thms
                val tacsb =
                    ASSUME_TAC right_hand_thm
                               THEN ASSUME_TAC comb_thm
                              (* THEN ASSUME_TAC (SPEC l  (INST_TYPE [alpha |-> ``:arm_state``,
                                                                    beta |-> l_type]
                                                                   no_access_violation_thm))
                              *) THEN RES_TAC
                               THEN (RW_TAC (srw_ss()) [])
                val _ = e (tacsb)
                val thrm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (thrm,tacsb)
            end;


        val prove_constT_action =
         fn (a,src_inv, trg_inv) =>
            let
                val (opr, arg) =
                    case dest_term a of
                        COMB (opr, arg) => (opr, arg)
                      |_ => Raise not_matched_pattern
                val tac = RW_TAC (srw_ss())
                                 []
                val _ = e (tac)
                val proved_thm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_thm, tac)
            end

        val prove_condT_action =
         fn (a, pred, expr, cm, postfix,thms) =>
            let val (opr, acs) = strip_comb a
                val (arg_thm,tc) = prove_const (List.nth(acs,1))   pred expr cm postfix thms
                val tacs =   ASSUME_TAC arg_thm
                                        THEN RW_TAC (srw_ss()) [List.nth(thms, 3)]
                val _ = e (tacs)
                val proved_thm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_thm,tc)
            end
        (*thms*)

        val prove_case_body =
         fn (opt,body,flag,pred, expr, cm, postfix,thms) =>
            let val (body_thm,body_tac) = prove_const body pred expr cm postfix thms
                val tacs = if (flag) then
                               CASE_TAC
                                   THEN FULL_SIMP_TAC (srw_ss()) []
                                   THEN1 (ASSUME_TAC body_thm
                                                     THEN FULL_SIMP_TAC (srw_ss()) [List.nth(thms, 0)]
                                                     THEN (FULL_SIMP_TAC (srw_ss()) []))
                           else
                               (ASSUME_TAC body_thm
                                           THEN FULL_SIMP_TAC (srw_ss()) [List.nth(thms, 0)]
                                           THEN (FULL_SIMP_TAC (srw_ss()) []))
                val _ = e (tacs)
            in
                (body_thm, tacs)
            end

        val analyze_action =
         fn (a, l , r, opr,pred,expr,cm,postfix,thms) =>
            if ((same_const  opr ``$>>=``) orelse
                (same_const  opr ``$|||``))
            then
                prove_composite_action (l, r, opr ,a, pred, expr,cm,postfix,thms)
            else
                let val _ = proof_progress ("\n\nProof of a simple action:\n "^(term_to_string l)^"\n\n")

                    val thm_exist = ((exists_theorem (current_theory()) (term_to_string l ^ postfix))) in
                    (* if (thm_exist) *)
                    (* then *)
                    prove_simple_action l a expr postfix
                (* else *)
                (*     prove_condT_action (a,pred,expr,cm) *)
                end
        val prove_abs_action =
         fn (a, pred ,expr ,cm ,postfix ,thms) =>
            let
                val (a_abs,a_body) = pairLib.dest_pabs a;
                val _ =  List.nth(pred,1)  a expr

                val _ = e (FULL_SIMP_TAC (let_ss) [])  (*change of Oliver*)
                val (proved_a,b) = prove_const a_body pred expr cm postfix thms

                val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
                val unbeta_a = mk_comb (a, a_abs)
                (*val (str , [fst , snd]) = dest_type (type_of a_body) *)
                (*        val (str , [a_body_type, b]) = dest_type snd;*)
                val snd = get_type_inst (type_of(a_body) , false)
                val a_body_type = get_type_inst (snd, true)
                val expr_elm = List.nth(expr,0)

                val proved_unbeta_lemma = prove(``(priv_cpsr_flags_constraints ^a_body ^expr_elm)=
                                          (priv_cpsr_flags_constraints ^unbeta_a ^expr_elm)``,
                                                     (ASSUME_TAC (SPECL [a_body,``^unbeta_a``, expr_elm]
                                                                        (INST_TYPE [beta |-> a_body_type,
                                                                                    alpha |-> ``:arm_state``]
                                                                                   (List.nth(thms,3)))))
                                                         THEN ASSUME_TAC unbeta_thm
                                                         THEN RES_TAC)

                val proved_preserve_unbeta_a =
                    TAC_PROOF(
                      ([], “priv_cpsr_flags_constraints ^unbeta_a ^expr_elm”),
                      (ASSUME_TAC (proved_unbeta_lemma))
                        THEN (ASSUME_TAC proved_a)
                        THEN (FULL_SIMP_TAC (srw_ss()) []))

                val abs_type = type_of a_abs
                val (abs_args, abs_body)  = generate_uncurry_abs a
                val tacs =  (ASSUME_TAC proved_preserve_unbeta_a)
                val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a
                val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
                                THEN (ASSUME_TAC (
                                      SPECL[a, List.nth(expr,0)]
                                           (INST_TYPE [alpha |-> abs_type,
                                                       beta  |-> ``:arm_state``,
                                                       gamma |-> a_body_type]
                                                      (List.nth(thms,4)))))
                                THEN (RW_TAC (srw_ss()) [])
                                THEN (FULL_SIMP_TAC (srw_ss()) [])
                                THEN (UNDISCH_ALL_TAC THEN
                                                      (RW_TAC (srw_ss()) [])
                                                      THEN (FULL_SIMP_TAC (srw_ss()) []))
                val _ = e (tacs)
                val proved_thm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_thm,tacs)
            end

        val prove_simple_unproved_action =
         fn (a, opr,cm ) =>
            let val a_name = opr
                val _ = if !Globals.interactive then
                          TextIO.print ("Do you have a theorem to prove " ^ (term_to_string (a)) ^ "  theorem? \n\n")
                        else ()
            (* val resp = valOf (TextIO.inputLine TextIO.stdIn)  *)
            in
                if (same_const  opr ``readT``)
                then
                    let val tac = RW_TAC (srw_ss())
                                         []
                                         THEN FULL_SIMP_TAC (srw_ss()) [readT_def]
                                         THEN PAT_X_ASSUM ``∀ii reg.X`` (fn thm => ASSUME_TAC (SPECL [``<|proc:=0|>``] thm))
                                         THEN FULL_SIMP_TAC (srw_ss()) [readT_def] THEN (REPEAT (RW_TAC (srw_ss()) []))

                        val _ = e (tac)
                        val (proved_thm) = top_thm()
                        val _ = proofManagerLib.drop()
                    in
                        (proved_thm, tac)
                    end
                else

                    let (* val  _ = (set_goal([], ``preserve_relation ^a``)) *)
                        val simp_thm = find_theorem ((term_to_string (opr))^"_def")
                        val tacs =  (FULL_SIMP_TAC (srw_ss()) [simp_thm,writeT_def])
                        val _ = e (tacs)
                        val (asm,con) = top_goal()
                        val a' = get_action_from_goal (top_goal())
                        val (flag,l ,r , opr) = decompose a'  postfix;
                        val (proved_a, tacb) =
                            if (flag)
                            then
                                analyze_action (a', l, r, opr,pred,expr,cm,postfix,thms)
                            else
                                let
                                    val (next_proof , next_tac) = prove_const a' pred expr cm postfix thms
                                    val tac = RW_TAC (srw_ss()) [next_proof]
                                    val _ = e (tac)
                                    val (proved_thm) = top_thm()
                                    val _ = proofManagerLib.drop()
                                in
                                    (proved_thm, tac)
                                end
                        val tacs = tacs THEN tacb
                    (* val _ = save_proof a_name a (tacs) *)
                    in
                        (proved_a, tacs)
                    end
            end
    in
        case dest_term a of
            (LAMB (c,b))  =>
            prove_abs_action (a, pred ,expr ,cm ,postfix ,thms)
          | COMB (c,b) =>
            if (same_const c ``UNCURRY``)
            then
                prove_abs_action (a, pred ,expr ,cm ,postfix ,thms)
            else
                let val _ = proof_progress ("current action:\n\n"^(term_to_string(a)^ "\n"))
                    val _ =  List.nth(pred,0)  a expr
                    val tac = FULL_SIMP_TAC (let_ss) []
                                            THEN FULL_SIMP_TAC (srw_ss()) [List.nth(thms,5)]
                                            THEN TRY (ASSUME_TAC (List.nth(thms,5))
                                                                 THEN FULL_SIMP_TAC (srw_ss()) [])
                    val _ = e (tac)
                in
                    if (can top_thm())
                    then
                        let val (proved_thm) = top_thm()
                            val _ = proofManagerLib.drop()
                        in
                            (proved_thm, tac)
                        end
                    else
                        let  val _ = proofManagerLib.b()
                             val a' = get_action_from_goal (top_goal());
                             val (flag,l ,r , opr) = decompose a' postfix;
                        in
                            if (flag)
                            then
                                analyze_action (a' , l, r, opr,pred,expr,cm,postfix,thms)
                            else
                                (* if (same_const opr ``UNCURRY``) *)
                                (* then *)
                                (* prove_abs_action (a',pred,expr,cm) *)
                                (* else *)
                                prove_simple_unproved_action (a',l,cm)
                        end
                end
          | _ => (ASSUME ``T``, NO_TAC)
    end;
fun get_first_cpc_lemmma abody expr_elm unbeta_a unbeta_thm thms =
    let val snd = get_type_inst (type_of(abody) , false)
        val abody_type = get_type_inst (snd, true)
        val  proved_unbeta_lemma =
             prove (``(priv_cpsr_flags_constraints ^abody ^expr_elm)=
             (priv_cpsr_flags_constraints ^unbeta_a ^expr_elm)``,
                   (ASSUME_TAC (SPECL [abody,``^unbeta_a``, expr_elm]
                                      (INST_TYPE [beta |-> abody_type,
                                                  alpha |-> ``:arm_state``]
                                                 (List.nth(thms,3)))))
                       THEN ASSUME_TAC unbeta_thm
                       THEN RES_TAC)
    in
        proved_unbeta_lemma
    end;


fun get_second_lemmma proved_a expr_elm unbeta_a proved_unbeta_lemma =
    TAC_PROOF(([], `` ( priv_cpsr_flags_constraints ^unbeta_a ^expr_elm)``),
               (ASSUME_TAC (proved_unbeta_lemma))
                   THEN (ASSUME_TAC proved_a)
                   THEN (FULL_SIMP_TAC (srw_ss()) []))


fun get_first_spc_lemma abody expr unbeta_a unbeta_thm thms =
    let val snd = get_type_inst (type_of(abody) , false)
        val mode = List.nth(expr,0)
        val bvt = List.nth(expr,1)
        val abody_type = get_type_inst (snd, true)
        val  proved_unbeta_lemma =
             prove (``(set_pc_to ^abody ^mode ^bvt)=
             (set_pc_to ^unbeta_a ^mode ^bvt)``,
                   (ASSUME_TAC (SPECL [abody,``^unbeta_a``, mode]
                                      (INST_TYPE [beta |-> abody_type,
                                                  alpha |-> ``:arm_state``]
                                                 (List.nth(thms,3)))))
                       THEN ASSUME_TAC unbeta_thm
                       THEN RES_TAC)
    in
        proved_unbeta_lemma
    end;


fun get_second_spc_lemma proved_a expr unbeta_a proved_unbeta_lemma =
    let val mode = List.nth(expr,0)
        val bvt = List.nth(expr,1)
    in
        TAC_PROOF (([], “set_pc_to ^unbeta_a ^mode ^bvt”),
                   ASSUME_TAC (proved_unbeta_lemma) THEN
                   ASSUME_TAC proved_a THEN FULL_SIMP_TAC (srw_ss()) [])
    end;

 fun prove_abs_action (a, pred ,expr ,proved_a,thms, unbetaf1, unbetaf2) =
    let
        val (a_abs,a_body) = pairLib.dest_pabs a;
        val _ =  List.nth(pred,1) a expr

        val _ = e (FULL_SIMP_TAC (let_ss) [])  (*change of Oliver*)

        val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
        val unbeta_a = mk_comb (a, a_abs)
        (*val (str , [fst , snd]) = dest_type (type_of a_body) *)
        (*        val (str , [a_body_type, b]) = dest_type snd;*)
        val snd = get_type_inst (type_of(a_body) , false)
        val a_body_type = get_type_inst (snd, true)
        val expr_elm = List.nth(expr,0)

        val proved_unbeta_lemma = unbetaf1 a_body expr unbeta_a unbeta_thm thms

        val proved_preserve_unbeta_a =  unbetaf2 proved_a expr unbeta_a proved_unbeta_lemma

        val abs_type = type_of a_abs
        val (abs_args, abs_body)  = generate_uncurry_abs a
        val tacs =  ASSUME_TAC proved_preserve_unbeta_a
        val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a
        val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
                        THEN (ASSUME_TAC (
                              SPECL[a, List.nth(expr,0)]
                                   (INST_TYPE [alpha |-> abs_type,
                                               beta  |-> ``:arm_state``,
                                               gamma |-> a_body_type]
                                              (List.nth(thms,4)))))
                        THEN (RW_TAC (srw_ss()) [])
                        THEN (FULL_SIMP_TAC (srw_ss()) [])
                        THEN (UNDISCH_ALL_TAC THEN
                                              (RW_TAC (srw_ss()) [])
                                              THEN (FULL_SIMP_TAC (srw_ss()) []))
        val _ = e (tacs)
        val proved_thm = top_thm()
        val _ = proofManagerLib.drop()
    in
        (proved_thm,tacs)
    end
end
