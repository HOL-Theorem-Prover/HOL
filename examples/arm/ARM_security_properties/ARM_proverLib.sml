structure ARM_proverLib :> ARM_proverLib =
struct

open  Abbrev HolKernel boolLib bossLib Parse proofManagerLib;
open  arm_seq_monadTheory ;
open tacticsLib  inference_rulesTheory;

(***************************************************************)
(*         ARM-PROVER: A Tool To Reason On ARM Model           *)
(*                           Narges                            *)
(***************************************************************)


exception not_matched_pattern;

fun proof_progress s = if !Globals.interactive then TextIO.print s else ()
val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val words_ss = simpLib.mk_simpset [wordsLib.WORD_ss];
val global_mode = ref ``16w:bool[5]``;
val simp_thms_list = ref ([]:(Theory.thm list));
val bool_ss = boolSimps.bool_ss -* ["lift_disj_eq", "lift_imp_disj"]

val mode_changing_comp_list =
    ref [``take_undef_instr_exception``, ``take_svc_exception``];
fun mode_changing_comp_list_rec lst opr =
    case lst of
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

fun get_action_from_goal gl =
    let val (asm ,con) = gl
        val (c1,d1) = if (is_comb con)
                      then
                          strip_comb con
                      else
                          Raise not_matched_pattern
    (* val (c2,d2) = strip_comb (List.nth(d1,0)) *)
    (* val (b,c) = if (is_comb (List.nth(d1,0)))  *)
    (*      then  *)
    (*          strip_comb  (List.nth(d1,0)) *)
    (*      else  *)
    (*              strip_comb (List.nth(d1,0)) *)
    in
        List.nth(d1,0)
    end

(* changed by Oliver *)


fun find_mode_update cpsr_with_x =
    let
        val (update_indicator, [constant, rest]) = strip_comb cpsr_with_x
    in
        if (update_indicator ~~ ``ARMpsr_M_fupd``)
        then constant
        else find_mode_update rest
    end;


fun get_mode_from_action_without_lambda a =
    let
        val (c1,d1) = strip_comb a
        val found   = find_mode_update  (List.nth(d1,1))
        val (c3,d3) = strip_comb (found)
    in
        (List.nth(d3,0))
    end

fun get_mode_from_action a =
    (* let val _ = debug_out "get mode from action" [a] in *)
    case dest_term a of
        (LAMB (c,b))  => get_mode_from_action_without_lambda b
      | _  => get_mode_from_action_without_lambda a
(* end *);

(* end of changes by Oliver *)


fun get_trg_invr_mode_from_goal (asm,con) =
    let
        val (x,trg_inv) =
            case dest_term con of
                COMB(x,trg_inv) => (x,trg_inv)
              | _ => Raise not_matched_pattern

        val (x,trg_mode) =
            case dest_term x of
                COMB(x,trg_mode) => (x,trg_mode)
              | _ => Raise not_matched_pattern
    in
        trg_mode
    end;


fun get_invrs_from_goal (asm,con) =
    let
        val (x,trg_inv) =
            case dest_term con of
                COMB(y,trg_inv) =>
                (case dest_term y of
                     COMB(z,trg_inv) =>
                     ( case dest_term z of
                           COMB(k,trg_inv) => (k,trg_inv)
                         | _ => Raise not_matched_pattern)
                   | _ => Raise not_matched_pattern)
              | _ => Raise not_matched_pattern

        val (b,src_inv) =
            case dest_term x of
                COMB(b,src_inv) =>
                (b,src_inv)
              | _ => Raise not_matched_pattern
    in
        (src_inv,trg_inv)
    end;

(*
fun exists_theorem thy x =
    let val thms = theorems thy
        val thm = List.find (fn (s,t) => (s=x)) thms
    in
        case thm of
            SOME (p,q) => true
          | NONE => false
    end;*)

fun exists_theorem thy x =
    isSome $ List.find (fn ((s,t),p) => (t=x)) $ DB.find x



fun find_theorem x =
    let
        val _ = proof_progress ("Searching for the theorem " ^ (x) ^ "\n")
        val db_x = DB.find x
        val res = List.find (fn ((s,t),p) => (t=x)) db_x in
        case  res of
            SOME ((s,t),(p,_,_)) =>
            let val _ = proof_progress ("The theorem " ^ x ^ " was found\n ") in
                p
            end
          |NONE =>
           let val _ = proof_progress ("The theorem " ^ x ^ " was not found\n ") in
               ASSUME ``T``
           end
    end;


fun prove_simple_action opr a uargs pthms =
    let
        val  mode_changing_comp =
          fn (opr) =>
             (mode_changing_comp_list_rec (! mode_changing_comp_list) opr) (*changed by Oliver *)

        val uf_fun = List.nth(uargs,0)
        val uy_fun = List.nth(uargs,1)
        val cm = List.nth(uargs,2)
        val ext = term_to_string(List.nth(uargs,3))

        val (src_inv,trg_inv) = get_invrs_from_goal(top_goal());
        val same_mode =  (term_eq src_inv trg_inv);
        val thrm =
            if (same_mode (* andalso (! global_mode=``16w:bool[5]``) *)) orelse
               (same_const opr ``write_cpsr``)
            then
                (*      (DB.fetch  (current_theory()) ((Hol_pp.term_to_string (opr)) ^ ext)) *)
                find_theorem ((Hol_pp.term_to_string (opr)) ^ ext)
            else
                (*      (DB.fetch  (current_theory()) ((Hol_pp.term_to_string (opr)) ^ "_comb"^ ext))*)
                find_theorem ((Hol_pp.term_to_string (opr)) ^ "_comb"^ ext)
        val _ =  if (same_mode (* andalso (! global_mode=``16w:bool[5]``) *))
                 then
                     proof_progress ("\nTheorem " ^ (term_to_string opr) ^ ext ^ " is applied!\n ")
                 else
                     proof_progress ("\nTheorem " ^ (term_to_string opr) ^ "_comb" ^ ext ^ " is applied!\n ")
      ;
        val tacs =
            if (same_const opr ``write_cpsr``)
            then
                RW_TAC (srw_ss()) [SPECL [``16w:bool[5]``,(get_mode_from_action a )] thrm]
            else
                if (same_mode orelse (mode_changing_comp opr))
                then
                    RW_TAC (srw_ss()) [thrm]
                else
                    let
                        val b_thm = if (same_const opr ``errorT``)
                                    then
                                        let
                                            val (c,str) =
                                                case dest_term a of
                                                    COMB(c,str) => (c,str)
                                                  |_ => Raise not_matched_pattern
                                        in
                                            if (same_mode)
                                            then
                                                SPECL [uf_fun,uy_fun] (
                                                INST_TYPE [alpha |->
                                                                 get_monad_type(type_of(a))] thrm)
                                            else
                                                SPECL [src_inv, trg_inv,
                                                       str,uf_fun,uy_fun]
                                                      (INST_TYPE [alpha |->
                                                                        get_monad_type(type_of(a))] thrm)
                                        end
                                    else
                                        let val a_thm = SPECL [``assert_mode 16w``,
                                                               ``assert_mode ^cm``,
                                                               trg_inv, ``assert_mode 16w``, a, uf_fun,uy_fun]
                                                              (INST_TYPE [alpha |-> get_monad_type(type_of(a))]
                                                                         preserve_relation_comb_thm1)

                                            val _ = proof_progress ("\nTheorem " ^ (term_to_string (concl a_thm)) ^ " \n\n\n ")
                                        in
                                            LIST_MP [thrm,
                                                     SPECL [``16w:bool[5]``, cm] comb_mode_thm] a_thm
                                        end
                    in
                        RW_TAC (srw_ss()) [b_thm]
                    end

        val _ = e (tacs)
        val proved_a = top_thm()
        val _ = proofManagerLib.drop()

        val cm' = (same_const  opr ``write_cpsr``);
        val new_mode =
            if (cm')
            then
                ``^cm:bool[5]``
            else
                !global_mode;
        val () = global_mode := new_mode
        val _ = proof_progress ("\nProof of theorem: " ^ (term_to_string a) ^ " is completed!\n "^
                                "global mode is " ^ (term_to_string (!global_mode)))
    in
        (proved_a , tacs)
    end;



fun decompose a src_inv trg_inv uargs =
    let val (opr, acs) =
            case dest_term a of
                (LAMB (b,c)) =>
                strip_comb c
              | (* (COMB (b,c)) *) _ =>
                                   strip_comb a
        val ext = term_to_string(List.nth(uargs,3))

        val thm_exists = if ((term_eq src_inv trg_inv)) orelse
                            ((same_const opr ``write_cpsr``) )
                         then
                             exists_theorem (current_theory()) (term_to_string opr ^ ext)
                         else
                             exists_theorem (current_theory()) (term_to_string opr ^ "_comb" ^ ext)

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

(* should be modified to save untouching and preserving lemmas as two separate lemmas*)

fun save_proof name a tacs =
    let val _ = TextIO.print ("Do you like to save the following theorem? \n " ^
                              (term_to_string (a)) ^ " \n")
        (* val _   = valOf (TextIO.inputLine TextIO.stdIn) *)
        val str = valOf (TextIO.inputLine TextIO.stdIn)
    in
        case str of
            "y\n" =>
            let val _ =  store_thm (((term_to_string (name)) ^ "_thm"), ``preserve_relation_mmu ^a``, tacs)
            in
                store_thm (((term_to_string (name)) ^ "_ut_thm"), ``preserve_relation_mmu ^a``, tacs)
            end
          | _ =>
            store_thm ("tatulogy", ``T``, DECIDE_TAC)
    end;



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

fun build_right_hand_side (src_inv, trg_inv,
                           rsrc_inv, rtrg_inv,
                           lsrc_inv, ltrg_inv,
                           l, r, a,
                           right_hand_thm,(* is_write_cpsr, *)
                           flg,uargs,trans_uf_thm) =
    let
        val uf_fun = List.nth(uargs,0)
        val uy_fun = List.nth(uargs,1)
        val cm = List.nth(uargs,2)

        val l_type = get_monad_type(type_of(l));
        val r_type =
            if(flg)
            then
                (get_monad_type ( get_type_inst (type_of(r) ,false)))
            else
                get_monad_type (type_of(r))
        val same_whole_mode =  (term_eq src_inv trg_inv);
        val same_right_mode =  (term_eq rsrc_inv rtrg_inv);
        val same_left_mode =   (term_eq lsrc_inv ltrg_inv);

        val  r_type' =   if ( same_right_mode )
                         then
                             r_type
                         else
                             get_monad_type (type_of(r))

        val base_thm = if (flg)
                       then
                           if ( same_whole_mode orelse
                                (same_right_mode andalso same_left_mode))
                           then
                               seqT_preserves_relation_uu_thm
                           else
                               if(same_right_mode orelse (not same_left_mode))
                               then
                                   seqT_preserves_relation_up2_thm
                               else
                                   seqT_preserves_relation_uc_thm

                       else
                           if (same_whole_mode)
                           then
                               parT_preserves_relation_uu_thm
                           else
                               parT_preserves_relation_up_thm

    in
        (*************************************************************************)
        (*for computations in user mode BEFORE seeing take_exception or write_cpsr*)
        (*************************************************************************)
        if (same_whole_mode)
        then
            let
                val operator_tac =
                    ASSUME_TAC (SPECL [l,r, !global_mode,uf_fun,uy_fun]
                                      (INST_TYPE [alpha |-> l_type,
                                                  beta  |-> r_type']
                                                 base_thm))
            in
                ASSUME_TAC right_hand_thm
                           THEN operator_tac
                           THEN ASSUME_TAC trans_uf_thm
                           THEN ASSUME_TAC (SPEC rtrg_inv comb_monot_thm)
                           THEN RES_TAC
            end
        else
            (*************************************************************************)
            (*for computations AFTER seeing take_exception or write_cpsr*)
            (*************************************************************************)
            ASSUME_TAC right_hand_thm
                       THEN ASSUME_TAC trans_uf_thm
                       THEN
                       (if (same_left_mode)
                        then
                            if (same_right_mode)
                            then
                                IMP_RES_TAC (SPECL [l,r,
                                                    !global_mode,uf_fun,uy_fun]
                                                   (INST_TYPE [alpha |-> l_type,
                                                               beta  |-> r_type]
                                                              base_thm
                                            ))
                                            THEN ASSUME_TAC (SPECL [!global_mode, cm] comb_mode_thm)
                                            THEN ASSUME_TAC (SPECL [src_inv,``(assert_mode ^cm)``,
                                                                    trg_inv,src_inv,a ,
                                                                    uf_fun,uy_fun]
                                                                   (INST_TYPE [alpha |-> get_monad_type(type_of(a))]
                                                                              preserve_relation_comb_v2_thm))
                            else
                                ASSUME_TAC (SPECL [``16w:bool[5]``,cm] comb_mode_thm)
                                           THEN IMP_RES_TAC
                                           (SPECL [src_inv,``(assert_mode ^cm)``,
                                                   trg_inv,src_inv,r ,uf_fun,uy_fun]
                                                  (INST_TYPE [alpha |-> l_type,
                                                              beta  |-> get_monad_type(type_of(a))]
                                                             preserve_relation_comb_abs_thm))
                                           THEN ASSUME_TAC (SPECL [l,r, ``16w:bool[5]``, cm,
                                                                   trg_inv ,uf_fun,uy_fun]
                                                                  (INST_TYPE [alpha |-> l_type,
                                                                              beta  |-> r_type]
                                                                             base_thm))
                        else
                            ASSUME_TAC (SPECL [l,r, ``16w:bool[5]``,
                                               !global_mode,
                                               uf_fun,uy_fun]
                                              (INST_TYPE [alpha |-> l_type,
                                                          beta  |-> r_type]
                                                         base_thm)))

    end




fun prove a src_inv trg_inv uargs pthms  =
    let
        val prove_COND_action =
         fn (if_part,else_part,condition,a,src_inv,trg_inv,uargs,pthms) =>
            let val _ = proof_progress ("A Conditional action\n\n\n")

                val (if_part_thm,tc) = prove if_part src_inv trg_inv uargs pthms;
                val (else_part_thm,tc') = prove else_part src_inv trg_inv uargs pthms;
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
         fn (l, r, opr, a, src_inv, trg_inv,uargs,pthms) =>
            let val _ = proof_progress ("\n\nProof of the compositional action:\n"
                                        ^(term_to_string a)^"\n\n")
                val cm = List.nth(uargs,2)

                (* val (f,ll ,lr , oprr) = decompose r src_inv trg_inv uargs; *)

                (* proof of the left part*)
                val (lsrc_inv,ltrg_inv) =
                    ( ``assert_mode ^(!global_mode)`` ,
                      ``assert_mode ^(!global_mode)``);

                val (left_hand_thm , tc) =   prove l  lsrc_inv ltrg_inv uargs pthms
                val tacs =  (ASSUME_TAC left_hand_thm)
                val _ = e (tacs)

                (* proof of the right part*)
                val (rsrc_inv , rtrg_inv ) =
                    if (String.isSubstring "take_undef_instr_exception"
                                           (Hol_pp.term_to_string r)) orelse
                       (String.isSubstring "take_svc_exception_part2"
                                           (Hol_pp.term_to_string r))
                    then
                        (src_inv , trg_inv)
                    else
                        ( ``assert_mode ^(!global_mode)`` ,
                          ``assert_mode ^(!global_mode)``);
                val (right_hand_thm, tc) = prove r  rsrc_inv rtrg_inv  uargs pthms;

                (* combining the left and right parts    *)
                val tacsb =
                    (if (same_const  opr ``$>>=``)
                     then
                         build_right_hand_side (src_inv, trg_inv,
                                                rsrc_inv, rtrg_inv,
                                                lsrc_inv, ltrg_inv,
                                                l , r, a, right_hand_thm,
                                                (* is_write_cpsr, *) true,uargs,
                                                List.nth(pthms,0))
                     else
                         build_right_hand_side (src_inv, trg_inv,
                                                rsrc_inv, rtrg_inv,
                                                lsrc_inv, ltrg_inv,
                                                l, r, a, right_hand_thm,
                                                (* is_write_cpsr , *)false,uargs,
                                                List.nth(pthms,0)))
                        THEN RES_TAC
                        THEN (RW_TAC (srw_ss()) [])

                val _ = e (tacsb)
                val thrm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (thrm,tacs THEN tacsb)
            end


        val prove_constT_action =
         fn (a,src_inv, trg_inv,uargs,pthms) =>
            let
                val (opr, arg) =
                    case dest_term a of
                        COMB (opr, arg) => (opr, arg)
                      |_ => Raise not_matched_pattern
                val trans_uf_thm = List.nth(pthms,1)
                val tac = ASSUME_TAC ((* SPEC (!global_mode) *) trans_uf_thm)
                                     THEN RW_TAC (srw_ss())
                                     [(SPECL [src_inv,arg,
                                              List.nth(uargs,0), List.nth(uargs,1)]
                                             (INST_TYPE [alpha |-> (type_of arg)]
                                                        constT_preserves_relation_thm))]
                val _ = e (tac)
                val proved_thm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_thm, tac)
            end
        val prove_forT_action =
         fn (a,src_inv,trg_inv, uargs,pthms) =>
            let
                val (opr, l,r,action) =
                    case strip_comb a of
                        (opr, [l,r,action]) => (opr, l,r,action)
                      |_ => Raise not_matched_pattern

                val (sub_thm , aub_tac) = prove action src_inv trg_inv uargs pthms
                val snd = get_type_inst (type_of(action), false)
                (*val (str , [fst , snd]) = dest_type (type_of(action))*)
                val r_type = get_monad_type(snd)
                val tacs = ASSUME_TAC sub_thm
                           THEN ASSUME_TAC (List.nth(pthms,0))
                           THEN ASSUME_TAC (List.nth(pthms,1))
                           THEN ASSUME_TAC (List.nth(pthms,5))
                           THEN ASSUME_TAC (SPECL [action, ``16w:word5``, (List.nth(uargs,0)), (List.nth(uargs,1))] (INST_TYPE [alpha |-> r_type]  forT_preserving_thm))
                           THEN RW_TAC (srw_ss()) [] (*changed by Oliver to enable loops *)
                val _ = e (tacs)
                val proved_thm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_thm, tacs)
            end
        val prove_condT_action =
         fn (a,src_inv,trg_inv,uargs,pthms) =>
            let val (opr, acs) = strip_comb a

                val reflex_uf_thm = List.nth(pthms,1)
                val (arg_thm,tc) = prove (List.nth(acs,1)) src_inv trg_inv uargs pthms
                val tacs =   ASSUME_TAC arg_thm
                                        THEN  ASSUME_TAC reflex_uf_thm
                                        THEN RW_TAC (srw_ss()) [condT_preserves_relation_thm]
                val _ = e (tacs)
                val proved_thm = top_thm()
                val _ = proofManagerLib.drop()
            in
                (proved_thm,tc)
            end
        val prove_case_body =
         fn (opt,body,flag,src_inv,trg_inv,uargs,pthms) =>
            let val (body_thm,body_tac) = prove body src_inv trg_inv uargs pthms
                val tacs = if (flag) then
                               CASE_TAC
                                   THEN FULL_SIMP_TAC (srw_ss()) []
                                   THEN1 (ASSUME_TAC body_thm
                                                     THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                                                     THEN (FULL_SIMP_TAC (srw_ss()) []))
                           else
                               (ASSUME_TAC body_thm
                                           THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                                           THEN (FULL_SIMP_TAC (srw_ss()) []))
                val _ = e (tacs)
            in
                (body_thm, tacs)
            end

        (* TODO: it does not return the tactic list correctly *)
        val prove_case_action =
         fn (a ,src_inv,trg_inv,uargs,pthms) =>
            let val tacs = FULL_SIMP_TAC bool_ss [preserve_relation_mmu_def] THEN CASE_TAC
                val _ = e (tacs)
                val (case_tag, case_options) = TypeBase.strip_case a
            in
                if (List.length(top_goals()) =2)
                then
                    let val _ = proofManagerLib.backup()
                        val cases = tl ((List.rev(case_options)))
                        val proved_cases =
                            map (fn (opt, body) =>
                                    prove_case_body (opt, body,true,src_inv,trg_inv,uargs,pthms)) cases
                        val (opt , body) = hd(List.rev(case_options))
                        val (body_thm,body_tac) = prove body src_inv trg_inv uargs pthms
                        val tacsb = (ASSUME_TAC body_thm
                                                THEN FULL_SIMP_TAC (srw_ss()) [preserve_relation_mmu_def]
                                                THEN (FULL_SIMP_TAC (srw_ss()) []  ORELSE METIS_TAC []))
                        val _ = e (tacsb)
                        val (proved_thm) = top_thm()
                        val _ = proofManagerLib.drop()
                    in
                        (proved_thm, tacs
                                         THEN (foldl (fn ((thm,tac),tacsc) => tacsc THEN tac) (NO_TAC) proved_cases)
                                         THEN tacsb)
                    end
                else
                    let  val proved_cases = map (fn (opt, body) =>
                                                    prove_case_body (opt, body,false,src_inv, trg_inv,uargs,pthms)) case_options
                         val (proved_thm) = top_thm()
                         val _ = proofManagerLib.drop()
                    in
                        (proved_thm, NO_TAC)
                    end
            end

        val analyze_action =
         fn (a, l , r, opr,src_inv,trg_inv,uargs,pthms) =>
            if ((same_const  opr ``$>>=``) orelse
                (same_const  opr ``$|||``))
            then
                prove_composite_action (l, r, opr ,a,src_inv,trg_inv,uargs,pthms)
            else
                if (same_const  opr ``COND``) then
                    let
                        val (opr, acs) = strip_comb a
                        val (if_part,else_part) =  (List.nth(acs,1),List.nth(acs,2)) ;
                    in
                        prove_COND_action (if_part, else_part,List.nth(acs,0),a,src_inv,trg_inv,uargs,pthms)
                    end
                else
                    if (same_const  opr ``constT``) then
                        prove_constT_action (a,src_inv,trg_inv,uargs,pthms)
                    else  if (same_const  opr ``forT``) then
                        prove_forT_action (a,src_inv,trg_inv,uargs,pthms)
                    else
                        if (TypeBase.is_case a) then
                            prove_case_action (a,src_inv,trg_inv,uargs,pthms)
                        else
                            let val _ = proof_progress ("\n\nProof of a simple action:\n "^(term_to_string l)^"\n\n")

                                val thm_exist = ((exists_theorem (current_theory())
                                                                 (term_to_string l ^ "_thm"))
                                                 orelse (exists_theorem (current_theory())
                                                                        (term_to_string l ^ "_comb_thm"))) in
                                if (thm_exist)
                                then
                                    prove_simple_action l a uargs pthms
                                else
                                    prove_condT_action (a,src_inv,trg_inv,uargs,pthms)
                            end
        val prove_abs_action =
         fn (a,src_inv,trg_inv,uargs,pthms) =>
            let
                val uf_fun = List.nth(uargs,0)
                val uy_fun = List.nth(uargs,1)
                val (a_abs,a_body) = pairLib.dest_pabs a;
                val _ =  set_goal([], ``
                                 (preserve_relation_mmu_abs ^a ^src_inv ^trg_inv ^uf_fun ^uy_fun) ``)
                val _ = e (FULL_SIMP_TAC (let_ss) (!simp_thms_list))  (*change of Oliver*)
                val (proved_a,b) = prove a_body src_inv trg_inv uargs pthms

                val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
                val unbeta_a = mk_comb (a, a_abs)
                val snd = get_type_inst (type_of(a_body) , false)
                val a_body_type = get_type_inst (snd, true)

                val proved_unbeta_lemma =
                    Tactical.prove (``(preserve_relation_mmu ^a_body ^src_inv ^trg_inv ^uf_fun ^uy_fun)=
                    (preserve_relation_mmu ^unbeta_a ^src_inv ^trg_inv ^uf_fun ^uy_fun)``,
                               (ASSUME_TAC (SPECL [a_body,``^unbeta_a``,src_inv,trg_inv,uf_fun,uy_fun]
                                                  (INST_TYPE[alpha |-> a_body_type] first_abs_lemma)))
                                   THEN (ASSUME_TAC unbeta_thm)
                                   THEN (RES_TAC))

                val proved_preserve_unbeta_a =
                    Tactical.prove (`` (preserve_relation_mmu ^unbeta_a ^src_inv ^trg_inv ^uf_fun ^uy_fun)``,
                               (ASSUME_TAC (proved_unbeta_lemma))
                                   THEN (ASSUME_TAC proved_a)
                                   THEN (FULL_SIMP_TAC (srw_ss()) []))

                val abs_type = type_of a_abs
                val (abs_args, abs_body)  = generate_uncurry_abs a
                val tacs =  (ASSUME_TAC proved_preserve_unbeta_a)
                val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a
                val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
                                THEN (ASSUME_TAC (
                                      SPECL[a, src_inv,trg_inv, uf_fun, uy_fun]
                                           (INST_TYPE [alpha |-> abs_type,
                                                       beta  |-> a_body_type] second_abs_lemma)))
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
         fn (a, opr ,uargs, pthms) =>
            let val a_name = opr
                val _ = if !Globals.interactive then
                          TextIO.print ("Do you have a theorem to prove " ^ (term_to_string (a)) ^ "  theorem? \n\n")
                        else ()
                val simp_thms = [List.nth(pthms,2),
                                 List.nth(pthms,3)]
            in
                if (same_const  opr ``readT``)
                then
                    let val tac = RW_TAC (srw_ss())
                                         (simp_thms@[preserve_relation_mmu_def,similar_def,readT_def,
                                                     equal_user_register_def,
                                                     comb_def,comb_mode_def,assert_mode_def])
                                         THEN FULL_SIMP_TAC (let_ss)
                                         (simp_thms@ [untouched_def, readT_def])
                                         THEN FULL_SIMP_TAC (srw_ss())
                                         (simp_thms@[untouched_def, readT_def])
                                         THEN (REPEAT (RW_TAC (srw_ss()) []))

                        val _ = e (tac)
                        val (proved_thm) = top_thm()
                        val _ = proofManagerLib.drop()
                    in
                        (proved_thm, tac)
                    end
                else

                    let
                        val simp_thm = find_theorem ((term_to_string (opr))^"_def")
                        val tacs =  (FULL_SIMP_TAC (srw_ss()) [simp_thm,writeT_def])
                        val _ = e (tacs)
                        val (asm,con) = top_goal()
                        val a' = get_action_from_goal (top_goal())
                        val (flag,l ,r , opr) = decompose a' src_inv trg_inv uargs
                        val (proved_a, tacb) =
                            if (flag)
                            then
                                analyze_action (a', l, r, opr,src_inv,trg_inv,uargs,pthms)
                            else
                                let
                                    val (next_proof , next_tac) = prove a' src_inv trg_inv uargs pthms
                                    val tac = RW_TAC (srw_ss()) [next_proof]
                                    val _ = e (tac)
                                    val (proved_thm) = top_thm()
                                    val _ = proofManagerLib.drop()
                                in
                                    (proved_thm, tac)
                                end
                        val tacs = tacs THEN tacb
                    in
                        (proved_a, tacs)
                    end
            end
    in
        let val (proved_thm,tacs) =
                case dest_term a of
                    (LAMB (c,b))  =>
                    prove_abs_action (a,src_inv,trg_inv,uargs,pthms)
                  | COMB (c,b) =>
                    if (same_const c ``UNCURRY``)
                    then
                        prove_abs_action (a,src_inv,trg_inv,uargs,pthms)
                    else
                        let val uf_fun = List.nth(uargs,0)
                            val uy_fun = List.nth(uargs,1)
                            val _ = proof_progress ("current action:\n\n"^(term_to_string(a)^ "\n"))
                            val  _ = (set_goal([], ``
                                              preserve_relation_mmu ^a ^src_inv ^trg_inv ^uf_fun ^uy_fun``))
                            val tac = FULL_SIMP_TAC (let_ss) [] THEN FULL_SIMP_TAC (srw_ss()) []
                            val _ = e (tac)
                            val tac = FULL_SIMP_TAC (srw_ss())
                                                    (List.drop(pthms,4)@(!simp_thms_list))
                            val tac = foldl (fn (thm,tc) => tc THEN (MP_TAC thm)) (tac)
                                            (List.drop(pthms,4));
                            val tac = tac THEN RW_TAC (srw_ss()) [];
                            val _ = e (tac);
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
                                     val (flag,l ,r , opr) = decompose a' src_inv trg_inv uargs;
                                in
                                    if (flag)
                                    then
                                        analyze_action (a' , l, r, opr,src_inv,trg_inv,uargs,pthms)
                                    else
                                        if (same_const opr ``UNCURRY``)
                                        then
                                            prove_abs_action (a',src_inv,trg_inv,uargs,pthms)
                                        else
                                            prove_simple_unproved_action (a', l,uargs,pthms)
                                end
                        end
                  | _ => (ASSUME ``T``, NO_TAC)
            val () = simp_thms_list := ([proved_thm]@(!simp_thms_list))
        in
            (proved_thm,tacs)
        end
    end;


end
