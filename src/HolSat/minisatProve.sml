
structure minisatProve :> minisatProve =
struct

local

open Lib boolLib Globals Parse Term Type Thm Drule Conv Feedback FileSys
open dimacsTools satTools SatSolvers satCommonTools minisatParse satConfig
     dpll def_cnf


in

exception SAT_cex of thm

val mk_sat_oracle_thm = mk_oracle_thm "HolSatLib";

val sat_warn = ref true (* control interactive warnings *)
val sat_limit = ref 100
  (* if > sat_limit clauses then interactive warning if using SML prover *)
val _ = register_btrace ("HolSatLib_warn",sat_warn);

fun warn ss =
    if !Globals.interactive andalso !sat_warn
    then print ("\nHolSat WARNING: "^ss^
                "\nTo turn off this warning, type: \
                \set_trace \"HolSatLib_warn\" 0; RET\n\n")
    else ()

fun replay_proof is_proved sva nr in_name solver vc clauseth lfn ntm proof =
    if is_proved then
        ((case getSolverPostExe solver of (* post-process proof, if required *)
             SOME post_exe => let
               val (fin,fout) = (in_name,in_name^"."^(getSolverName solver))
             in
               ignore(Systeml.system_ps
                        (getSolverPostRun solver post_exe (fin,fout)))
             end
           | NONE => ());
        (case replayProof sva nr in_name solver vc clauseth lfn proof of
             SOME th => th
           | NONE => (warn "Proof replay failed. Using internal prover.";
                      DPLL_TAUT (dest_neg ntm)))) (*triv prob/unknown err*)
    else mk_sat_oracle_thm([ntm],F)

local
    fun transform_model cnfv lfn model =
        let val model2 =
            if isSome cnfv then
                mapfilter (fn l => let val x = hd(free_vars l)
                                       val y = rbapply lfn x
                                   in if is_var y then subst [x|->y] l
                                      else failwith"" end) model
            else model
        in model2 end
in
fun invoke_solver solver lfn ntm clauseth cnfv vc is_proved svm sva in_name =
    let val nr = Array.length clauseth
    in
      if access(getSolverExe solver,[A_EXEC]) then
        let
          val answer = invokeSat solver T (SOME vc) (SOME nr) svm sva in_name
        in case answer of
              SOME model => (* returns |- model ==> ~t *)
              let val model' = transform_model cnfv lfn model
              in if is_proved then satCheck model' ntm
                 else mk_sat_oracle_thm([],mk_imp(list_mk_conj model',ntm)) end
            | NONE    => (* returns ~t |- F *)
                replay_proof is_proved sva nr in_name solver vc clauseth
                             lfn ntm NONE
        end
      else (* do not have execute access to solver binary, or it doesn't exist*)
        (if nr > !sat_limit then
           warn "SAT solver not found. Using slow internal prover."
         else ();
         DPLL_TAUT (dest_neg ntm))
    end
end

(* cleanup temp files. this won't work fully if we cannot delete files
   generated by the SAT solver *)
fun clean_delete s = OS.FileSys.remove s handle Interrupt => raise Interrupt
                                              | e => ()
(* then raise exception if countermodel was found,
   else deduce input term from solver's result *)
fun finalise solver infile is_cnf th tmpname in_name =
    let val solver_name = getSolverName solver
        val _ = if isSome infile then ()
                else
                  app clean_delete [
                    "resolve_trace",                 (* in case using ZChaff *)
                    in_name,                                          (* CNF *)
                    tmpname,(* tmpfile(created by Poly/ML, but not MoscowML) *)
                    in_name^"."^solver_name,                (* result/status *)
                    in_name^"."^solver_name^".proof",               (* proof *)
                    in_name^"."^solver_name^".stats"
                  ]
        val res =
            if is_imp(concl th)
            then raise (SAT_cex th)
            else
                if is_cnf
                then (NOT_INTRO(DISCH_ALL th))
                else CONV_RULE NOT_NOT_CONV (NOT_INTRO(DISCH_ALL th))
     in res end

(* convert input to term to CNF and write out DIMACS file               *)
(* if infile is SOME name, then assume name.cnf exists and is_cnf=true  *)
(* if is_cnf, then assume tm \equiv ~s where s is in CNF                *)
(* if CNF conversion found true or false, return theorem directly       *)
exception initexp of thm;
fun initialise infile is_cnf tm =
    let val (cnfv,vc,svm,sva,tmpname,in_name,ntm,lfn,clauseth) =
            if isSome infile
            then let val fname = valOf infile
                     val (tm,svm,sva) = genReadDimacs fname
                     val (cnfv,vc,lfn,clauseth) = to_cnf is_cnf (mk_neg tm)
                 in (cnfv,vc,svm,sva,"",fname,mk_neg tm,lfn,clauseth) end
            else let val (cnfv,vc,lfn,clauseth) = to_cnf is_cnf (mk_neg tm)
                     val (tmpname,cnfname,sva,svm) =
                         generateDimacs (SOME vc) tm (SOME clauseth)
                                        (SOME (Array.length clauseth))
                 in (cnfv,vc,svm,sva,tmpname,cnfname,mk_neg tm,lfn,clauseth) end
    in if vc=0 then
         (* no vars: all 'presimp'-ified conjuncts were either T or F *)
           let val th0 = presimp_conv (dest_neg ntm)
           in if is_F (rhs (concl th0)) then raise SAT_cex (EQF_ELIM th0)
              else raise initexp (EQT_ELIM th0)
           end
       else
         (cnfv,vc,svm,sva,tmpname,in_name,ntm,lfn,clauseth)
    end

val dbg_show_input = ref false;

fun GEN_SAT conf = (* single entry point into HolSatLib *)
    let val (tm,solver,infile,proof,is_cnf,is_proved) = dest_config conf
        val _ = if !dbg_show_input then (print "\n"; print_term tm; print "\n")
                else ()
        val (cnfv,vc,svm,sva,tmpname,in_name,ntm,lfn,clauseth) =
            initialise infile is_cnf tm
        val th = if isSome proof
                 then replay_proof is_proved sva (Array.length clauseth) in_name
                                   solver vc clauseth lfn ntm proof
                 else invoke_solver solver lfn ntm clauseth cnfv vc
                                    is_proved svm sva in_name
        val res = finalise solver infile is_cnf th tmpname in_name
    in res end
    handle initexp th => th

(* default config invokes pre-installed MiniSat 1.14p *)
fun SAT_PROVE tm = GEN_SAT (set_term tm base_config)
fun SAT_ORACLE tm =
    GEN_SAT ((set_term tm o set_flag_is_proved false) base_config)

(* same functionality for ZChaff, if installed by user *)
val zchaff_config = set_solver zchaff base_config
fun ZSAT_PROVE tm = GEN_SAT (set_term tm zchaff_config)
fun ZSAT_ORACLE tm =
    GEN_SAT ((set_term tm o set_flag_is_proved false) zchaff_config)

end
end
