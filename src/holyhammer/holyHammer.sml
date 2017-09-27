(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Export types, constants, predicted theorems to        *)
(*                 the holyHammer framework which performs premise       *)
(*                 selection and calls to external provers. The lemmas   *)
(*                 found by the provers help Metis to reconstruct the    *)
(*                 proof.                                                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)


structure holyHammer :> holyHammer =
struct

open HolKernel boolLib hhWriter hhReconstruct hhsTools hhsFeature hhsPredict

val ERR = mk_HOL_ERR "holyHammer"

fun cmd_in_dir dir cmd = OS.Process.system ("cd " ^ dir ^ "; " ^ cmd)

(*---------------------------------------------------------------------------
   Caching of the dictionnaries. Makes subsequent call of holyhammer in
   the same theory faster.
 ----------------------------------------------------------------------------*)

val dict_cache = ref (dempty (list_compare String.compare))
fun clean_cache () = dict_cache := dempty (list_compare String.compare)

(*---------------------------------------------------------------------------
   Settings
 ----------------------------------------------------------------------------*)

datatype prover = Eprover | Z3
fun name_of atp = case atp of
    Eprover => "eprover"
  | Z3 => "z3"

datatype predictor = KNN | Mepo
val predictor_glob = ref (thmknn_ext)
fun set_predictor pred = case pred of
    KNN  => predictor_glob := thmknn_ext
  | Mepo => predictor_glob := thmmepo_ext

val timeout_glob = ref 5
fun set_timeout n = timeout_glob := n

fun set_minimization b = minimize_flag := b

(*---------------------------------------------------------------------------
   Directories
 ----------------------------------------------------------------------------*)

val hh_dir = HOLDIR ^ "/src/holyhammer"
val hh_bin_dir = HOLDIR ^ "/src/holyhammer/hh"
val provers_dir = hh_dir ^ "/provers"
fun thy_dir_of atp = hh_dir ^ "/theories" ^ "_" ^ name_of atp

fun prover_files atp = 
  provers_dir ^"/" ^ name_of atp ^ "_files"

fun out_of_prover atp = 
  provers_dir ^ "/" ^ name_of atp ^ "_files" ^ "/" ^ name_of  atp ^ "_out"

fun status_of_prover atp =
  provers_dir ^ "/" ^ name_of atp ^ "_files" ^ "/" ^ name_of atp ^ "_status"

(* ----------------------------------------------------------------------
   Predicting theorems
   ---------------------------------------------------------------------- *)

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

fun dep_of d s =
  let 
    val thm = thm_of_string s
    val l = (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
  in
    mapfilter (fn x => dfind x d) l
  end

fun init_predictions d1 d2 thyl =
  let
    fun add_thy_dict thy =
      let 
        fun g thm = (Dep.depid_of o Tag.dep_of o Thm.tag) thm
        fun f (name,thm) =
          let val fullname = thy ^ "Theory." ^ name in
            d1 := dadd fullname (fea_of_goal (dest_thm thm)) (!d1);
            d2 := dadd (g thm) fullname (!d2)
          end
      in
        app f (DB.thms thy)
      end
  in
    app add_thy_dict thyl
  end

fun select_premises n term = 
  let
    val goalfea = fea_of_goal ([],term)
    val cthy = current_theory ()
    val thyl = ancestry cthy
    val d1 = ref (dempty String.compare)
    val d2 = ref (dempty (cpl_compare String.compare Int.compare))
    val (o1,o2) = dfind thyl (!dict_cache) handle _ =>
      (
      print_endline "Initialization...";
      init_predictions d1 d2 thyl;
      dict_cache := dadd thyl (!d1,!d2) (!dict_cache);
      print_endline 
        ("Caching " ^ int_to_string (dlength (!d1)) ^ " feature vectors");
      (!d1,!d2)
      )
    val _ = (d1 := o1; d2 := o2)
    val _ = init_predictions d1 d2 [cthy]
    val thmfeav = dlist (!d1)
    val thmfeavdep = 
      map (fn (name,fea) => (name, fea, dep_of (!d2) name)) thmfeav
  in
    map (split_string "Theory.") ((!predictor_glob) n thmfeavdep goalfea)
  end

(*---------------------------------------------------------------------------
   Export to TPTP THF
 ----------------------------------------------------------------------------*)

fun all_files dir =
  let 
    val stream = OS.FileSys.openDir dir
    fun loop acc stream = 
      case OS.FileSys.readDir stream of
        NONE => acc
      | SOME s => loop (s :: acc) stream  
    val l = loop [] stream
  in
    OS.FileSys.closeDir stream;
    l 
  end

fun clean_dir dir =
  let 
    val _ = OS.FileSys.mkDir dir handle _ => ()
    val l0 = all_files dir 
    val l1 = map (fn x => OS.Path.concat (dir,x)) l0
  in
    app OS.FileSys.remove l1
  end
  
fun export_problem atp premises cj =
  let
    val thy_dir = thy_dir_of atp
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct 
  in    
    clean_dir thy_dir;
    (* write loaded theories *)
    write_thyl thy_dir premises thyl;
    (* write the conjecture in thf format *)
    write_conjecture (thy_dir ^ "/conjecture.fof") cj;
    (* write the dependencies between theories *)
    write_thydep (thy_dir ^ "/thydep.dep") thyl
  end

(*---------------------------------------------------------------------------
   Translate from higher-order to first order
 ----------------------------------------------------------------------------*)

fun translate_atp atp =
  let 
    val thy_dir = thy_dir_of atp
    val target_dir = prover_files atp
    val _ = clean_dir target_dir
    val cmd = String.concatWith " "
      [hh_bin_dir ^ "/hh",
       "all","0",thy_dir,
       thy_dir ^ "/conjecture.fof",
       "conjecture", target_dir, 
       "-thydep", thy_dir ^ "/thydep.dep",">","/dev/null"]
  in
    cmd_in_dir hh_dir cmd
  end

fun launch_atp atp tim =
  let val cmd = case atp of
      Eprover => "sh eprover.sh " ^ int_to_string tim
    | Z3      => "sh z3.sh " ^ int_to_string tim
  in
    cmd_in_dir provers_dir cmd
  end

fun launch_parallel tim =
  let val cmd =
    String.concatWith " & "
    ["sh eprover.sh " ^ int_to_string tim,
     "sh z3.sh " ^ int_to_string tim,
     "wait"]
  in
    cmd_in_dir provers_dir cmd
  end

(*---------------------------------------------------------------------------
   Read theorems needed for the proof and replay the proof with Metis.
 ----------------------------------------------------------------------------*)

fun reconstruct_atp atp cj =
  reconstruct (status_of_prover atp, out_of_prover atp) cj

fun reconstruct_atp_stac atp cj =
  reconstruct_stac (status_of_prover atp, out_of_prover atp) cj

fun get_lemmas_atp atp = get_lemmas
 (status_of_prover atp, out_of_prover atp)


(*---------------------------------------------------------------------------
   Performs all previous steps with (experimentally) the best parameters.
 ----------------------------------------------------------------------------*)

fun hh_atp atp timeout n term =
  let
    val premises = select_premises n term
    val _ = export_problem atp premises term
    val _ = translate_atp atp
    val _ = launch_atp atp timeout
  in
    reconstruct_atp atp term
  end

fun hh_eprover term = hh_atp Eprover (!timeout_glob) 128 term

fun hh_z3 term = hh_atp Z3 (!timeout_glob) 32 term

fun holyhammer term = 
  let
    val premises32 = select_premises 32 term
    val premises128 = select_premises 128 term
    val _ = export_problem Eprover premises128 term
    val _ = translate_atp Eprover
    val _ = export_problem Z3 premises32 term
    val _ = translate_atp Z3
    val _ = launch_parallel (!timeout_glob)
  in
    reconstruct_atp Eprover term 
    handle _ => reconstruct_atp Z3 term
  end

fun hh_stac goal = 
  let
    val term = list_mk_imp goal
    val premises32 = select_premises 32 term
    val premises128 = select_premises 128 term
    val _ = export_problem Eprover premises128 term
    val _ = translate_atp Eprover
    val _ = export_problem Z3 premises32 term
    val _ = translate_atp Z3
    val _ = launch_parallel (!timeout_glob)
  in
    reconstruct_atp_stac Eprover term 
    handle _ => reconstruct_atp_stac Z3 term
  end

fun hh_tac goal = (holyhammer (list_mk_imp goal)) goal

end
