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
   the same theory faster. Not to be used for paralell calls.
 ----------------------------------------------------------------------------*)

val dict_cache = ref (dempty (list_compare String.compare))
fun clean_cache () = dict_cache := dempty (list_compare String.compare)

(*---------------------------------------------------------------------------
   Settings
 ----------------------------------------------------------------------------*)

datatype prover = Eprover | Z3 | Satallax
fun name_of atp = case atp of
    Eprover => "eprover"
  | Z3 => "z3"
  | Satallax => "satallax"

val timeout_glob = ref 5
fun set_timeout n = timeout_glob := n

fun set_minimization b = minimize_flag := b

(*---------------------------------------------------------------------------
   Directories
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

val hh_dir = HOLDIR ^ "/src/holyhammer"
val hh_bin_dir = HOLDIR ^ "/src/holyhammer/hh"
val provbin_dir = hh_dir ^ "/provers"

fun probdir_of atp = hh_dir ^ "/problem_" ^ name_of atp
fun provdir_of atp = provbin_dir ^ "/" ^ name_of atp ^ "_files"

fun out_of atp = provdir_of atp ^ "/out"
fun status_of atp = provdir_of atp ^ "/status"

fun out_dir dir = dir ^ "/out"
fun status_dir dir = dir ^ "/status"


(* ----------------------------------------------------------------------
   Predicting theorems
   ---------------------------------------------------------------------- *)

fun insert_feav thmdict thyl =
  let
    fun add_thmdict thy =
      let 
        fun f (name,thm) =
          if uptodate_thm thm then
            let val fullname = thy ^ "Theory." ^ name in
              thmdict := dadd fullname (fea_of_goal (dest_thm thm)) (!thmdict)
            end
          else ()
      in
        app f (DB.thms thy)
      end
  in
    app add_thmdict thyl
  end

fun cached_ancfeav () = 
  let
    val thyl = ancestry (current_theory ())
    val thmdictref = ref (dempty String.compare)
  in
    dfind thyl (!dict_cache) handle _ =>
      (
      print_endline "Initialization...";
      insert_feav thmdictref thyl;
      dict_cache := dadd thyl (!thmdictref) (!dict_cache);
      print_endline ("Caching " ^ int_to_string (dlength (!thmdictref)) ^ " feature vectors");
      !thmdictref
      )
  end
 
fun insert_curfeav thmdict =
  let 
    val thmdictref = ref thmdict
    val _ = insert_feav thmdictref [current_theory ()] 
    val feav = dlist (!thmdictref)
    val symweight = learn_tfidf feav
  in
    (symweight,feav)
  end




(*---------------------------------------------------------------------------
   Export to TPTP THF
 ----------------------------------------------------------------------------*)

fun pred_filter pred thy ((name,_),_)=
  let val thypred = map snd (filter (fn x => fst x = thy) pred) in
    mem name thypred  
  end
 
fun export_problem probdir premises cj =
  let
    val premises' = map (split_string "Theory.") premises
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct 
  in    
    clean_dir probdir;
    write_problem probdir (pred_filter premises') thyl cj;
    write_thydep (probdir ^ "/thydep.dep") thyl
  end

fun export_theories dir thyl =
  (
  clean_dir dir;
  write_thyl dir (fn thy => (fn thma => true)) thyl;
  write_thydep (dir ^ "/thydep.dep") thyl
  )

(*---------------------------------------------------------------------------
   Translate from higher-order to first order
 ----------------------------------------------------------------------------*)

fun translate_bin bin probbdir provdir =
  let 
    val _ = clean_dir provdir
    val cmd = String.concatWith " "
      [bin,
       "all","0",probbdir,
       probbdir ^ "/conjecture.fof",
       "conjecture", provdir, 
       "-thydep", probbdir ^ "/thydep.dep",">","/dev/null"]
  in
    cmd_in_dir hh_dir cmd
  end

fun translate_fof dir_in dir_out = 
  translate_bin (hh_bin_dir ^ "/hh") dir_in dir_out
fun translate_thf dir_in dir_out = 
  translate_bin (hh_bin_dir ^ "/hh_thf") dir_in dir_out

fun launch_atp dir atp tim =
  let val cmd = case atp of
      Eprover => 
      "sh eprover.sh " ^ int_to_string tim ^ " " ^ dir ^
      " > /dev/null 2> /dev/null"
    | Z3      => "sh z3.sh " ^ int_to_string tim ^ " " ^ dir ^
      " > /dev/null 2> /dev/null"
    | _       => raise ERR "launch_atp" "atp not supported"
  in
    cmd_in_dir provbin_dir cmd
  end

(*---------------------------------------------------------------------------
   Read theorems needed for the proof and replay the proof with Metis.
 ----------------------------------------------------------------------------*)

fun reconstruct_dir dir cj = reconstruct (status_dir dir, out_dir dir) cj
fun reconstruct_atp atp cj = reconstruct (status_of atp, out_of atp) cj

fun reconstruct_dir_stac dir cj =
  reconstruct_stac (status_dir dir, out_dir dir) cj

fun get_lemmas_atp atp = get_lemmas (status_of atp, out_of atp)

(*---------------------------------------------------------------------------
   Performs all previous steps with (experimentally) the best parameters.
 ----------------------------------------------------------------------------*)

fun hh_atp preddir probdir provdir n atp t term =
  let
    val (symweight,feav) = insert_curfeav (cached_ancfeav ())
    val premises = thmknn_wdep symweight 128 feav (fea_of_goal ([],term))
    val _ = export_problem probdir premises term
    val _ = translate_fof probdir provdir
    val _ = launch_atp provdir atp t
  in
    reconstruct_dir provdir term
  end

fun launch_parallel t =
  let val cmd =
    String.concatWith " & "
    ["sh eprover.sh " ^ int_to_string t ^ " " ^ provdir_of Eprover,
     "sh z3.sh " ^ int_to_string t ^ " " ^ provdir_of Z3,
     "wait"]
  in
    cmd_in_dir provbin_dir cmd
  end

fun holyhammer_goal goal =
  let
    val term = list_mk_imp goal
    val (symweight,feav) = insert_curfeav (cached_ancfeav ())
    val premises = thmknn_wdep symweight 128 feav (fea_of_goal goal)
    val _ = export_problem (probdir_of Eprover) premises term
    val _ = translate_fof (probdir_of Eprover) (provdir_of Eprover)
    val _ = export_problem (probdir_of Z3) (first_n 32 premises) term
    val _ = translate_fof (probdir_of Z3) (provdir_of Z3)
    val _ = launch_parallel (!timeout_glob)
  in
    reconstruct_atp Eprover term 
    handle _ => reconstruct_atp Z3 term
  end

fun holyhammer term = holyhammer_goal ([],term)

fun hh_tac goal = (holyhammer_goal goal) goal

fun hh_stac pid (symweight,feav) t goal = 
  let
    val term = list_mk_imp goal
    val ns = int_to_string pid
    val term = list_mk_imp goal
    val premises = thmknn_wdep symweight 128 feav (fea_of_goal goal)
    val probdir = hh_dir ^ "/problem_" ^ ns
    val _ = export_problem probdir premises term
    val provdir = provbin_dir ^ "/prover_" ^ ns
    val _ = translate_fof probdir provdir
    val _ = launch_atp provdir Eprover t
  in
    reconstruct_dir_stac provdir term
  end



end
