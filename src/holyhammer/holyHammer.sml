(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Export types, constants, predicted theorems to        *)
(*                 the holyHammer framework. The lemmas                  *)
(*                 found by the provers help Metis to reconstruct the    *)
(*                 proof.                                                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib hhWriter hhReconstruct tttTools tttExec tttFeature tttPredict

val ERR = mk_HOL_ERR "holyHammer"

fun cmd_in_dir dir cmd = OS.Process.system ("cd " ^ dir ^ "; " ^ cmd)

(*---------------------------------------------------------------------------
   Caching of the dictionnaries. Makes subsequent call of holyhammer in
   the same theory faster. Not to be used for parallel calls.
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
val hh_bin_dir = hh_dir ^ "/hh"
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

fun add_fea dict (name,thm) =
  let val g = dest_thm thm in
    if not (dmem g (!dict)) andalso
       uptodate_thm thm
    then dict := dadd g (name, fea_of_goal g) (!dict)
    else ()
  end

fun insert_feav thmdict thyl =
  let
    val dict = ref thmdict
    fun f_thy thy =
      let fun f (name,thm) =
        add_fea dict ((thy ^ "Theory." ^ name), thm)
      in
        app f (DB.thms thy)
      end
  in
    app f_thy thyl;
    !dict
  end

fun cached_ancfeav () =
  let
    val thyl = ancestry (current_theory ())
    val thmdict = dempty goal_compare
  in
    dfind thyl (!dict_cache) handle _ =>
      let 
        val newdict = insert_feav thmdict thyl 
      in
        dict_cache := dadd thyl newdict (!dict_cache);
        print_endline ("Loading " ^ int_to_string (dlength newdict) ^
           " theorems");
        newdict
      end
  end

fun insert_namespace thmdict =
  let
    val dict = ref thmdict
    fun f (x,y) = (namespace_tag ^ "Theory." ^ x, y)
    val l1 = hide_out namespace_thms ()
    val l2 = map f l1
  in
    app (add_fea dict) l2;
    (!dict)
  end

fun create_symweight_feav thmdict =
  let
    val l = dlist thmdict
    val feav = map snd l
    val symweight = learn_tfidf feav
    fun f (g,(name,fea)) = (name,(g,fea))
    val revdict = dnew String.compare (map f l)
  in
    (symweight,feav,revdict)
  end

fun update_thmdata () =
  let
    val dict0 = cached_ancfeav ()
    val dict1 = insert_feav dict0 [current_theory ()]
    val dict2 = insert_namespace dict1
  in
    create_symweight_feav dict2
  end

(*---------------------------------------------------------------------------
   Export to TT format
 ----------------------------------------------------------------------------*)

fun pred_filter pred thy ((name,_),_) =
  let val thypred = map snd (filter (fn x => fst x = thy) pred) in
    mem name thypred
  end

fun in_namespace s = fst (split_string "Theory." s) = namespace_tag

fun export_problem probdir premises cj =
  let
    val premises' = map (split_string "Theory.") premises
    (* val _ = print_endline (String.concatWith " " (first_n 10 premises)) *)
    val nsthml1 = filter in_namespace premises
    fun f s = case thm_of_sml (snd (split_string "Theory." s)) of
        SOME (_,thm) => SOME (s,thm)
      | NONE => NONE
    val nsthml2 = hide_out (List.mapPartial f) nsthml1
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct
  in
    clean_dir probdir;
    write_problem probdir (pred_filter premises') nsthml2 thyl cj;
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

fun reconstruct_dir dir goal = reconstruct (status_dir dir, out_dir dir) goal
fun reconstruct_atp atp goal = reconstruct (status_of atp, out_of atp) goal

fun reconstruct_dir_stac dir goal =
  reconstruct_stac (status_dir dir, out_dir dir) goal

fun get_lemmas_atp atp = get_lemmas (status_of atp, out_of atp)

(*---------------------------------------------------------------------------
   Performs all previous steps with (experimentally) the best parameters.
   Todo: replace by PolyML.fork for faster termination of asynchronous calls.
 ----------------------------------------------------------------------------*)

fun launch_parallel t =
  let val cmd =
    String.concatWith " & "
    ["sh eprover.sh " ^ int_to_string t ^ " " ^ provdir_of Eprover,
     "sh z3.sh " ^ int_to_string t ^ " " ^ provdir_of Z3,
     "wait"]
  in
    cmd_in_dir provbin_dir cmd
  end

(* todo:
     translate when the prover's binary exists.
     terminate when the first prover finds a proof. *)
fun holyhammer_goal goal =
  let
    val term = list_mk_imp goal
    val (symweight,feav,revdict) = update_thmdata ()
    val premises = thmknn_wdep (symweight,feav,revdict) 128  (fea_of_goal goal)
    val _ = export_problem (probdir_of Eprover) premises term
    val _ = translate_fof (probdir_of Eprover) (provdir_of Eprover)
    val _ = export_problem (probdir_of Z3) (first_n 32 premises) term
    val _ = translate_fof (probdir_of Z3) (provdir_of Z3)
    val _ = launch_parallel (!timeout_glob)
  in
    reconstruct_atp Eprover goal
    handle _ => reconstruct_atp Z3 goal
  end

fun holyhammer term = holyhammer_goal ([],term)

fun hh goal = (holyhammer_goal goal) goal

fun hh_stac pid (symweight,feav,revdict) t goal =
  let
    val term = list_mk_imp goal
    val ns = int_to_string pid
    val premises = thmknn_wdep (symweight,feav,revdict) 128 (fea_of_goal goal)
    val probdir = hh_dir ^ "/problem_" ^ ns
    val _ = export_problem probdir premises term
    val provdir = provbin_dir ^ "/prover_" ^ ns
    val _ = translate_fof probdir provdir
    val _ = rmDir_rec probdir
    val _ = launch_atp provdir Eprover t
    val r = reconstruct_dir_stac provdir goal
    val _ = rmDir_rec provdir
  in
    r
  end

end
