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

fun thm_of_string s =
  let val (a,b) = split_string "Theory." s in DB.fetch a b end

fun dep_of d s =
  let 
    val thm = thm_of_string s
    val l = (Dep.depidl_of o Tag.dep_of o Thm.tag) thm
  in
    mapfilter (fn x => dfind x d) l
  end

fun insert_feav d1 d2 thyl =
  let
    fun add_thy_dict thy =
      let 
        fun g thm = (Dep.depid_of o Tag.dep_of o Thm.tag) thm
        fun f (name,thm) =
          if uptodate_thm thm
          then
            let val fullname = thy ^ "Theory." ^ name in
              d1 := dadd fullname (fea_of_goal (dest_thm thm)) (!d1);
              d2 := dadd (g thm) fullname (!d2)
            end
          else ()
      in
        app f (DB.thms thy)
      end
  in
    app add_thy_dict thyl
  end

fun cached_ancfeav () = 
  let
    val thyl = ancestry (current_theory ())
    val d1 = ref (dempty String.compare)
    val d2 = ref (dempty (cpl_compare String.compare Int.compare))
    val (o1,o2) = dfind thyl (!dict_cache) handle _ =>
      (
      print_endline "Initialization...";
      insert_feav d1 d2 thyl;
      dict_cache := dadd thyl (!d1,!d2) (!dict_cache);
      print_endline 
        ("Caching " ^ int_to_string (dlength (!d1)) ^ " feature vectors");
      (!d1,!d2)
      )
  in
    (o1,o2)
  end
 
fun insert_curfeav (o1,o2) =
  let 
    val d1 = ref o1
    val d2 = ref o2
    val _ = insert_feav d1 d2 [current_theory ()]
    val thmfeav = dlist (!d1)
    val thmfeavdep = 
      map (fn (name,fea) => (name, fea, dep_of (!d2) name)) thmfeav
  in
    thmfeavdep
  end

fun select_premises preddir n thmfeavdep term =
  let 
    val _ = clean_dir preddir
    val goalfea = fea_of_goal ([],term)
    val l = thmknn_ext preddir n thmfeavdep goalfea
  in
    map (split_string "Theory.") l
  end

(*---------------------------------------------------------------------------
   Export to TPTP THF
 ----------------------------------------------------------------------------*)

fun pred_filter pred thy ((name,_),_)=
  let val thypred = map snd (filter (fn x => fst x = thy) pred) in
    mem name thypred  
  end
 
fun export_problem dir premises cj =
  let
    val ct   = current_theory ()
    val thyl = ct :: Theory.ancestry ct 
  in    
    clean_dir dir;
    (* write loaded theories *)
    write_thyl dir (pred_filter premises) thyl;
    (* write the conjecture in thf format *)
    write_conjecture (dir ^ "/conjecture.fof") cj;
    (* write the dependencies between theories *)
    write_thydep (dir ^ "/thydep.dep") thyl
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
       "-thydep", probbdir ^ "/thydep.dep",">","/dev/null","2>","/dev/null"]
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
   For THF experiments with Satallax.
   Example: 
   reproving_thf Satallax "arithmetic" (hd (DB.theorems "arithmetic"));
   need to change print_vartype and others.
 ----------------------------------------------------------------------------*)

fun reproving_thf thy (name,thm) =
  let
    val probdir = probdir_of Satallax
    val provdir = provdir_of Satallax
    val _ = print ("  " ^ name ^ "\n")
    val cj = list_mk_imp (dest_thm thm) 
    val thyl = thy :: Theory.ancestry thy
    val (b,pred) = depl_as_pred thm
    val newname = 
      if (not b) 
        then "broken_dependencies____" ^ thy ^ "____" ^ name 
        else thy ^ "____" ^ name
    val thf_file = provdir ^ "/thf_in"
    val out_dir = hh_dir ^ "/thf_problems/" ^ thy
    val out_file = out_dir ^ "/" ^ quote newname
  in    
    OS.FileSys.mkDir (hh_dir ^ "/thf_problems") handle _ => ();
    OS.FileSys.mkDir out_dir handle _ => ();
    clean_dir probdir;
    (* write loaded theories *)
    write_thyl probdir (pred_filter pred) thyl;
    (* write the conjecture in tt format *)
    write_conjecture (probdir ^ "/conjecture.fof") cj;
    (* write the dependencies between theories *)
    write_thydep (probdir ^ "/thydep.dep") thyl;
    (* translate to thf_in *)
    ignore (translate_thf probdir provdir);
    (* copying the produced file *)
    ignore (cmd_in_dir hh_dir ("mv " ^ thf_file ^ " " ^ out_file))
  end

fun reproving_thf_thyl thyl =
  let fun f thy = 
    (print (thy ^ "\n"); app (reproving_thf thy) (DB.theorems thy))
  in
    app f thyl
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

fun hh_atp preddir probdir provdir n atp t cj =
  let
    val thmfeavdep = insert_curfeav (cached_ancfeav ())
    val premises = select_premises preddir n thmfeavdep cj
    val _ = export_problem probdir premises cj
    val _ = translate_fof probdir provdir
    val _ = launch_atp provdir atp t
  in
    reconstruct_dir provdir cj
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

fun holyhammer term =
  let
    val thmfeavdep = insert_curfeav (cached_ancfeav ())
    val premises32 = select_premises hhs_predict_dir 32 thmfeavdep term
    val premises128 = select_premises hhs_predict_dir 128 thmfeavdep term
    val _ = export_problem (probdir_of Eprover) premises128 term
    val _ = translate_fof (probdir_of Eprover) (provdir_of Eprover)
    val _ = export_problem (probdir_of Z3) premises32 term
    val _ = translate_fof (probdir_of Z3) (provdir_of Z3)
    val _ = launch_parallel (!timeout_glob)
  in
    reconstruct_atp Eprover term 
    handle _ => reconstruct_atp Z3 term
  end

fun hh_tac goal = (holyhammer (list_mk_imp goal)) goal

fun hh_stac pid thmfeavdep t goal = 
  let
    val ns = int_to_string pid
    val term = list_mk_imp goal
    val preddir = hhs_predict_dir ^ "_" ^ ns
    val premises = select_premises preddir 128 thmfeavdep term
    val probdir = hh_dir ^ "/problem_" ^ ns
    val _ = export_problem probdir premises term
    val provdir = provbin_dir ^ "/prover_" ^ ns
    val _ = translate_fof probdir provdir
    val _ = launch_atp provdir Eprover t
  in
    reconstruct_dir_stac provdir term
  end



end
