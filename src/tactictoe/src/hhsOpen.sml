(* =========================================================================  *)
(* FILE          : hhsOpen.sml                                                *)
(* DESCRIPTION   : Find string representation of SML values and structures in *)
(* a signature.                                                               *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsOpen :> hhsOpen =
struct

open HolKernel boolLib hhsTools

val ERR = mk_HOL_ERR "hhsOpen"

(* ---------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)

val cthy_unfold_glob = ref "scratch"

val hhs_unfold_dir = tactictoe_dir ^ "/unfold_log"
val hhs_scripts_dir = tactictoe_dir ^ "/scripts"
fun debug_unfold s = 
  append_endline (hhs_unfold_dir ^ "/" ^ !cthy_unfold_glob) s

(* ---------------------------------------------------------------------------
   Running a command on a file in a directory
   -------------------------------------------------------------------------- *)

fun cmd_in_dir dir cmd =
  ignore (OS.Process.system ("cd " ^ dir ^ ";" ^ cmd))

fun run_cmd cmd = ignore (OS.Process.system cmd)

(* ---------------------------------------------------------------------------
   Creating holmakefile for a file from existing holmakefile in dirorg.
   -------------------------------------------------------------------------- *)

fun first_mfile dirorg diruo =
  let
    val mfile = dirorg ^ "/Holmakefile"
    val temp = diruo ^ "/temp"
    val newmfile = diruo ^ "/Holmakefile"
    val cmd = "sed -e :a -e '/\\\\$/N; s/\\\\\\n//; ta' "
      ^ mfile ^ " > " ^ newmfile
  in
    if FileSys.access (mfile, [])
    then 
      (ignore (OS.Process.system cmd); SOME newmfile)
    else 
      (debug_unfold ("Warning: " ^ dirorg ^ " has no Holmakefile"); 
       NONE)
  end
  
fun new_mfile prefix alls mfile =
  let 
    val l0 = readl mfile
    fun is_blank c = c = #" " orelse c = #"\n"
    fun is_fs c = c = #"/"
    fun is_include s = 
      let val sl = String.tokens is_blank s in
        hd sl = "INCLUDES" handle Empty => false
      end
  in
    case List.find is_include l0 of 
      NONE => () 
    | SOME includes =>
      let
        val (_,dirl) = split_sl "=" (String.tokens is_blank includes)
        fun add_prefix s = 
          if ((String.sub (s,0) = #"$" orelse String.sub (s,0) = #"/") 
               handle _ => false)
          then s
          else prefix ^ s
        val _ = FileSys.remove mfile
        val newincludes =
          String.concatWith " " (["INCLUDES","="] @ (map add_prefix dirl))
        val newall = "all: code.uo"
      in
        writel mfile [newincludes,alls]
      end
  end

fun code_mfile dirorg diruo = case first_mfile dirorg diruo of
    NONE => ()
  | SOME mfile => new_mfile "../../" "all: code.uo" mfile

fun ttt_mfile dirorg diruo = case first_mfile dirorg diruo of
    NONE => ()
  | SOME mfile => new_mfile "../" "all: ttt.uo" mfile

(* ---------------------------------------------------------------------------
   Running holmake on a directory
   -------------------------------------------------------------------------- *)

fun run_holmake dir = cmd_in_dir dir (HOLDIR ^ "/bin/Holmake")

(* ---------------------------------------------------------------------------
   Running buildheap on a file (full path necessary)
   -------------------------------------------------------------------------- *)

fun run_hol0 file =
  let
    val buildheap = HOLDIR ^ "/bin/buildheap"
    val state0 = "-b " ^ HOLDIR ^ "/bin/hol.state0"
    val gc = "--gcthreads=1"
    val hol0 = String.concatWith " " [buildheap,gc,state0,file]
  in
    run_cmd hol0 
  end

fun run_hol file =
  let
    val buildheap = HOLDIR ^ "/bin/buildheap"
    val gc = "--gcthreads=1"
    val hol = String.concatWith " " [buildheap,gc,file]
  in
    run_cmd hol
  end

(* ---------------------------------------------------------------------------
   Exporting elements of a structure (values + substructures)
   -------------------------------------------------------------------------- *)

fun top_struct s = hd (String.tokens (fn x => x = #".") s)
  
fun part_val l =
  let
    open PolyML.NameSpace.Values
    val (constructors,l0) = partition (fn x => isConstructor (snd x)) l
    val (exceptions,l1) = partition (fn x => isException (snd x)) l0 
  in
    (l1,constructors,exceptions)
  end

fun test_struct s x = fst x <> top_struct s

fun tactictoe_cleanstruct s = 
  let val l = filter (test_struct s) (#allStruct PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetStructure (map fst l)
  end

fun test_val x = 
  not (String.isPrefix "tactictoe" (fst x) orelse fst x = "it")

fun tactictoe_cleanval () = 
  let val l = filter test_val (#allVal PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetValue (map fst l)
  end

fun tactictoe_export s =
  let
    val dir = hhs_open_dir ^ "/" ^ s
    val l = filter test_val (#allVal PolyML.globalNameSpace ())
    val structures = 
      filter (test_struct s) (#allStruct PolyML.globalNameSpace ())
    val (values,constructors,exceptions) = part_val l
  in
    writel (dir ^ "/structures")   (map fst structures);
    writel (dir ^ "/values")       (map fst values);
    writel (dir ^ "/constructors") (map fst constructors);
    writel (dir ^ "/exceptions")   (map fst exceptions)
  end

(* ---------------------------------------------------------------------------
   Generating code
   -------------------------------------------------------------------------- *)

fun code_of s =
  [
   "open hhsOpen;",
   "tactictoe_cleanval ();", 
   "tactictoe_cleanstruct " ^ mlquote s ^ ";",
   "open " ^ s ^ ";",
   "tactictoe_export " ^ mlquote s ^ ";"
  ]

(* ---------------------------------------------------------------------------
   Export
   -------------------------------------------------------------------------- *)

fun export_struct dirorg dirttt s = 
  let 
    val dirstruct = dirttt ^ "/" ^ s
    val structuo = dirstruct ^ "/code.uo"
  in
    mkDir_err hhs_open_dir; mkDir_err (hhs_open_dir ^ "/" ^ s);
    mkDir_err dirttt; mkDir_err dirstruct; 
    writel (dirstruct ^ "/code.sml") (code_of s);
    code_mfile dirorg dirstruct;
    run_holmake dirstruct;
    run_hol structuo
  end

(* ---------------------------------------------------------------------------
   Import
   -------------------------------------------------------------------------- *)

fun import_struct s = 
  let val dir = hhs_open_dir ^ "/" ^ s in
    (readl (dir ^ "/values"), readl (dir ^ "/constructors"),
     readl (dir ^ "/exceptions"), readl (dir ^ "/structures"))
  end

(* ---------------------------------------------------------------------------
   Export and import
   -------------------------------------------------------------------------- *)

fun export_import_struct dirorg dirttt s =
  (
  export_struct dirorg dirttt s;
  import_struct s handle _ => 
    (debug_unfold ("warning: structure " ^ s ^ " not found"); ([],[],[],[]))
  )



end (* struct *)
