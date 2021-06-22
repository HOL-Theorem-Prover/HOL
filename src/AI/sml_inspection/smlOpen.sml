(* ========================================================================  *)
(* FILE          : smlOpen.sml                                               *)
(* DESCRIPTION   : Find string representation of SML values and structures   *)
(* in a signature.                                                           *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure smlOpen :> smlOpen =
struct

open HolKernel boolLib aiLib smlExecScripts

val ERR = mk_HOL_ERR "smlOpen"
val open_dir = HOLDIR ^ "/src/AI/sml_inspection/open"
val openscript_dir = HOLDIR ^ "/src/AI/sml_inspection/openscript"

(* -------------------------------------------------------------------------
   Generate SML code for exporting values of a structure
   ------------------------------------------------------------------------- *)

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

fun sml_cleanstruct s =
  let val l = filter (test_struct s) (#allStruct PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetStructure (map fst l)
  end

fun test_val x =
  not (String.isPrefix "sml" (fst x) orelse fst x = "it")

fun sml_cleanval () =
  let val l = filter test_val (#allVal PolyML.globalNameSpace ()) in
    app PolyML.Compiler.forgetValue (map fst l)
  end

fun sml_exportstruct s =
  let
    val dir = open_dir ^ "/" ^ s
    val _ = app mkDir_err [open_dir,dir]
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

fun export_struct_code s =
  [
   "open smlOpen;",
   "sml_cleanval ();",
   "sml_cleanstruct " ^ mlquote s ^ ";",
   "open " ^ s ^ ";",
   "sml_exportstruct " ^ mlquote s ^ ";"
  ]

(* -------------------------------------------------------------------------
   Run previous code
   ------------------------------------------------------------------------- *)

fun export_struct s =
  let
    val _ = mkDir_err openscript_dir
    val script = openscript_dir ^ "/" ^ s ^ "__open__sml.sml"
  in
    writel script (export_struct_code s);
    exec_script script
  end

fun import_struct s =
  let val dir = open_dir ^ "/" ^ s in
    (readl (dir ^ "/values"), readl (dir ^ "/constructors"),
     readl (dir ^ "/exceptions"), readl (dir ^ "/structures"))
  end

fun view_struct s =
  (
  export_struct s;
  import_struct s handle Interrupt => raise Interrupt | _ => ([],[],[],[])
  )

fun view_struct_cached s = import_struct s handle Io _ => view_struct s


end (* struct *)
