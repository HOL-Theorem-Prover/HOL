(*
   End-to-end test for [projects.<id>] siblings: A refers to B via
   `[projects.b] path = "../B"` where B is a sibling directory, not an
   ancestor.  Before the fix, running Holmake in A dies with
   `Cannot find file $(sib_B)/BTheory.ui' during the load of B's compiled
   theory, because holpathdb's upward walk from A never visits B and so
   never registers `sib_B'.
*)
open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val hol_state0 = Globals.HOLDIR ++ "bin" ++ "hol.state0"

fun run_holmake_in dir args =
    let val saved = OS.FileSys.getDir()
        val _ = OS.FileSys.chDir dir
        val r = Systeml.systeml (Holmake :: args)
    in
      OS.FileSys.chDir saved; r
    end

fun write_file p contents =
    let val s = TextIO.openOut p
    in TextIO.output (s, contents); TextIO.closeOut s end

fun rm_rf p =
    if OS.FileSys.isDir p handle OS.SysErr _ => false then
      let val ds = OS.FileSys.openDir p
          fun loop () =
              case OS.FileSys.readDir ds of
                  NONE => OS.FileSys.closeDir ds
                | SOME nm => (rm_rf (p ++ nm); loop ())
      in loop (); OS.FileSys.rmDir p handle OS.SysErr _ => () end
    else (OS.FileSys.remove p handle OS.SysErr _ => ())

fun fresh_dir () =
    let val nm = OS.FileSys.tmpName ()
        val _ = OS.FileSys.remove nm handle OS.SysErr _ => ()
        val _ = OS.FileSys.mkDir nm
    in nm end

fun holheap_decl () =
    "ifdef POLY\nHOLHEAP = " ^ hol_state0 ^ "\nendif\n"

fun product_at d nm =
    HOLFileSys.access (d ++ nm, []) handle OS.SysErr _ => false

fun read_all f =
    let val is = TextIO.openIn f
    in TextIO.inputAll is before TextIO.closeIn is end
    handle _ => ""

(* ---------- 1. One-hop sibling: A refers to B via [projects.b] ---------- *)

val _ = tprint "sibling externals: build B, then Holmake in A resolves $(sib_B)"

val root1 = fresh_dir ()
val dirA1 = root1 ++ "A"
val dirB1 = root1 ++ "B"
val _ = OS.FileSys.mkDir dirA1
val _ = OS.FileSys.mkDir dirB1

val _ = write_file (dirB1 ++ "holproject.toml") "name = \"sib_B\"\n"
val _ = write_file (dirB1 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirB1 ++ "BScript.sml")
  "Theory B[bare]\n\
  \Ancestors bool\n\
  \Theorem b_truth = TRUTH\n"

val _ = write_file (dirA1 ++ "holproject.toml")
  "name = \"sib_A\"\n\
  \[projects.b]\n\
  \path = \"../B\"\n"
val _ = write_file (dirA1 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirA1 ++ "AScript.sml")
  "Theory A[bare]\n\
  \Ancestors B\n\
  \Theorem a_truth = b_truth\n"

(* Step 1: build B standalone.  Sanity: B's .ui embeds `$(sib_B)` --
   the token the fix has to decode at A's build time. *)
val rB1 = run_holmake_in dirB1 ["--nolmbc"]
val bBuilt = product_at dirB1 "BTheory.uo"
val uiFile = dirB1 ++ ".hol" ++ "objs" ++ "BTheory.ui"
val uiContents = read_all uiFile
val hasSibToken = String.isSubstring "$(sib_B)" uiContents

(* Step 2: Holmake in A.  Must resolve $(sib_B) in B's headers. *)
val rA1 = run_holmake_in dirA1 ["--nolmbc"]
val aBuilt = product_at dirA1 "ATheory.uo"

val _ =
    if OS.Process.isSuccess rB1 andalso bBuilt andalso hasSibToken
       andalso OS.Process.isSuccess rA1 andalso aBuilt
    then OK ()
    else die ("FAILED: B_exit=" ^ Bool.toString (OS.Process.isSuccess rB1) ^
              " BTheory.uo=" ^ Bool.toString bBuilt ^
              " $(sib_B)-in-ui=" ^ Bool.toString hasSibToken ^
              " A_exit=" ^ Bool.toString (OS.Process.isSuccess rA1) ^
              " ATheory.uo=" ^ Bool.toString aBuilt)

(* ---------- 2. Two-hop transitive: A -> B -> C ---------- *)

val _ = tprint "sibling externals: transitive walk A -> B -> C"

val root2 = fresh_dir ()
val dirA2 = root2 ++ "A"
val dirB2 = root2 ++ "B"
val dirC2 = root2 ++ "C"
val _ = OS.FileSys.mkDir dirA2
val _ = OS.FileSys.mkDir dirB2
val _ = OS.FileSys.mkDir dirC2

val _ = write_file (dirC2 ++ "holproject.toml") "name = \"sib_C\"\n"
val _ = write_file (dirC2 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirC2 ++ "CScript.sml")
  "Theory C[bare]\n\
  \Ancestors bool\n\
  \Theorem c_truth = TRUTH\n"

val _ = write_file (dirB2 ++ "holproject.toml")
  "name = \"sib_B\"\n\
  \[projects.c]\n\
  \path = \"../C\"\n"
val _ = write_file (dirB2 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirB2 ++ "BScript.sml")
  "Theory B[bare]\n\
  \Ancestors C\n\
  \Theorem b_truth = c_truth\n"

val _ = write_file (dirA2 ++ "holproject.toml")
  "name = \"sib_A\"\n\
  \[projects.b]\n\
  \path = \"../B\"\n"
val _ = write_file (dirA2 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirA2 ++ "AScript.sml")
  "Theory A[bare]\n\
  \Ancestors B\n\
  \Theorem a_truth = b_truth\n"

val rC2 = run_holmake_in dirC2 ["--nolmbc"]
val rB2 = run_holmake_in dirB2 ["--nolmbc"]
val rA2 = run_holmake_in dirA2 ["--nolmbc"]
val aBuilt2 = product_at dirA2 "ATheory.uo"

val _ =
    if OS.Process.isSuccess rC2 andalso OS.Process.isSuccess rB2
       andalso OS.Process.isSuccess rA2 andalso aBuilt2
    then OK ()
    else die ("FAILED: C_exit=" ^ Bool.toString (OS.Process.isSuccess rC2) ^
              " B_exit=" ^ Bool.toString (OS.Process.isSuccess rB2) ^
              " A_exit=" ^ Bool.toString (OS.Process.isSuccess rA2) ^
              " A/ATheory.uo=" ^ Bool.toString aBuilt2)

(* ---------- 3. Local-file override: [projects.b] in holproject.local.toml ---------- *)

val _ = tprint "sibling externals: [projects.b] in holproject.local.toml"

val root3 = fresh_dir ()
val dirA3 = root3 ++ "A"
val dirB3 = root3 ++ "B"
val _ = OS.FileSys.mkDir dirA3
val _ = OS.FileSys.mkDir dirB3

val _ = write_file (dirB3 ++ "holproject.toml") "name = \"sib_B\"\n"
val _ = write_file (dirB3 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirB3 ++ "BScript.sml")
  "Theory B[bare]\n\
  \Ancestors bool\n\
  \Theorem b_truth = TRUTH\n"

val _ = write_file (dirA3 ++ "holproject.toml") "name = \"sib_A\"\n"
val _ = write_file (dirA3 ++ "holproject.local.toml")
  "[projects.b]\n\
  \path = \"../B\"\n"
val _ = write_file (dirA3 ++ "Holmakefile") (holheap_decl ())
val _ = write_file (dirA3 ++ "AScript.sml")
  "Theory A[bare]\n\
  \Ancestors B\n\
  \Theorem a_truth = b_truth\n"

val rB3 = run_holmake_in dirB3 ["--nolmbc"]
val rA3 = run_holmake_in dirA3 ["--nolmbc"]
val aBuilt3 = product_at dirA3 "ATheory.uo"

val _ =
    if OS.Process.isSuccess rB3 andalso OS.Process.isSuccess rA3
       andalso aBuilt3
    then OK ()
    else die ("FAILED: B_exit=" ^ Bool.toString (OS.Process.isSuccess rB3) ^
              " A_exit=" ^ Bool.toString (OS.Process.isSuccess rA3) ^
              " A/ATheory.uo=" ^ Bool.toString aBuilt3)

val _ = rm_rf root1
val _ = rm_rf root2
val _ = rm_rf root3
