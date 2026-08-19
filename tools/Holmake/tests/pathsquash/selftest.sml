(* Unit tests for the two pieces of Holmake_tools that decide how a
   target's directory is rendered in the parallel builder's completion
   lines (tools/Holmake/poly/MB_Monitor.sml).

     hmdir.tree_key      names the source tree a directory belongs to;
                         the build shows holpath prefixes only when the
                         directories being built span more than one.
     squash_path         shortens the directory to the space the
                         completion line has left for it.
*)

open testutils

fun quote s = "\"" ^ String.toString s ^ "\""
fun equals expected = check_result (fn r => r = expected)

val squash = Holmake_tools.squash_path

fun sqtest (w, s, expected) =
    (tprint ("squash_path " ^ Int.toString w ^ " " ^ quote s);
     require_msg (equals expected) quote (squash w) s)

val cml = "$(CAKEMLDIR)/compiler/backend/proofs"
val rel = "examples/lambda/barendregt/basics"
val abs = "/opt/stuff/deep/place"
val one = "verylongdirectoryname"

val _ = List.app sqtest [
      (* the whole path while it fits ... *)
      (36, cml, "$(CAKEMLDIR)/compiler/backend/proofs"),
      (* ... then interior arcs go one at a time, tree name retained *)
      (35, cml, "$(CAKEMLDIR)/.../backend/proofs"),
      (31, cml, "$(CAKEMLDIR)/.../backend/proofs"),
      (30, cml, "$(CAKEMLDIR)/.../proofs"),
      (23, cml, "$(CAKEMLDIR)/.../proofs"),
      (* then the tree name itself is sacrificed for the leaf arcs *)
      (22, cml, ".../backend/proofs"),
      (18, cml, ".../backend/proofs"),
      (17, cml, ".../proofs"),
      (10, cml, ".../proofs"),
      (* and finally the last arc is cut on the left *)
      (9, cml, "...proofs"),
      (6, cml, "...ofs"),
      (4, cml, "...s"),
      (* no room for even one character of content *)
      (3, cml, ""),
      (0, cml, ""),
      (~3, cml, ""),

      (* a relative path (what a single-tree build shows) elides the
         same way *)
      (33, rel, "examples/lambda/barendregt/basics"),
      (32, rel, "examples/.../barendregt/basics"),
      (29, rel, "examples/.../basics"),
      (18, rel, ".../basics"),
      (9, rel, "...basics"),

      (* an unabbreviated absolute path keeps its leading slash: that
         slash is part of what identifies the tree *)
      (21, abs, "/opt/stuff/deep/place"),
      (20, abs, "/opt/.../deep/place"),
      (18, abs, "/opt/.../place"),
      (13, abs, ".../place"),

      (* a single arc has no interior to elide *)
      (21, one, "verylongdirectoryname"),
      (20, one, "...longdirectoryname"),
      (7, one, "...name")
    ]

val _ = tprint "squash_path never exceeds its width"
val _ =
    let
      fun bad w =
          List.exists (fn s => size (squash w s) > Int.max(w, 0))
                      [cml, rel, abs, one, "", "/", "a/b"]
      val ws = List.tabulate (60, fn i => i - 2)
    in
      case List.find bad ws of
          NONE => OK()
        | SOME w => die ("too wide at " ^ Int.toString w)
    end

(* ---------------------------------------------------------------------
    the path database underneath, and hmdir.tree_key over it
   --------------------------------------------------------------------- *)

val _ = holpathdb.extend_db {vname = "TSTOUTER", path = "/tmp/tstouter"}
val _ = holpathdb.extend_db {vname = "TSTINNER",
                             path = "/tmp/tstouter/inner"}

(* a directory that *is* a registered directory abbreviates to a bare
   $(VNAME); tree_key leans on this for such a directory to be counted
   as being in its own tree at all *)
fun rltest (s, expected) =
    (tprint ("reverse_lookup " ^ quote s);
     require_msg (equals expected) quote
                 (fn p => holpathdb.reverse_lookup {path = p}) s)

val _ = List.app rltest [
      ("/tmp/tstouter", "$(TSTOUTER)"),
      ("/tmp/tstouter/sub", "$(TSTOUTER)/sub"),
      ("/tmp/elsewhere", "/tmp/elsewhere")
    ]

fun tkey s = Holmake_tools.hmdir.tree_key
               (Holmake_tools.hmdir.fromPath {origin = "/", path = s})

fun tktest (s, expected) =
    (tprint ("tree_key " ^ quote s);
     require_msg (equals expected) quote tkey s)

val _ = List.app tktest [
      ("/tmp/tstouter/sub/dir", "$(TSTOUTER)"),
      ("/tmp/tstouter", "$(TSTOUTER)"),
      (* deepest registered directory wins *)
      ("/tmp/tstouter/inner", "$(TSTINNER)"),
      ("/tmp/tstouter/inner/deeper", "$(TSTINNER)"),
      (* not a prefix in the path sense, despite the string prefix *)
      ("/tmp/tstouterly", ""),
      ("/tmp/elsewhere", "")
    ]
