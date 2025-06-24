structure theorystats =
struct

open Portable
open RawTheory_dtype
open RawTheoryReader

infix |>
fun x |> f = f x

infix ++
val op++ = OS.Path.concat

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             TextIO.flushOut TextIO.stdErr;
             OS.Process.exit OS.Process.failure)

fun warn s = (
  TextIO.output(TextIO.stdErr, "WARNING: " ^ s ^ "\n");
  TextIO.flushOut TextIO.stdErr
);

fun println s = print (s ^ "\n")

structure RawTheorykey =
struct
  type key = raw_name * string (* name with hash + path *)
  val ord = pair_compare (raw_name_compare, String.compare)
  fun pp (rn, p) =
      HOLPP.add_string(
        "(" ^ raw_name_toString rn ^ ", \"" ^ String.toString p ^ "\")"
      )
end

structure TheoryGraph = Graph(RawTheorykey)

type raw_nodedata = {
  exports : string raw_exports,
  parents : raw_name list
}

type derived_data = {
  name : string,
  parents : string list,
  num_axms : int,
  num_defs : int,
  num_thms : int,
  path : string
}


fun readThy p (g,links) =
    let
      open RawTheoryReader
      val dat as {parents, name, exports, ...} =
          RawTheoryReader.load_raw_thydata{path = p}
          handle TheoryReader s => raise Fail ("Bad decode for " ^ p)
      val {dir, file} = OS.Path.splitDirFile p
      val {base, ext} = OS.Path.splitBaseExt file
      val _ = ext = SOME "dat" andalso base = name ^ "Theory" orelse
              (warn ("Theory.dat at " ^ p ^ " has name " ^ name); true)
      val hash = SHA1.sha1_file {filename=p}
      val key = ({thy=name, hash=hash},dir)
    in
      SOME (g |> TheoryGraph.new_node(key, {exports = exports, parents = parents}),
            (key, parents)::links)
    end handle Fail s => (warn s; NONE)


(* depth-first, preorder *)
fun recurse_toDirs action A worklist =
    case worklist of
        [] => A
      | d::ds =>
        let
          val A' = action d A
          val ds' = Portable.listDir d
                                     |> map (fn f => d ++ f)
                                     |> List.filter OS.FileSys.isDir
        in
          recurse_toDirs action A' (ds' @ ds)
        end

fun find_theory_action dir A =
    let
      open OS.FileSys
      val objsdirname = dir ++ ".holobjs"
    in
      if access (objsdirname, [A_READ, A_EXEC]) andalso isDir objsdirname then
        let val thys = Portable.listDir objsdirname
                                        |> List.filter (String.isSuffix "Theory.dat")
                                        |> List.map (fn thy => dir ++ thy)
            fun foldthis (thydat,A) =
                let val f = #file (OS.Path.splitDirFile thydat)
                    val b = #base (OS.Path.splitBaseExt f)
                in
                  if access(dir ++ (b ^ ".sig"), [A_READ]) then
                    if access (dir ++ (String.substring(b, 0, size b - 6) ^ "Script.sml"),
                               [A_READ])
                    then
                      case readThy thydat A of SOME A' => A' | NONE => A
                    else (
                      warn (
                        "No Script.sml file for " ^ thydat ^
                        "; ignoring it");
                      A
                    )
                  else (
                    warn ("No Theory.sig file for " ^ thydat ^
                          "; ignoring it");
                    A
                  )
                end
        in
          List.foldl foldthis A thys
        end
      else A
    end


end (* struct *)

