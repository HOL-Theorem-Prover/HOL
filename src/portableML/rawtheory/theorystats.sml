structure theorystats =
struct

open Portable
open RawTheory_dtype
open RawTheoryReader

val emit_scan_progress = ref (fn (s:string) => ())

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

fun getHash p = SHA1.sha1_file {filename=p}

fun readThy p (g,links) =
    let
      val _ = !emit_scan_progress p
      open RawTheoryReader
      val dat as {parents, name, exports, ...} =
          RawTheoryReader.load_raw_thydata{path = p}
          handle TheoryReader s => raise Fail ("Bad decode for " ^ p)
      val {dir, file} = OS.Path.splitDirFile p
      val {base, ext} = OS.Path.splitBaseExt file
      val _ = ext = SOME "dat" andalso base = name ^ "Theory" orelse
              (warn ("Theory.dat at " ^ p ^ " has name " ^ name); true)
      val hash = HFS_NameMunge.toFSfn false getHash p
      val key = ({thy=name, hash=hash},dir)
    in
      SOME (g |> TheoryGraph.new_node(key, {exports=exports, parents=parents}),
            (key, parents)::links)
    end handle Fail s => (warn s; NONE)
             | e => die ("readThy \"" ^ String.toString p ^ "\": " ^
                         General.exnMessage e)


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

fun find_theory_files_action dir A =
  let
    open OS.FileSys
    val objsdirname = dir ++ ".hol/objs"
  in
    if access (objsdirname, [A_READ, A_EXEC])
       andalso isDir objsdirname
    then
      let
        val thys =
          Portable.listDir objsdirname
          |> List.filter
               (String.isSuffix "Theory.dat")
        fun collect (thyfile, acc) =
          let
            val thydat = dir ++ thyfile
            val {base, ...} =
              OS.Path.splitBaseExt thyfile
            val thy_name =
              String.substring
                (base, 0, size base - 6)
          in
            Symtab.cons_list
              (thy_name, thydat) acc
          end
      in
        List.foldl collect A thys
      end
    else A
  end

fun find_theory_action dir A =
    let
      open OS.FileSys
      val objsdirname = dir ++ ".hol/objs"
    in
      if access (objsdirname, [A_READ, A_EXEC]) andalso isDir objsdirname then
        let val thys =
                Portable.listDir objsdirname
                                 |> List.filter (String.isSuffix "Theory.dat")
                                 |> List.map (fn thy => dir ++ thy)
            fun foldthis (thydat,A) =
                let val f = #file (OS.Path.splitDirFile thydat)
                    val b = #base (OS.Path.splitBaseExt f)
                in
                  if access(objsdirname ++ (b ^ ".sig"), [A_READ]) then
                    if access (dir ++ (String.substring(b, 0, size b - 6) ^
                                       "Script.sml"),
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

(* ======================================================================== *)
(* Unused theorem scanning *)
(* ======================================================================== *)

type thm_ref = {thy : string, idx : int}

fun string_of_thm_ref {thy, idx} =
  thy ^ "[" ^ Int.toString idx ^ "]"

(* Load theories and their ancestors *)
fun load_with_ancestors
    target_thys thy_file_map (g, links) =
  let
    val to_read = ref target_thys
    val read_set =
      ref (Redblackset.empty String.compare)
    val result_g = ref g
    val result_links = ref links

    fun process_thy thy =
      if Redblackset.member(!read_set, thy)
      then ()
      else
        let
          val _ =
            read_set :=
              Redblackset.add(!read_set, thy)
          val paths =
            case Symtab.lookup thy_file_map thy
            of SOME ps => ps
             | NONE => []
          fun try_paths [] = ()
            | try_paths (p::ps) =
                case readThy p
                       (!result_g, !result_links)
                of
                  SOME (new_g, new_links) =>
                    let
                      val (key, parents) =
                        (case new_links of
                          [] => raise Fail "empty links"
                        | (k, ps) :: _ =>
                            (k, ps))
                    in
                      result_g := new_g;
                      result_links := new_links;
                      List.app
                        (fn p =>
                          to_read :=
                            (#thy p) :: !to_read
                        ) parents
                    end
                | NONE => try_paths ps
        in
          try_paths paths
        end

    fun loop () =
      case !to_read of
        [] => ()
      | thy :: rest =>
          (to_read := rest;
           process_thy thy;
           loop ())
  in
    loop ();
    (!result_g, !result_links)
  end

(* Extract all theorem names and build index *)
fun build_usage_sets theories =
  let
    (* Collect all theorem names *)
    val all_thms =
      ref ([] : (thm_ref * string) list)

    (* Set of theorems that are depended upon *)
    val used_thms = ref ([] : thm_ref list)

    fun process_theory (thy_name, nd : raw_nodedata) =
      let
        val {exports, ...} = nd
        val {thms, ...} = exports
        fun process_idx_thm (i, thm) =
          let
            val ref_key = {thy = thy_name, idx = i}
            val name = #name thm
          in
            all_thms := (ref_key, name) :: !all_thms
          end
        val thm_indices =
          List.tabulate (List.length thms, fn i => i)
      in
        ListPair.app process_idx_thm
          (thm_indices, thms);

        List.app (fn thm =>
          let val {deps, ...} = #deps thm
          in
            List.app (fn (dep_thy, indices) =>
              List.app (fn idx =>
                used_thms :=
                  {thy = dep_thy, idx = idx} :: !used_thms
              ) indices
            ) deps
          end
        ) thms
      end
  in
    List.app process_theory theories;
    (!all_thms, !used_thms)
  end

(* Find unused theorems *)
fun find_unused theories =
  let
    val (all_thms, used_thms) =
      build_usage_sets theories
    fun is_used ref_key =
      List.exists (fn u =>
        #thy u = #thy ref_key andalso
        #idx u = #idx ref_key
      ) used_thms
  in
    List.filter (fn (ref_key, _) =>
      not (is_used ref_key)
    ) all_thms
  end


end (* struct *)

