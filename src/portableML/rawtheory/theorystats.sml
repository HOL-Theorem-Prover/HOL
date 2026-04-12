structure theorystats :> theorystats =
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

type thykey = RawTheory_dtype.raw_name * string
structure RawTheorykey =
struct
  type key = thykey
  val ord = pair_compare (raw_name_compare, String.compare)
  fun pp (rn, p) =
      HOLPP.add_string(
        "(" ^ raw_name_toString rn ^ ", \"" ^ String.toString p ^ "\")"
      )
end

structure TheoryGraph = Graph(RawTheorykey)

type thygraph_data = {exports : string RawTheory_dtype.raw_exports,
                      parents : raw_name list} TheoryGraph.T *
                     (thykey * raw_name list) list

type theory_locn_map = string list Symtab.table

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


(* ----------------------------------------------------------------------
    Depth-first, preorder
   ---------------------------------------------------------------------- *)
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
       andalso isDir objsdirname then
      let
        val thys =
          Portable.listDir objsdirname
          |> List.filter (String.isSuffix "Theory.dat")
        fun collect (thyfile, acc) =
          let
            val thydat = dir ++ thyfile
            val {base, ...} = OS.Path.splitBaseExt thyfile
            val thy_name =
              String.substring (base, 0, size base - 6)
          in
            Symtab.cons_list (thy_name, thydat) acc
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

(* ----------------------------------------------------------------------
    Unused theorem scanning
   ---------------------------------------------------------------------- *)

type thm_ref = {thy : string, idx : int}

fun string_of_thm_ref {thy, idx} =
  thy ^ "[" ^ Int.toString idx ^ "]"

structure ThmRefKey =
struct
  type key = thm_ref
  val ord = fn ({thy=t1, idx=i1}, {thy=t2, idx=i2}) =>
    case String.compare(t1, t2) of
      EQUAL => Int.compare(i1, i2)
    | other => other
  fun pp {thy, idx} =
    HOLPP.add_string (thy ^ "[" ^ Int.toString idx ^ "]")
end

structure ThmGraph = Graph(ThmRefKey)

(* ----------------------------------------------------------------------
    Load theories and their ancestors
   ---------------------------------------------------------------------- *)

fun load_with_ancestors target_thys thy_file_map (g, links) =
  let
    fun process_thy thy (read_set, (G, links)) =
      if Redblackset.member(read_set, thy) then ((read_set, (G, links)), [])
      else
        let
          val read_set' = Redblackset.add(read_set, thy)
        in
          case Symtab.lookup thy_file_map thy of
              SOME [p] =>
              (case readThy p (G, links) of
                   SOME (G',l') => ((read_set', (G',l')), map #thy (#2 (hd l')))
                 | NONE => ((read_set', (G, links)), []))
            | SOME ps =>
              die
                ("Cannot cope with multiple instances of theory " ^
                 thy ^ " which appears to be present at\n" ^
                 String.concat (map (fn p => " " ^ p ^ "\n") ps))
            | NONE => (warn ("Cannot find location of theory " ^ thy ^
                             "; ignoring it");
                       ((read_set', (G, links)), []))
        end

    fun loop glr worklist =
        case worklist of
            [] => glr
          | [] :: rest => loop glr rest
          | (thy :: rest1) :: rest2 =>
            case process_thy thy glr of
                (gl', parents) => loop gl' (parents :: rest1 :: rest2)
  in
    #2 (loop (Redblackset.empty String.compare, (g, links)) [target_thys])
  end

(* ----------------------------------------------------------------------
    Find unused theorems
   ---------------------------------------------------------------------- *)

fun find_unused theories =
  let
    val all_thm_refs = ref ([] : (thm_ref * string) list)

    fun scan_max_indices ((thy_name, {exports,...} : raw_nodedata), tab) =
      let
        val {thms, ...} = exports
        fun foldthis ({deps, name, ...}:string raw_thm, (mx, nametab)) =
          let
            val {me = (_, i), ...} = deps
          in
            (Int.max(i,mx), Inttab.update (i, name) nametab)
          end
      in
        Symtab.update (thy_name, List.foldl foldthis (0, Inttab.empty) thms) tab
      end
    val name_maxidx_tab = List.foldl scan_max_indices Symtab.empty theories
    val _ = Symtab.fold (fn (thy, (mx, _)) => fn () =>
                            print ("Theory " ^ thy ^ " has max idx " ^
                                   Int.toString mx ^ "\n"))
                        name_maxidx_tab ()


    val used_array_tab =
        Symtab.fold (fn (thy,(mx, _)) =>
                        Symtab.update (thy, Array.array(mx+1, false)))
                    name_maxidx_tab
                    Symtab.empty

    fun process_theory (thy_name, nd : raw_nodedata) =
      let
        val {exports, ...} = nd
        val {thms, ...} = exports
        fun process_idx_thm {deps, ...} =
          let
            val {deps=dep_list, ...} = deps
            fun appthis (dep_thy, indices) =
              case Symtab.lookup used_array_tab dep_thy of
                  SOME arr =>
                  (* Subscript exception is possible because of theorems
                     that are stored in TypeBase and not exported with names *)
                  List.app (fn idx => Array.update(arr, idx, true)
                                      handle Subscript => ())
                           indices
                | NONE => ()
          in
            List.app appthis dep_list
          end
      in
        List.app process_idx_thm thms
      end
    fun buildresult (thy, arr) tab =
        let
          val (_, nametab) = valOf (Symtab.lookup name_maxidx_tab thy)
          fun foldthis (i, usedp, tab) =
              if not usedp then
                case Inttab.lookup nametab i of
                    NONE => tab
                  | SOME s => Symtab.map_default
                                (thy,Redblackset.empty String.compare)
                                (fn set => Redblackset.add(set,s))
                                tab
              else tab
        in
          Array.foldli foldthis tab arr
        end
  in
    List.app process_theory theories;
    Symtab.fold buildresult used_array_tab Symtab.empty
  end


end (* struct *)

