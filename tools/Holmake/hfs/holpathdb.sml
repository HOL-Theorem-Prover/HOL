structure holpathdb :> holpathdb =
struct

val empty_strset = Binaryset.empty String.compare
type dbrec = {mapf : (string,string) Binarymap.dict,
              dom : string Binaryset.set, rng : string Binaryset.set}
val holpath_db : dbrec ref =
    ref {mapf = Binarymap.mkDict String.compare, dom = empty_strset,
         rng = empty_strset}

fun fold f x = Binarymap.foldl (fn (k,v,A) => f {vname = k, path = v} A) x
                               (#mapf (!holpath_db))

fun lookup_holpath {vname = s} = Binarymap.peek(#mapf (!holpath_db), s)

fun reverse_lookup {path} =
  let
    fun split vnm p0 p =
      "$(" ^ vnm ^ ")/" ^ String.extract(p, size p0 + 1, NONE)
    fun foldthis (vnm, p, acc) =
      if String.isPrefix (p^"/") path then
        case acc of
            NONE => SOME (size p, split vnm p path)
          | SOME (sz', p') => if size p > sz' then
                                SOME (size p, split vnm p path)
                              else acc
      else acc
  in
    case Binarymap.foldl foldthis NONE (#mapf (!holpath_db)) of
        NONE => path
      | SOME (_, p) => p
  end

fun extend_db {vname, path} =
    let val {mapf,dom,rng} = !holpath_db
    in
      holpath_db := {mapf = Binarymap.insert(mapf, vname, path),
                     dom = Binaryset.add(dom, vname),
                     rng = Binaryset.add(rng, path)}
    end

fun db_vnames() = #dom (!holpath_db)
fun db_dirs() = #rng (!holpath_db)

fun warn s = TextIO.output(TextIO.stdErr, "WARNING: " ^ s ^ "\n")

fun subst_pathvars modPath =
  let
    fun die s = (warn s; modPath)
  in
    if size modPath > 0 andalso String.sub(modPath, 0) = #"$" then
      if size modPath < 2 orelse String.sub(modPath, 1) <> #"(" then
        die ("Bad occurrence of $ in mod-path "^modPath)
      else
        let
          val (varname, rest) =
              Substring.position ")" (Substring.extract(modPath, 2, NONE))
          val varname = Substring.string varname
        in
          if Substring.size rest = 0 then
            die ("No matching r-paren in "^modPath)
          else
            let
              val rest = Substring.string
                           (Substring.dropl (fn c => c = #"/")
                                            (Substring.slice(rest,1,NONE)))
            in
              case lookup_holpath {vname = varname} of
                  NONE => die ("No HOL path for variable "^varname^" in " ^
                               modPath)
                | SOME p => OS.Path.concat(p,rest)
            end
        end
    else modPath
  end

fun read_whole_file{filename} =
    let
      val istrm = TextIO.openIn filename
      fun readit A =
          case TextIO.inputLine istrm of
              NONE => (TextIO.closeIn istrm; String.concat (List.rev A))
            | SOME s => readit (s::A)
    in
      readit []
    end

fun set_member s e = Binaryset.member(s,e)

fun checkfile_is_bare filename =
    let
      val {arcs = farcs, isAbs = fabs, vol} = OS.Path.fromString filename
    in
      if not fabs andalso length farcs = 1 andalso vol = "" then ()
      else
        raise Fail ("files_upward_in_hierarchy: bad filename: "^filename)
    end

fun files_upward_in_hierarchy gen_extras {diag} {filenames, starter_dirs, skip} =
    let
      val _ = app checkfile_is_bare filenames
      val _ = null filenames andalso
              raise Fail "files_upward_in_hierarchy: empty filenames list"
      fun maybe_readfiles filenames d A =
          case filenames of
              [] => A
            | filename::fs =>
              let
                val f = OS.Path.concat (d,filename)
              in
                if OS.FileSys.access(f,[OS.FileSys.A_READ]) then
                  Binarymap.insert(A, d, (filename, read_whole_file{filename = f}))
                else maybe_readfiles fs d A
              end

      fun recurse A visited worklist =
          case worklist of
              [] => A
            | [] :: rest => recurse A visited rest
            | (d0::ds) :: rest =>
              let
                val d = OS.Path.mkCanonical d0
                val _ = diag (fn _ => "Visiting " ^ d)
                val A' = maybe_readfiles filenames d A
                val visited' = Binaryset.add(visited, d)
                val parent = OS.Path.getParent d
                val to_maybe_visit = parent :: gen_extras d
                val to_visit = List.filter (not o set_member visited)
                                           to_maybe_visit
              in
                recurse A' visited' (to_visit :: ds :: rest)
              end
    in
      recurse (Binarymap.mkDict String.compare) skip
              [List.filter (not o set_member skip) starter_dirs]
    end



infix ++
fun p1 ++ p2 = OS.Path.concat(p1,p2)

val holproject_toml_file = "holproject.toml"
val holproject_local_file = "holproject.local.toml"
val holpath_file = ".holpath"

fun abs_relative_to base p =
    OS.Path.mkCanonical
      (if OS.Path.isAbsolute p then p
       else OS.Path.mkAbsolute {path = p, relativeTo = base})

(* Pull the holpath vname out of a parsed holproject.toml table.  An
   optional `holpath` key takes precedence; otherwise we fall back to
   `name`.  This lets a project keep a human-facing `name` (e.g.
   "cakeml") distinct from the variable name used in HOL paths (e.g.
   "CAKEMLDIR").  NONE means neither key is set.  Either key present
   with a non-string value raises Fail naming the offending path. *)
fun vname_from_table projfile tbl =
    let
      fun lookup_string key =
          case TOML.lookupInTable tbl [key] of
              NONE => NONE
            | SOME (TOMLvalue_dtype.STRING s) => SOME s
            | SOME _ =>
                raise Fail (holproject_toml_file ^ " at " ^ projfile ^
                            ": `" ^ key ^ "` must be a string")
    in
      case lookup_string "holpath" of
          SOME s => SOME s
        | NONE => lookup_string "name"
    end

(* [projects.<id>] externals from an already-parsed table, as (id, abs)
   pairs.  Ignores malformed sub-entries -- the strict variant lives in
   HMProject.externals_from_table and fires when project mode engages. *)
fun externals_from_table dir tbl =
    case TOML.lookupInTable tbl ["projects"] of
        SOME (TOMLvalue_dtype.TABLE svs) =>
          List.mapPartial
            (fn (id, TOMLvalue_dtype.TABLE inner) =>
                  (case TOML.lookupInTable inner ["path"] of
                       SOME (TOMLvalue_dtype.STRING p) =>
                         SOME (id, abs_relative_to dir p)
                     | _ => NONE)
              | _ => NONE)
            svs
      | _ => []

fun extract_from_holpath_file s =
    let
      val sz = size s - 1
      val nm = if String.sub(s,sz) = #"\n" then String.extract(s,0,SOME sz) else s
    in
      nm
    end

(* Try to open+read a file; NONE on any IO/permissions failure.  Used for
   files that may or may not exist -- skipping the pre-check keeps this
   TOCTOU-safe and halves syscalls in the miss path. *)
fun try_read_file f =
    SOME (read_whole_file {filename = f}) handle IO.Io _ => NONE

(* Externals declared in `dir`'s holproject.local.toml (if any).  Local
   overrides live only in this per-dev-file; the committed file is
   handled by the caller who has already parsed it. *)
fun local_externals_at dir =
    case try_read_file (dir ++ holproject_local_file) of
        NONE => []
      | SOME c => (externals_from_table dir (TOML.fromString c)
                   handle _ => [])

(* Dedup by id: keep first occurrence in input order.  Feed locals first
   so they override same-id entries from the committed file, matching
   HMProject.load's precedence at core/HMProject.sml:258-263. *)
fun dedup_ext_paths xs =
    let
      fun step ((id, p), acc) =
          if List.exists (fn (id', _) => id' = id) acc then acc
          else (id, p) :: acc
    in
      List.map #2 (List.rev (List.foldl step [] xs))
    end


fun search_for_extensions gen {skip,starter_dirs = dlist} =
  let
    val dmap = files_upward_in_hierarchy gen {diag = fn _ => ()}
                 {filenames = [holproject_toml_file, holpath_file],
                  starter_dirs = dlist, skip = skip}

    (* Single pass over dmap: parse each holproject.toml once and pull
       both the self-vname and the [projects.<id>] externals from the same
       table.  Seeds carry the externals-lists into the worklist below,
       avoiding a re-read of the same files the upward walk already
       loaded. *)
    fun collect (dstr, (fnm, contents), (results, seeds)) =
        if fnm = holproject_toml_file then
          let
            val dstr = OS.Path.mkCanonical dstr
            val projfile = dstr ++ holproject_toml_file
            val tbl = TOML.fromString contents
                      handle e =>
                        raise Fail ("Malformed " ^ holproject_toml_file ^
                                    " at " ^ projfile ^ ": " ^
                                    General.exnMessage e)
            val results' =
                case vname_from_table projfile tbl of
                    NONE => results
                  | SOME nm => {vname = nm, path = dstr} :: results
            val exts = dedup_ext_paths
                         (local_externals_at dstr @
                          externals_from_table dstr tbl)
          in
            (results', (dstr, exts) :: seeds)
          end
        else if fnm = holpath_file then
          ({vname = extract_from_holpath_file contents, path = dstr}
           :: results, seeds)
        else (results, seeds)
    val (self_results, seeds) = Binarymap.foldl collect ([], []) dmap

    (* Fixed-point walk over reachable externals.  Registers the *target's*
       own holpath/name, not the [projects.<id>] `id' from the consumer --
       the `id' is a diagnostic label per HMProject.sig:5-6, whereas the
       token embedded in B's .ui/.uo headers is B's own holpath.
       Permissive: a broken external is silently skipped and only surfaces
       via HMProject.load when project mode actually engages. *)
    val initial_visited =
        List.foldl (fn ((d, _), s) => Binaryset.add(s, d)) empty_strset seeds
    fun step (ext, (visited, results, worklist)) =
        let val ext = OS.Path.mkCanonical ext in
          if Binaryset.member (visited, ext) then (visited, results, worklist)
          else
            let val visited' = Binaryset.add (visited, ext) in
              case try_read_file (ext ++ holproject_toml_file) of
                  NONE => (visited', results, worklist)
                | SOME contents =>
                    let
                      val projfile = ext ++ holproject_toml_file
                      val tbl_opt = SOME (TOML.fromString contents)
                                    handle _ => NONE
                    in
                      case tbl_opt of
                          NONE => (visited', results, worklist)
                        | SOME tbl =>
                            let
                              val results' =
                                  case (vname_from_table projfile tbl
                                        handle _ => NONE) of
                                      NONE => results
                                    | SOME v =>
                                        {vname = v, path = ext} :: results
                              val exts = dedup_ext_paths
                                           (local_externals_at ext @
                                            externals_from_table ext tbl)
                            in
                              (visited', results', exts :: worklist)
                            end
                    end
            end
        end
    fun walk (visited, results, worklist) =
        case worklist of
            [] => results
          | exts :: rest =>
              let val (visited', results', worklist') =
                      List.foldl step (visited, results, rest) exts
              in walk (visited', results', worklist') end
  in
    walk (initial_visited, self_results, List.map #2 seeds)
  end


end (* struct *)
