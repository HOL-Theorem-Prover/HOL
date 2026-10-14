structure HFS_NameMunge :> HFS_NameMunge =
struct


infix ++
val op++ = OS.Path.concat
exception DirNotFound
val HOLOBJDIR = ".hol/objs"
val HOLOBJDIR_arcs = [".hol", "objs"]
val HOLOBJDIR_arcs' = ["objs", ".hol"]
  (* yes, flipped, as they're inserted into a list that is then reversed;
     see insert_before_last *)

(* Must not refer to Systeml: genUseScript.sml, poly-holdeptool.ML and
   portableML.mlb load this file before (or without) it. *)
val legacy_depdir = ".hol/make-deps"
val legacy_logdir = ".hol/logs"
val legacy_lockdir = ".hol/locks"
val legacy_docsdir = ".hol/docs"

fun warn s = (TextIO.output (TextIO.stdErr, s ^ "\n");
              TextIO.flushOut TextIO.stdErr)

fun base_app {dirname} P action a0 =
    let
      open OS.FileSys
      val ds = openDir dirname handle OS.SysErr _ => raise DirNotFound
      fun loop a =
          case readDir ds of
              NONE => (closeDir ds; a)
            | SOME nextfile =>
              loop (if P nextfile then action nextfile a else a)
    in
      loop a0 handle e => (closeDir ds; raise e) before
      closeDir ds
    end



fun insert_before_last A es [] = raise Fail "HFS_NameMunge: insert_before_last"
  | insert_before_last A es [last] = (List.rev (es @ A), last)
  | insert_before_last A es (h::t) = insert_before_last (h::A) es t

fun isPSuffix sfx s =
    size sfx < size s andalso String.isSuffix sfx s

fun last_and_revfront A [] = raise Fail "HFS_NameMunge: last_and_revfront"
  | last_and_revfront A [t] = (A, t)
  | last_and_revfront A (h::t) = last_and_revfront (h::A) t

(* ----------------------------------------------------------------------
    The layout
   ---------------------------------------------------------------------- *)

type layout = {srcroot : string, objroot : string}

fun absolute p =
    OS.Path.mkCanonical
      (if OS.Path.isAbsolute p then p
       else OS.Path.mkAbsolute {path = p, relativeTo = OS.FileSys.getDir()})

fun canonical p = OS.FileSys.fullPath p handle OS.SysErr _ => absolute p

fun join d "" = d
  | join d r = OS.Path.concat (d, r)

(* SOME rel when p is root or below it *)
fun rel_under root p =
    if p = root then SOME ""
    else if String.isPrefix (root ^ "/") p then
      SOME (String.extract (p, size root + 1, NONE))
    else NONE

(* fullPath of directories whose lexical position fails to match the
   layout (symlinked trees, macOS /var), memoised because the dependency
   scan asks about every product of every INCLUDES directory.  Races
   between threads only lose entries. *)
val nbuckets = 509
fun shash s =
    CharVector.foldl (fn (c, h) => (h * 31 + Char.ord c) mod nbuckets) 0 s
val realdirs : (string * string) list Array.array =
    Array.array (nbuckets, [])
fun clear_realdirs () =
    Array.modify (fn _ => []) realdirs
fun realdir d =
    let
      val i = shash d
    in
      case List.find (fn (k, _) => k = d) (Array.sub (realdirs, i)) of
          SOME (_, r) => r
        | NONE =>
          let
            val r = OS.FileSys.fullPath d handle OS.SysErr _ => d
          in
            Array.update (realdirs, i, (d, r) :: Array.sub (realdirs, i));
            r
          end
    end

(* NONE: never configured, so consult the environment (once).  A saved
   heap can carry the value of this reference, which is safe only
   because every bin/hol entry point calls configure after loadState. *)
val the_layout : layout option option ref = ref NONE
val stale_warned = ref false

fun configure lopt =
    (clear_realdirs ();
     stale_warned := false;
     the_layout :=
       SOME (Option.map
               (fn {srcroot, objroot} =>
                   {srcroot = OS.Path.mkCanonical srcroot,
                    objroot = OS.Path.mkCanonical objroot})
               lopt))

fun layout_from_env () =
    let
      fun get v = case OS.Process.getEnv v of
                      SOME "" => NONE
                    | x => x
    in
      case (get "HOLOBJROOT", get "HOLSRCROOT") of
          (NONE, NONE) => NONE
        | (SOME obj, SOME src) =>
          let
            val obj = canonical obj and src = canonical src
          in
            if obj = src then
              (warn "HOLOBJROOT and HOLSRCROOT are the same directory; \
                    \ignoring both";
               NONE)
            else SOME {srcroot = src, objroot = obj}
          end
        | (SOME _, NONE) =>
          (warn "HOLOBJROOT is set but HOLSRCROOT is not; ignoring HOLOBJROOT";
           NONE)
        | (NONE, SOME _) =>
          (warn "HOLSRCROOT is set but HOLOBJROOT is not; ignoring HOLSRCROOT";
           NONE)
    end

fun current_layout () =
    case !the_layout of
        SOME l => l
      | NONE => let val l = layout_from_env ()
                in
                  the_layout := SOME l; l
                end

datatype place = Legacy | InObjroot | Mapped of string

(* d is absolute and canonical *)
fun classify ({srcroot, objroot} : layout) d =
    let
      fun lexical d =
          case rel_under objroot d of
              SOME _ => SOME InObjroot
            | NONE => Option.map Mapped (rel_under srcroot d)
    in
      case lexical d of
          SOME p => p
        | NONE =>
          let val d' = realdir d
          in
            if d' = d then Legacy
            else getOpt (lexical d', Legacy)
          end
    end

fun owned_by_layout p =
    case current_layout () of
        NONE => false
      | SOME l => (case classify l (absolute p) of
                       Mapped _ => true
                     | _ => false)

fun kind_dir kind legacy d =
    case current_layout () of
        NONE => d ++ legacy
      | SOME (l as {objroot, ...}) =>
        let val absd = absolute d
        in
          case classify l absd of
              InObjroot => absd
            | Mapped rel => join (objroot ++ kind) rel
            | Legacy => d ++ legacy
        end

val objdir_for = kind_dir "objs" HOLOBJDIR
val depdir_for = kind_dir "make-deps" legacy_depdir
val logdir_for = kind_dir "logs" legacy_logdir
val lockdir_for = kind_dir "locks" legacy_lockdir
val docsdir_for = kind_dir "docs" legacy_docsdir

fun project_state_dir root =
    case current_layout () of
        SOME {srcroot, objroot} =>
          if absolute root = srcroot orelse canonical root = srcroot then
            objroot
          else root ++ ".hol"
      | NONE => root ++ ".hol"

fun holobjdir_var_for d =
    if owned_by_layout d then objdir_for d else HOLOBJDIR

fun artifact_dirs_for d =
    if owned_by_layout d then
      map (fn f => f d)
          [objdir_for, depdir_for, logdir_for, lockdir_for, docsdir_for]
    else []

fun FStoHOL p =
    let
      fun legacy () =
          let
            val {isAbs, vol, arcs} = OS.Path.fromString p
          in
            case List.rev arcs of
                f :: "objs" :: ".hol" :: rest =>
                SOME (OS.Path.toString
                        {isAbs = isAbs, vol = vol,
                         arcs = List.rev (f :: rest)})
              | _ => NONE
          end
    in
      case current_layout () of
          NONE => legacy ()
        | SOME {srcroot, objroot} =>
          (case rel_under (objroot ++ "objs") (absolute p) of
               SOME "" => NONE
             | SOME rel => SOME (join srcroot rel)
             | NONE => legacy ())
    end

(* Products left in <dir>/.hol/objs by a legacy build are ignored once a
   layout maps dir elsewhere; say so, once. *)
fun check_stale absd objdir =
    if !stale_warned then ()
    else
      let
        val legacy = absd ++ HOLOBJDIR
        fun nonempty d =
            let val ds = OS.FileSys.openDir d
            in
              isSome (OS.FileSys.readDir ds) before OS.FileSys.closeDir ds
            end handle OS.SysErr _ => false
      in
        if objdir <> legacy andalso nonempty legacy then
          (stale_warned := true;
           warn ("Ignoring stale products in " ^ legacy ^
                 " (run cleanAll in the legacy layout to remove them)"))
        else ()
      end

(* nm is the filename as HOL thinks it is; if that name is fine, then the
   function returns NONE; otherwise the function returns SOME(name', dir)
   where the name' is the complete path to where the filename actually needs
   to be, and dir is the directory that may need to be checked for existence
*)
fun HOLtoFS nm =
    let
      val {isAbs, vol, arcs} = OS.Path.fromString nm
      val (parent_paths, file) = last_and_revfront [] arcs
      val {base,ext} = OS.Path.splitBaseExt file
      val changep =
          case (parent_paths, ext) of
              ("sigobj" :: _, _) => false
            | (_, SOME s) => s = "uo" orelse s = "ui" orelse
                             (isPSuffix "Theory" base andalso
                              (s = "sml" orelse s = "dat" orelse s = "sig"))
            | (_, NONE) => false
      fun legacy () =
          let
            val (arcs', last) = insert_before_last [] HOLOBJDIR_arcs' arcs
            val dir = OS.Path.toString {isAbs = isAbs, vol = vol, arcs = arcs'}
          in
            SOME {fullfile = OS.Path.concat(dir, last), dir = dir}
          end
    in
      if changep then
        case current_layout () of
            NONE => legacy ()
          | SOME (l as {objroot, ...}) =>
            let
              val {dir, file} = OS.Path.splitDirFile (absolute nm)
            in
              case classify l dir of
                  InObjroot => NONE (* never munge twice *)
                | Mapped rel =>
                  let val dir' = join (objroot ++ "objs") rel
                  in
                    SOME {fullfile = dir' ++ file, dir = dir'}
                  end
                | Legacy => legacy ()
            end
      else NONE
    end

fun toFSfn writep f nm =
    let
      open OS.FileSys
      val aclist = (if writep then [A_WRITE] else []) @ [A_READ, A_EXEC]
    in
      case HOLtoFS nm of
          NONE => f nm
        | SOME {dir, fullfile = nm'} =>
          if OS.FileSys.access(dir, []) then
            if access(dir, aclist) andalso isDir dir
            then
              f nm'
            else raise Fail ("HFS_NameMunge: " ^ dir ^ " exists but is not " ^
                             "accessible directory")
          else if writep then
            (HOLFS_dtype.createDirIfNecessary dir; f nm')
          else f nm'
    end

(* How a directory listing presents products:
     Splice: legacy; the .hol entry is replaced by the entries of
             .hol/objs (in place, so listing order is as it always was)
     Plain: a directory inside objroot; listed as is
     Chain d: products live in d; a stray .hol entry is hidden and d's
              entries follow the directory's own *)
datatype listing = Splice | Plain | Chain of string

fun listing_for s =
    case current_layout () of
        NONE => Splice
      | SOME _ =>
        let
          val absd = absolute s
          val objdir = objdir_for absd
        in
          if objdir = (absd ++ HOLOBJDIR) then Splice
          else if objdir = absd then Plain
          else (check_stale absd objdir; Chain objdir)
        end

type dirstream = {dirname : string, listing : listing,
                  main : OS.FileSys.dirstream,
                  sub : OS.FileSys.dirstream option ref,
                  chained : bool ref}

fun openDir s : dirstream =
    let val listing = listing_for s
        val ds = OS.FileSys.openDir s
    in
      {dirname = s, listing = listing, main = ds, sub = ref NONE,
       chained = ref false}
    end

fun splice_readDir (dirname, ds, r as ref subdsopt) =
    case subdsopt of
        NONE => (case OS.FileSys.readDir ds of
                     NONE => NONE
                   | SOME s =>
                     if s = ".hol" then
                       let val p = OS.Path.concat(dirname, HOLOBJDIR)
                       in
                         if OS.FileSys.isDir p handle OS.SysErr _ => false then
                           let val ds' = OS.FileSys.openDir p
                           in
                             case OS.FileSys.readDir ds' of
                                 NONE => (OS.FileSys.closeDir ds';
                                          OS.FileSys.readDir ds)
                               | SOME s' => (r := SOME ds'; SOME s')
                           end
                         else SOME s
                       end
                     else SOME s)
      | SOME ds' => (case OS.FileSys.readDir ds' of
                         NONE => (r := NONE;
                                  OS.FileSys.closeDir ds';
                                  OS.FileSys.readDir ds)
                       | SOME s => SOME s)

fun chain_readDir objdir (main, sub, chained) =
    case !sub of
        SOME ds' =>
        (case OS.FileSys.readDir ds' of
             NONE => (sub := NONE; OS.FileSys.closeDir ds'; NONE)
           | x => x)
      | NONE =>
        if !chained then NONE
        else
          case OS.FileSys.readDir main of
              SOME ".hol" => chain_readDir objdir (main, sub, chained)
            | SOME s => SOME s
            | NONE =>
              (chained := true;
               if OS.FileSys.isDir objdir handle OS.SysErr _ => false then
                 (sub := SOME (OS.FileSys.openDir objdir);
                  chain_readDir objdir (main, sub, chained))
               else NONE)

fun readDir ({dirname, listing, main, sub, chained} : dirstream) =
    case listing of
        Splice => splice_readDir (dirname, main, sub)
      | Plain => OS.FileSys.readDir main
      | Chain objdir => chain_readDir objdir (main, sub, chained)

fun closeDir ({main, sub, ...} : dirstream) =
    (OS.FileSys.closeDir main;
     case !sub of
         NONE => ()
       | SOME ds' => (OS.FileSys.closeDir ds'; sub := NONE))

fun pushdir d f a0 =
    if OS.FileSys.isDir d handle OS.SysErr _ => false then
      let val d0 = OS.FileSys.getDir()
          val _ = OS.FileSys.chDir d
          val res = f a0 handle e => (OS.FileSys.chDir d0; raise e)
      in
        OS.FileSys.chDir d0;
        res
      end
    else a0


fun read_files_with_objs {dirname} P action a0 =
    case listing_for dirname of
        Splice =>
        let val objdir = dirname ++ HOLOBJDIR
        in
          base_app
            {dirname=dirname}
            (fn s => s = ".hol" orelse P s)
            (fn s => fn a =>
                if s = ".hol" then
                  pushdir
                    objdir
                    (base_app
                       {dirname="."} P
                       (fn s =>
                           action {physdir=objdir, base = s}))
                    a
                else action {physdir=dirname,base=s} a)
            a0
        end
      | Plain =>
        base_app {dirname=dirname} P
                 (fn s => action {physdir=dirname, base=s}) a0
      | Chain objdir =>
        let
          val a1 = base_app {dirname=dirname}
                            (fn s => s <> ".hol" andalso P s)
                            (fn s => action {physdir=dirname, base=s})
                            a0
        in
          pushdir objdir
                  (base_app {dirname="."} P
                            (fn s => action {physdir=objdir, base=s}))
                  a1
        end

fun clean_last () =
    case current_layout () of
        NONE => (OS.FileSys.rmDir HOLOBJDIR handle OS.SysErr _ => ())
      | SOME _ =>
        let val cwd = OS.FileSys.getDir()
            val objdir = objdir_for cwd
        in
          if objdir = cwd then ()
          else OS.FileSys.rmDir objdir handle OS.SysErr _ => ()
        end

end (* struct *)
