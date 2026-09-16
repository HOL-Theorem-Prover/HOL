(* ----------------------------------------------------------------------
   Installs `LSPExtension.gotoDefinition', `LSPExtension.hover' and
   `LSPExtension.fixupTheoremLink'.  A plugin records the preterms each
   declaration typechecks; the handlers walk them down to whatever the
   cursor is on.

   Here rather than in `src/coretypes/DefnBase.sml' so that nothing in
   the Holmake-built tree names `LSPExtension', which is what lets the
   Moscow ML build ignore the LSP entirely.  `tools-poly/hol.ML' loads
   the file when the LSP starts; the plugin's `init' then runs at
   `markServerStarted', before the first compile.

   Nothing needs `Meta.load' first: every structure named below is
   already in the heap.
   ---------------------------------------------------------------------- *)

local
(* Inside the `local' so it does not reach the namespace user files
   compile against, which is the server's. *)
open HolKernel
fun get_locn (locn.Loc_Near loc) = get_locn loc
  | get_locn (locn.Loc (locn.LocA start, locn.LocA (l,c))) = SOME(start,(l,c+1))
  | get_locn _ = NONE

datatype preterm_or_pretype = PTM of Preterm.preterm list * Preterm.preterm
                            | PTY of Pretype.pretype

fun leLC (l,c) (l',c') = l <= l' andalso (l <> l' orelse c <= c')
fun fixup a NONE = a
  | fixup a (SOME b) = if #1 a = #1 b then a else b
(* `dl` is how many lines this declaration has moved since the pass
   that recorded it: an edit confined to a `Proof ... QED` body above it
   moves it down the file without moving it sideways, so its columns
   still hold.  Rather than reposition the recorded preterms -- whose
   own `locn`s are read again on the way down, so it would mean
   rebuilding them -- the search runs in the frame they were recorded
   in, and only the answer is brought forward.  It costs two additions
   per hover instead of a tree rebuild per edit. *)
fun backLines dl (l, c) = (l - dl, c)
fun fwdLines dl (l, c) = (l + dl, c)

fun navigateTo lines startTarget endTarget = let
  val startTargetLC0 = LSPExtension.getLineCol lines startTarget
  val endTargetLC0 = LSPExtension.getLineCol lines endTarget
  fun inFrame dl = let
  val startTargetLC = backLines dl startTargetLC0
  val endTargetLC = backLines dl endTargetLC0
  fun navigateToTy ty fail =
    case get_locn locn.Loc_Unknown of (* FIXME Pretype.locn ty *)
      SOME (start, stop) =>
      if leLC start startTargetLC andalso leLC endTargetLC stop then
        SOME (navigateToTyCore (start, stop) ty)
      else fail ()
    | _ => fail ()
  and navigateToTys [] fail = fail ()
    | navigateToTys (ty::tys) fail =
        navigateToTy ty (fn () => navigateToTys tys fail)
  and navigateToTyCore pos ty =
    fixup (pos, PTY ty) (case ty of
      Pretype.Tyop {Args,...} => navigateToTys Args (fn () => NONE)
    | _ => NONE)
  fun navigateTo ls a fail =
    case get_locn (Preterm.locn a) of
      SOME (start, stop) =>
      if leLC start startTargetLC andalso leLC endTargetLC stop then
        SOME (navigateToCore (start, stop) ls a)
      else fail ()
    | _ => fail ()
  and navigateToCore pos ls a =
    fixup (pos, PTM (ls, a)) (case a of
      Preterm.Var {Ty, ...} => navigateToTy Ty (fn () => NONE)
    | Preterm.Const {Ty, ...} => navigateToTy Ty (fn () => NONE)
    | Preterm.Overloaded {Ty, ...} => navigateToTy Ty (fn () => NONE)
    | Preterm.Comb {Rand, Rator, ...} =>
      navigateTo ls Rand (fn () => navigateTo ls Rator (fn () => NONE))
    | Preterm.Abs {Bvar, Body, ...} =>
      navigateTo ls Bvar (fn () => navigateTo (Bvar::ls) Body (fn () => NONE))
    | Preterm.Constrained {Ptm, Ty, ...} =>
      navigateTo ls Ptm (fn () => navigateToTy Ty (fn () => NONE))
    | Preterm.Antiq _ => NONE
    | Preterm.Pattern {Ptm, ...} => navigateTo ls Ptm (fn () => NONE))
  fun navigateToL [] = NONE
    | navigateToL ((start, stop, ptm, env) :: ds) =
      if leLC start startTargetLC andalso leLC endTargetLC stop then
        SOME (navigateToCore (start, stop) [] ptm, env)
      else navigateToL ds
  in navigateToL end
  fun navigateToLL [] = NONE
    | navigateToLL (((start, stop), dl, l) :: ds) =
      if start <= startTarget andalso endTarget <= stop then
        (* the answer comes back in the recorded frame; bring it
           forward, along with `dl` so a caller reading positions out of
           the preterms themselves can do the same *)
        (case inFrame dl l of
           NONE => NONE
         | SOME (((s, e), x), env) =>
           SOME (((fwdLines dl s, fwdLines dl e), x), dl, env))
      else navigateToLL ds
  in navigateToLL end

val checkLog = ThreadLocal.new ()

fun lspTypecheckListener (ptm, env) =
  case ThreadLocal.get checkLog of NONE => () | SOME qs =>
  case get_locn (Preterm.locn ptm) of NONE => () | SOME (start, stop) =>
  ThreadLocal.set (checkLog, (start, stop, ptm, env) :: qs)

fun gotoDefinition tag ({lines, plugins, fromFileLine, ...}, target) = let
  val ds = case LSPExtension.getPluginData (plugins, tag) of
    NONE => raise Empty
  | SOME ds => ds
  val out = case navigateTo lines target target ds of
    SOME ((loc, PTY ty), _, env) => let
    val ty = case Pretype.toTypeM ty env of
                 errormonad.Some (_, ty) => ty
               | _ => raise Empty
    val {Thy, Tyop, ...} = Type.dest_thy_type ty
    (* TODO *)
    val _ = (loc, Thy, Tyop)
    in raise Empty end
  | SOME ((loc, PTM (bvs, tm)), dl, env) => let
    val tm = case Preterm.typecheck NONE tm env of
      errormonad.Some (_, tm) => tm | _ => raise Empty
    val (hd, _) = strip_comb tm
    fun findVar [] = []
      | findVar (bv::bvs) =
        case Preterm.typecheck NONE bv env of
          errormonad.Some (_, tm) =>
          if term_eq tm hd then
            (* read out of the preterm, so in the frame it was recorded
               in -- brought forward like the navigator's own answer *)
            case get_locn (Preterm.locn bv) of
              SOME (s, e) => let
                val tgt = (fwdLines dl s, fwdLines dl e)
              in
                [{uri = NONE, origin = SOME loc, range = tgt, selRange = tgt}]
              end
            | _ => []
          else findVar bvs
        | _ => findVar bvs
    in
      if is_var hd then
        findVar bvs
      else if is_const hd then
        case DefnBase.lookup_userdef hd of
          SOME {thmname, ...} =>
          (case DB.lookup thmname of
            SOME (_, {loc = DB.Located {scriptpath, linenum, ...}, ...}) =>
            [fromFileLine {origin = SOME loc,
              file = holpathdb.subst_pathvars scriptpath,
              line = linenum - 1}]
          | _ => [])
        | NONE => []
      else []
    end
  | _ => raise Empty
  in out end
  handle HOL_ERR _ => [] | Empty => []

fun hover tag ({lines, plugins, ppToString, ...}, (start, stop)) = let
  val ds = case LSPExtension.getPluginData (plugins, tag) of
    NONE => raise Empty
  | SOME ds => ds
  val (range, tm, env) = case navigateTo lines start stop ds of
    SOME ((range, PTM (_, tm)), _, env) => (range, tm, env)
  | _ => raise Empty
  val (range, tm) = case Preterm.typecheck NONE tm env of
    errormonad.Some (_, tm) => (range, tm)
  | _ => raise Empty
  fun f () = let
    val typp = Parse.pp_type_without_colon (type_of tm)
    val tmpp = with_flag (Globals.max_print_depth, 4) Parse.pp_term tm
    open HOLPP
  in
    PrettyBlock(0, true, [], [tmpp, PrettyString ":", PrettyBreak(1, 2), typp])
  end
  val s =
      with_flag (Parse.current_backend, PPBackEnd.raw_terminal)
                (ppToString o f) ()
  in [{range = SOME range, markdown = s}] end
  handle HOL_ERR _ => [] | Empty => []

fun lastIndexOf c s = let
  fun go i = if i = 0 then ~1 else case i - 1 of i' =>
    if c = String.sub (s, i') then i' else go i'
  in go (String.size s) end

in

val _ = LSPExtension.fixupTheoremLink := (fn {uri, text, start, stop} => let
  val written = String.substring (text, start, stop - start)
  (* A qualified reference -- `finite_mapTheory.FRANGE_DEF' -- spans the
     whole dotted name, and the DB knows the theorem by its own name.
     Without this the lookup fails and the jump lands in the generated
     signature rather than in the script the theorem is proved in. *)
  val id = String.extract (written, lastIndexOf #"." written + 1, NONE)
  val basename = String.extract (uri, lastIndexOf #"/" uri + 1, NONE)
  (* no extension is possible -- Poly names the unit it is compiling ""
     -- and `SOME ~1` would raise `Subscript` *)
  val stem = case lastIndexOf #"." basename of
                 ~1 => basename
               | i => String.extract (basename, 0, SOME i)
  in
    if 6 <= size stem andalso
       String.extract (stem, size stem - 6, NONE) = "Theory"
    then
      case DB.lookup{Name=id, Thy=String.extract(stem,0,SOME(size stem - 6))} of
        SOME (_, {loc = DB.Located {scriptpath, linenum, ...}, ...}) =>
        SOME {file = holpathdb.subst_pathvars scriptpath, line = linenum - 1}
      | _ => NONE
    else NONE
  end)

val _ = LSPExtension.registerPlugin true {
  name = "DefnBase",
  init = fn tag => (
    Listener.add_listener
      Preterm.typecheck_listener
      ("LSP", lspTypecheckListener)
      handle HOL_ERR _ =>
        !WARNING_outstream "<<warning: failed to add typecheck listener>>\n";
    LSPExtension.gotoDefinition := gotoDefinition tag;
    LSPExtension.hover := hover tag),
  beforeCompile = fn () => ThreadLocal.set (checkLog, []),
  afterCompile = fn (r, x) =>
    case ThreadLocal.get checkLog of
      SOME (l as _::_) => let
      val x = case x of SOME x => x | NONE => []
      in SOME ((r, 0, l) :: x) end
    | _ => x,
  (* A declaration this pass did not re-run keeps everything recorded
     about it; only where it sits has changed.  Its byte range is a
     pair of integers and moves now; its preterms are left where they
     were and the search moves to meet them (see `navigateTo`). *)
  reuseFrom = fn {fromByte, bytes, lines} => fn old => fn new => let
    val old = case old of SOME l => l | NONE => []
    val new = case new of SOME l => l | NONE => []
    val carried =
      List.foldr
        (fn ((r as (start, stop), dl, l), acc) =>
            if start >= fromByte
            then ((start + bytes, stop + bytes), dl + lines, l) :: acc
            else acc)
        [] old
    (* newest-first, and the carried declarations are the later ones *)
    in case carried @ new of [] => NONE | l => SOME l end }
end;
