(* tools-poly/lsp/lsp_namespace.ML

   Interposed `PolyML.NameSpace.nameSpace` used by the LSP's per-file
   compile.  A "file layer" (six per-kind Binarymap refs) sits on top
   of `PolyML.globalNameSpace`; the compiler both reads through and
   writes into this layered view, so bindings created by the file's
   own compile can be discarded between compiles without affecting
   any state loaded at LSP boot.

   Motivation.  When the user deletes a `val foo = …` from the file
   and recompiles, Poly/ML's `globalNameSpace` retains the old binding
   forever — hovers and later compiles keep resolving `foo`.  The LSP
   `resetForCompile` hook already restores `Context` and
   `Meta.snapshotLoaded`, but has no way to un-register from
   `PolyML.globalNameSpace` (no `#deleteVal`).  Interpose instead: the
   file layer is a per-compile scratchpad we clear on each reset.

   Loaded from `tools-poly/hol.ML` BEFORE `lsp/holide.ML`, since
   `holide.ML`'s `codeFn` will route its enters through this layer.

   Per-thread.  The six tables are thread-local, not global refs,
   because the compiler's name resolution is what a tactic-replaying
   worker needs and two workers must not see each other's bindings: a
   shared layer would make a compile's result depend on which worker
   ran last, which presents as a flaky tactic rather than as a
   threading bug.  A fresh thread starts with an empty layer and
   inherits one explicitly --- `snapshotLayer` captures the calling
   thread's tables and returns a thunk that installs them on whatever
   thread calls it, so the spawner captures and the worker installs. *)

structure LSPNameSpace : sig
  val fileNS : PolyML.NameSpace.nameSpace
  val clearFileLayer : unit -> unit
  (* Return a thunk that restores each of the six kind-tables to
     their current contents.  Used by LSP mid-compile snapshots so a
     resume at dec N re-installs the file-layer state that was live
     at the end of dec N.  Symmetric to `Meta.snapshotLoaded`. *)
  val snapshotLayer : unit -> unit -> unit
end = struct

  (* Mirrors src/portableML/poly/concurrent/ThreadLocal, which cannot be
     loaded here: it writes `Thread.getLocal`, and at this point in the
     boot `Thread` is Poly's outer structure, so the primitives are
     `Thread.Thread.*`.  Same signature, so the two stay swappable. *)
  structure ThreadLocal : sig
    type 'a t
    val new : unit -> 'a t
    val get : 'a t -> 'a option
    val set : 'a t * 'a -> unit
  end = struct
    type 'a t = 'a Universal.tag
    val new = Universal.tag
    val get = Thread.Thread.getLocal
    val set = Thread.Thread.setLocal
  end

  (* a function, not a value: `Binarymap.mkDict String.compare` is an
     application, so binding it with `val` would make it monomorphic
     under the value restriction and unify all six tables *)
  fun emptyTbl () = Binarymap.mkDict String.compare
  fun mkTable () = ThreadLocal.new ()
  (* an untouched thread reads as an empty layer *)
  fun tblGet t = case ThreadLocal.get t of NONE => emptyTbl () | SOME d => d
  fun tblSet t d = ThreadLocal.set (t, d)
  fun tblLookup t k = Binarymap.peek (tblGet t, k)
  fun tblEnter t (k, v) = tblSet t (Binarymap.insert (tblGet t, k, v))
  fun tblAll t = Binarymap.foldr (fn (n, v, acc) => (n, v) :: acc) []
                                 (tblGet t)
  fun tblClear t = tblSet t (emptyTbl ())

  val vTbl = mkTable ()
      : (string, PolyML.NameSpace.Values.value) Binarymap.dict
        ThreadLocal.t
  val tTbl = mkTable ()
      : (string, PolyML.NameSpace.TypeConstrs.typeConstr) Binarymap.dict
        ThreadLocal.t
  val fTbl = mkTable ()
      : (string, PolyML.NameSpace.Infixes.fixity) Binarymap.dict
        ThreadLocal.t
  val sTbl = mkTable ()
      : (string, PolyML.NameSpace.Structures.structureVal) Binarymap.dict
        ThreadLocal.t
  val gTbl = mkTable ()
      : (string, PolyML.NameSpace.Signatures.signatureVal) Binarymap.dict
        ThreadLocal.t
  val nTbl = mkTable ()
      : (string, PolyML.NameSpace.Functors.functorVal) Binarymap.dict
        ThreadLocal.t

  fun overlay lookup all enter t globalLookup globalAll =
    { lookup = fn s => (case lookup t s of NONE => globalLookup s | v => v),
      enter  = fn (s, v) => enter t (s, v),
      (* Union of file layer and global.  In the very common empty-file
         case (start of a compile), skip building a shadow-set entirely
         so `allVal` costs no more than `globalAll ()`.  When the file
         layer is populated, filter out globals that were shadowed. *)
      all    = fn () =>
        case all t of
          [] => globalAll ()
        | file =>
          let val fileNames =
                List.foldl (fn ((n, _), s) => Binaryset.add (s, n))
                           (Binaryset.empty String.compare) file
          in file @ List.filter (fn (n, _) => not (Binaryset.member (fileNames, n)))
                                (globalAll ())
          end }

  val ns = PolyML.globalNameSpace
  val {lookupVal = gLV, enterVal = _, allVal = gAV,
       lookupType = gLT, enterType = _, allType = gAT,
       lookupFix = gLF, enterFix = _, allFix = gAF,
       lookupStruct = gLS, enterStruct = _, allStruct = gAS,
       lookupSig = gLSig, enterSig = _, allSig = gASig,
       lookupFunct = gLFn, enterFunct = _, allFunct = gAFn} = ns

  val v = overlay tblLookup tblAll tblEnter vTbl gLV gAV
  val t = overlay tblLookup tblAll tblEnter tTbl gLT gAT
  val f = overlay tblLookup tblAll tblEnter fTbl gLF gAF
  val s = overlay tblLookup tblAll tblEnter sTbl gLS gAS
  val g = overlay tblLookup tblAll tblEnter gTbl gLSig gASig
  val n = overlay tblLookup tblAll tblEnter nTbl gLFn gAFn

  val fileNS : PolyML.NameSpace.nameSpace = {
    lookupVal = #lookup v, enterVal = #enter v, allVal = #all v,
    lookupType = #lookup t, enterType = #enter t, allType = #all t,
    lookupFix = #lookup f, enterFix = #enter f, allFix = #all f,
    lookupStruct = #lookup s, enterStruct = #enter s, allStruct = #all s,
    lookupSig = #lookup g, enterSig = #enter g, allSig = #all g,
    lookupFunct = #lookup n, enterFunct = #enter n, allFunct = #all n }

  fun clearFileLayer () =
    (tblClear vTbl; tblClear tTbl; tblClear fTbl;
     tblClear sTbl; tblClear gTbl; tblClear nTbl)

  (* Captures this thread's layer; the returned thunk installs it on
     whichever thread calls it.  That is both the mid-compile resume
     (same thread) and the way a worker inherits its spawner's layer. *)
  fun snapshotLayer () = let
    val v = tblGet vTbl val t = tblGet tTbl val f = tblGet fTbl
    val s = tblGet sTbl val g = tblGet gTbl val n = tblGet nTbl
  in
    fn () => (tblSet vTbl v; tblSet tTbl t; tblSet fTbl f;
              tblSet sTbl s; tblSet gTbl g; tblSet nTbl n)
  end

end;
