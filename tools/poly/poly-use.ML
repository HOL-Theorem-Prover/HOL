(* this is an -*- sml -*- file *)
structure PolyGeneral = General
structure PolyArray = Array
structure PolySubstring = Substring
structure PolyWord8Vector = Word8Vector;

use "tools/poly/PP.sig";
use "tools/poly/PP.sml";

(* awfulness to make the environment look like Moscow ML's *)
structure Meta = struct fun loaded () = [] fun load s = () end
structure General = struct
  open PolyGeneral
  type ppstream = PP.ppstream
end
open General
structure Array = struct
  open PolyArray
  fun extract (a, i, jopt) =
    ArraySlice.vector(ArraySlice.slice(a,i,jopt))
  fun copyVec {di,dst,len,src,si} =
    let val v = VectorSlice.vector(VectorSlice.slice(src,si,len))
    in
      PolyArray.copyVec {di = di, dst = dst, src = v}
    end
end;

structure Word8Vector = struct
  open PolyWord8Vector
  fun mapi f (v,i,jopt) = let
    open Word8VectorSlice
  in
    PolyWord8Vector.mapi f (vector(slice(v,i,jopt)))
  end
  fun foldri f b (v,i,jopt) = let
    open Word8VectorSlice
  in
    PolyWord8Vector.foldri f b (vector(slice(v,i,jopt)))
  end
end;
structure Substring = struct
  open PolySubstring
  val all = PolySubstring.full
end;

structure PreProcess = OS.Process;
structure Path = OS.Path
structure Process = OS.Process
structure FileSys = OS.FileSys;
exception Interrupt = SML90.Interrupt

val qdir = ref "src";
fun quse s = (use (!qdir ^ s ^ ".sig"); use (!qdir ^ s ^ ".sml"))

(* systeml *)
val _ = qdir := "tools/Holmake/";
quse "Systeml";   (* GENERATED! *)

(* poly *)
val _ = qdir := "tools/poly/";
quse "Random";
quse "Listsort";
quse "Binarymap";
quse "Susp";

(* portableML *)
val _ = qdir := "src/portableML/";
quse "Arbnum";
use "tools/poly/Portable.sig";
use "tools/poly/Portable.sml";
quse "Arbint";
quse "Arbrat";
quse "Randomset";
quse "Redblackmap";
quse "Redblackset";
quse "PIntMap";
(* don't really need
quse "Profile";
*)

(* prekernel *)
val _ = qdir := "src/prekernel/";
quse "locn";
quse "Globals";
quse "Feedback";
use "src/prekernel/Lib.sig";
use "tools/poly/Lib.sml";
quse "Count";
quse "HOLset";
use "src/prekernel/RestrictedTag-sig.sml";
quse "Tag";
quse "HOLset";
quse "Lexis";

(* kernel *)
val _ = qdir := "src/experimental-kernel/";
quse "Type";
use "src/experimental-kernel/RestrictedTerm-sig.sml";
quse "Term";
quse "Thm";
quse "SharingTables";
quse "RawParse";
quse "TheoryPP";
quse "Theory";
quse "Definition";
quse "Net";
use "src/experimental-kernel/HolKernel.sml";
use "src/experimental-kernel/Overlay.sml";

(* parsing and printing *)
val _ = qdir := "src/parse/";
quse "optmonad";
quse "stmonad";
quse "seq";
quse "seqmonad";
quse "Pretype";
quse "Absyn";
quse "GrammarSpecials";
quse "HOLgrammars";
quse "CharSet";
quse "HOLtokens";
quse "Literal";
quse "MLstring";
quse "base_tokens";
use "src/parse/base_lexer.sml";  (* GENERATED! *)
quse "Overload";
quse "TypeNet";
quse "qbuf";
quse "type_tokens";
quse "type_grammar";
quse "parse_type";
quse "Preterm";
quse "term_pp_types";
quse "term_tokens";
quse "term_grammar";
quse "parse_term";
quse "Parse_support";
(* pretty-printing *)
quse "type_pp";
quse "term_pp";
quse "Parse";
quse "ParseDatatype";
quse "Hol_pp";

(* install pretty-printers *)
fun pp2polypp (f :  ppstream -> 'a -> unit)
              (putString : string -> unit,
               beginBlock : int * bool -> unit,
               spaceBlock : int * int -> unit,
               endBlock : unit -> unit)
              (dpth_limit : int)
              recursive_print
              (e : 'a) = putString (f e)
fun dq (f : 'a -> string) x = "``" ^ f x ^ "``"

val _ = PolyML.install_pp (pp2polypp (dq Parse.term_to_string))
val _ = PolyML.install_pp (pp2polypp Parse.thm_to_string)
val _ = PolyML.install_pp (pp2polypp (dq Parse.type_to_string))


(* bools *)
val _ = qdir := "src/bool/";



(* ----------------------------------------------------------------------
    A version of "use" that filters quotations. The native PolyML version
    of "use" is found in the "PolyML" structure.
   ---------------------------------------------------------------------- *)

local
  (* used to stand for "has double quote", but the same analysis is necessary
     even for files that contain single quotes because of the special
     treatment that the filter gives to things like `s1 ^ s2`
  *)
  fun has_dq file =
      let
        val istrm = TextIO.openIn file
        fun loop() =
            case TextIO.input1 istrm of
              NONE => false
            | SOME #"`" => true
            | SOME _ => loop()
      in
        loop() before TextIO.closeIn istrm
      end handle IO.Io _ => false
  infix ++
  fun p1 ++ p2 = Path.concat (p1, p2)
  open Systeml
  fun unquote_to file1 file2 =
      systeml [HOLDIR ++ "bin" ++ "unquote", file1, file2]
in
fun use s =
  if has_dq s then
    let
      val filename = FileSys.tmpName()^".hol"
    in
      if Process.isSuccess (unquote_to s filename) then
        (PolyML.use filename; FileSys.remove filename)
        handle e => (FileSys.remove filename handle _ => (); raise e)
      else (TextIO.output(TextIO.stdOut,
                          ("Failed to translate file: "^s^"\n"));
            raise Fail "use")
    end
  else PolyML.use s
end;

(* quse needs redefining too *)
fun quse s = (use (!qdir ^ s ^ ".sig"); use (!qdir ^ s ^ ".sml"))


val _ = qdir := "src/bool/";
quse "DB";
use "src/bool/boolScript.sml";

use "boolTheory.sig";

structure boolTheory :> boolTheory = struct
  open boolScript
  val DISJ_COMM = DISJ_SYM
  val CONJ_COMM = CONJ_SYM
  val itself_TY_DEF = DB.definition "itself_TY_DEF"
  val bool_grammars = Parse.current_lgrms()
end;

quse "boolSyntax";
quse "DefnBase";
quse "Abbrev";
quse "Rsyntax";
quse "Drule";

open Portable; (* need to see frag type constructor *)
quse "Tactical";
quse "Psyntax";
quse "Thm_cont";
quse "Conv";
quse "Pmatch";
quse "simpfrag";
quse "Tactic";
quse "Rewrite";
quse "Prim_rec";
quse "TypeBasePure";
quse "TypeBase";
quse "ConstMapML";
quse "Ho_Net";
quse "Ho_Rewrite";
quse "EmitML";
use "src/bool/boolLib.sml";
quse "dep_rewrite";
quse "Mutual";

(* goalstack *)
val _ = qdir := "src/goalstack/";
quse "Bwd";
quse "History";
quse "GoalstackPure";
quse "goalstackLib";

val _ = PolyML.install_pp
            (pp2polypp (PP.pp_to_string 75 goalstackLib.pp_goalstack))
val _ = PolyML.install_pp
            (pp2polypp (PP.pp_to_string 75 goalstackLib.pp_proofs))
open HolKernel Parse boolLib goalstackLib;

PolyML.export("polyhol.bare", PolyML.rootFunction);
