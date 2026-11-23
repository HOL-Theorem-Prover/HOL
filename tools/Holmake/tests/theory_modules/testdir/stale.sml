(* Decoded data whose parents are canonical but whose references aren't
   current is refused before anything is registered, and the context
   stays usable.  moduleA stays canonical after a rollback to before its
   load, since the canonical set isn't part of the context, but its
   entries are gone.  Run in a process of its own, without a module
   cache; exits with failure, saying why, if any of this doesn't hold. *)
open HolKernel Parse boolLib bossLib;
fun fail s = (TextIO.output (TextIO.stdErr, "stale: " ^ s ^ "\n");
              OS.Process.exit OS.Process.failure);
use "theory_hash.sml";
fun raises f = (ignore (f ()); false) handle _ => true;

val before_a = Context.snapshot ();
val _ = load "moduleATheory";
val _ = TheoryReader.is_canonical "moduleA" orelse
        fail "moduleA loaded without canonical stamps";
val with_a = Context.snapshot ();
val decoded =
    case TheoryReader.capture_decoded load "moduleBTheory" of
        (_, SOME d) => d
      | (_, NONE) => fail "moduleB's load decoded nothing";
fun has_data () =
    List.exists (fn ty => isSome (Theory.LoadableThyData.segment_data
                                    {thy = "moduleB", thydataty = ty}))
                ["compute", "simp.deltas"];
val _ = has_data () orelse fail "moduleB's load added no theory data";

val _ = Context.restore before_a;
val _ = TheoryReader.is_canonical "moduleA" orelse
        fail "the rollback made moduleA non-canonical";
val _ = not (TheoryReader.refs_current decoded) orelse
        fail "references to moduleA's removed entries count as current";
val _ = not (TheoryReader.register_decoded (theory_hash "moduleB") decoded)
        orelse fail "decoded data with stale references was registered";
val _ = raises (fn () => prim_mk_const {Thy = "moduleB", Name = "b_value"})
        orelse fail "the refused registration added a constant";
val _ = raises (fn () =>
                   Theory.link_parents ("moduleChild", "")
                                       [("moduleB", theory_hash "moduleB")])
        orelse fail "the refused registration linked the theory";
val _ = null (DB.thy "moduleB") orelse
        fail "the refused registration bound theorems";
val _ = not (has_data ()) orelse
        fail "the refused registration added theory data";

(* Back in a context with moduleA, its other child loads *)
val _ = Context.restore with_a;
val _ = load "moduleCTheory";
val _ = Thm.is_sealed "moduleC" orelse fail "moduleC's load didn't seal it";
