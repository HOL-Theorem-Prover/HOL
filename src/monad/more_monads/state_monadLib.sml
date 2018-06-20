structure state_monadLib :> state_monadLib =
struct

open HolKernel Parse boolLib numLib simpLib
open state_transformerTheory

structure Parse = struct
  open Parse
  val (Type, Term) =
    parse_from_grammars state_transformerTheory.state_transformer_grammars
end
open Parse

val add_state_monad_compset =
  let
    val cnv =
      SIMP_CONV std_ss
         [Once state_transformerTheory.FOR_def,
          Once state_transformerTheory.MWHILE_DEF,
          state_transformerTheory.MMAP_DEF,
          state_transformerTheory.MCOMP_DEF,
          state_transformerTheory.JOIN_DEF,
          state_transformerTheory.FOREACH_def,
          state_transformerTheory.READ_def,
          state_transformerTheory.WRITE_def,
          state_transformerTheory.NARROW_def,
          state_transformerTheory.WIDEN_def,
          state_transformerTheory.UNIT_DEF,
          state_transformerTheory.BIND_DEF,
          state_transformerTheory.EXT_DEF,
          state_transformerTheory.IGNORE_BIND_DEF,
          state_transformerTheory.sequence_def,
          state_transformerTheory.mapM_def,
          boolTheory.LET_DEF, boolTheory.COND_RATOR, pairTheory.UNCURRY_DEF,
          combinTheory.o_DEF,
          combinTheory.I_THM
          |> Q.SPEC `x`
          |> Conv.CONV_RULE (Conv.RAND_CONV (Conv.UNBETA_CONV ``x:'a``))
          |> Drule.GEN_ALL
          |> Drule.EXT] o
      Feedback.trace ("notify type variable guesses", 0) Parse.Term
  in
    computeLib.add_thms
      (pairTheory.UNCURRY_DEF ::
       List.map cnv
         [
          `UNIT v s`,
          `BIND f g s`,
          `EXT f g s`,
          `mapM f s`,
          `MMAP f g s`,
          `MCOMP f g s x`,
          `JOIN f s`,
          `FOREACH ([], f) s`,
          `FOREACH (h :: t, f) s`,
          `FOR (i, j, f) s`,
          `READ f s`,
          `WRITE f s`,
          `NARROW v f s`,
          `WIDEN f (s1, s2)`,
          `MWHILE f g s`,
          `IGNORE_BIND f g s`,
          `sequence l s`
         ]
      )
  end

end
