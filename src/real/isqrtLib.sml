structure isqrtLib :> isqrtLib =
struct

open HolKernel Parse boolLib
open transcSyntax

local
   fun isqrt_square i =
      let
         val sqr = Arbnum.isqrt i
      in         if Arbnum.* (sqr, sqr) = i
            then realSyntax.mk_injected (numLib.mk_numeral sqr)
         else raise ERR "isqrt" "not a square"
      end
   val sqrt =
      Lib.total (isqrt_square o numLib.dest_numeral o realSyntax.dest_injected)
   fun mk_ge_thm n = Thm.SPEC (realSyntax.dest_injected n) realTheory.REAL_POS
   fun sqrt_thm thm =
      thm |> Drule.MATCH_MP transcTheory.POW_2_SQRT
          |> Conv.CONV_RULE (Conv.LAND_CONV (Conv.RAND_CONV bossLib.EVAL))
   val sqrt_conv = Conv.REWR_CONV o sqrt_thm
in
   fun iSQRT_COMPUTE_CONV tm =
      let
         val r = transcSyntax.dest_sqrt tm
      in
         case Lib.total realSyntax.dest_div r of
            SOME (n, d) =>
              (case (sqrt n, sqrt d) of
                  (SOME rn, SOME rd) =>
                      let
                         (* for testing
                           val SOME (n, d) = Lib.total realSyntax.dest_div r
                           val SOME rn = sqrt n
                           val SOME rd = sqrt d
                         *)
                         val x = mk_ge_thm n
                         val y = mk_ge_thm d
                         val rx = mk_ge_thm rn
                         val ry = mk_ge_thm rd
                         val rwt1 =
                            Drule.MATCH_MP transcTheory.SQRT_DIV (Thm.CONJ x y)
                      in
                         (Conv.REWR_CONV rwt1
                          THENC Conv.FORK_CONV (sqrt_conv rx, sqrt_conv ry)) tm
                      end
                | _ => raise ERR "iSQRT_COMPUTE_CONV" "")
          | NONE =>
             (case sqrt r of
                 SOME rn => sqrt_thm (mk_ge_thm rn)
               | _ => raise ERR "iSQRT_COMPUTE_CONV" "")
      end
end

val () = computeLib.add_convs [(transcSyntax.sqrt_tm, 1, iSQRT_COMPUTE_CONV)]

end
