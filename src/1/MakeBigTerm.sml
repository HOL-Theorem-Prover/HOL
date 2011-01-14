structure MakeBigTerm =
struct

open HolKernel Random boolSyntax

fun gen_ty gen = let
  val n = Random.random gen
in
  if n < 0.1 then gen_ty gen --> gen_ty gen
  else if n < 0.5 then bool
  else if n < 0.9 then alpha
  else beta
end

fun gen_var gen bvars tyr = let
  val bvs = case tyr of NONE => bvars
                      | SOME ty => List.filter (fn t => type_of t = ty) bvars
in
  if Random.random gen < 0.5 andalso not (null bvs) then
    List.nth (bvs, Random.range(0, length bvs) gen)
  else let
      val ty = case tyr of NONE => gen_ty gen | SOME ty => ty
    in
      mk_var((if can dom_rng ty then "f" else "x")  ^
             Int.toString (Random.range(0,25) gen), ty)
    end
end

fun gen_term0 gen bvars sz tyrequired = let
  val gt = gen_term0 gen bvars
  fun rmk_comb sz tyr = let
    val szs as (sz1, sz2) = (sz div 2, sz - sz div 2)
    val (fsz, xsz) = if sz1 = sz2 then szs else
                     if Random.random gen < 0.5 then (sz1, sz2) else (sz2, sz1)
    val dom_ty = gen_ty gen
    val rng_ty = case tyr of NONE => gen_ty gen  | SOME ty => ty
  in
    mk_comb(gt fsz (SOME (dom_ty --> rng_ty)), gt xsz (SOME dom_ty))
  end
in
  case tyrequired of
    NONE => let
      val n = Random.random gen
    in
      if sz <= 1 then
        if n < 0.1 then boolSyntax.F
        else if n < 0.2 then boolSyntax.T
        else if n < 0.3 then mk_arb (gen_ty gen)
        else gen_var gen bvars NONE
      else if sz = 2 then
        if n < 0.7 then rmk_comb 2 NONE
        else let
            val bv = gen_var gen [] NONE
          in
            mk_abs(bv, gen_term0 gen (bv::bvars) 1 NONE)
          end
      else if n < 0.4 then let
          val fsz = (sz - 1) div 2
          val xsz = (sz - 1) - fsz
          val opn = if n < 0.3 then mk_conj else mk_disj
        in
          opn(gt fsz (SOME bool), gt xsz (SOME bool))
        end
      else if n < 0.75 then rmk_comb sz NONE
      else let
          val bv = gen_var gen [] NONE
        in
          mk_abs(bv, gen_term0 gen (bv::bvars) (sz - 1) NONE)
        end
    end
  | SOME ty => let
      val n = Random.random gen
    in
      if sz = 1 then
        if ty = bool then
          if n < 0.15 then T
          else if n < 0.30 then F
          else gen_var gen bvars tyrequired
        else if n < 0.3 then mk_arb ty
        else gen_var gen bvars tyrequired
      else
        case Lib.total dom_rng ty of
          NONE =>
          if ty = bool andalso sz > 2 andalso n < 0.4 then let
              val opn = if n < 0.3 then mk_conj else mk_disj
              val arg1sz = (sz - 1) div 2
              val arg2sz = (sz - 1) - arg1sz
            in
              opn (gt arg1sz (SOME bool), gt arg2sz (SOME bool))
            end
          else rmk_comb sz tyrequired
        | SOME (d, r) =>
          if n < 0.25 then let
              val bv = gen_var gen [] (SOME d)
            in
              mk_abs(bv, gen_term0 gen (bv::bvars) (sz - 1) (SOME r))
            end
          else rmk_comb sz tyrequired
    end
end

fun gen_term i sz = gen_term0 (Random.newgenseed i) [] sz NONE

end
