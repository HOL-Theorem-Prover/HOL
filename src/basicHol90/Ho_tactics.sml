(*---------------------------------------------------------------------------
 * Pop the first assumption that matches the pattern and give it to
 * a function (tactic).
 *---------------------------------------------------------------------------*)
open HolKernel Drule

infix |->

fun match_with_constants constants pat_tm actual_tm = let
  val (tm_inst, ty_inst) = Ho_match.match_term [] pat_tm actual_tm
  val bound_vars = map #2 tm_inst
in
  null (intersect constants bound_vars)
end handle HOL_ERR _ => false



fun PAT_ASSUM pat thfun (asl, w) = let
  val possible_matches = List.filter (can (Ho_match.match_term [] pat)) asl
in
  case possible_matches of
    [] => raise HOL_ERR {origin_structure = "Ho_tactics",
                         origin_function = "PAT_ASSUM",
                         message = "No assumptions match pattern"}
  | [x] => let
      val (ob, asl') = Lib.pluck (fn t => t = x) asl
    in
      thfun (ASSUME ob) (asl', w)
    end
  | _ => let
      val fvars = free_varsl (w::asl)
      val (ob,asl') = Lib.pluck (match_with_constants fvars pat) asl
    in
      thfun (ASSUME ob) (asl',w)
    end
end

