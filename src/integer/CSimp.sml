structure CSimp :> CSimp =
struct

open HolKernel boolLib CooperThms intSyntax integerTheory int_arithTheory

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
end
open Parse

val lhand = rand o rator

fun has_atom dthis is_other t = let
  val (t1, t2) = dthis t
in
  has_atom dthis is_other t1 orelse has_atom dthis is_other t2
end handle HOL_ERR _ => not (is_other t)

fun find_atom ASSOC COMM dthis is_other t = let
  val find_atom = find_atom ASSOC COMM dthis is_other
  val is_this = can dthis
  fun move_atom_from_left t =
      if is_this (lhand t) then REWR_CONV (GSYM ASSOC) t
      else ALL_CONV t
  val move_atom_from_right = REWR_CONV COMM THENC move_atom_from_left
  val (t1, t2) = dthis t
in
  if has_atom dthis is_other t1 then
    LAND_CONV find_atom THENC move_atom_from_left
  else
    RAND_CONV find_atom THENC move_atom_from_right
end t handle (e as HOL_ERR _) => if is_other t then raise e else ALL_CONV t

datatype matchmode = NOMATCH | NEGATED | POSITIVE
fun compare_pair accmode eqnp tp =
    if rand eqnp <> rand tp then NOMATCH
    else let
        val e_coeff = lhand eqnp
        val t_coeff = lhand tp
        val (e_negged, e_core) =
            if is_negated e_coeff then (true, rand e_coeff)
            else (false, e_coeff)
        val (t_negged, t_core) =
            if is_negated t_coeff then (true, rand t_coeff)
            else (false, t_coeff)
        val possible_mode =
            if e_negged <> t_negged then NEGATED else POSITIVE
      in
        if accmode = NOMATCH orelse possible_mode = accmode then
          if e_core = t_core then possible_mode
          else NOMATCH
        else NOMATCH
      end
fun determine_match accmode eqnpart tpart =
    case (is_plus eqnpart, is_plus tpart) of
      (true, true) => let
      in
        case compare_pair accmode (rand eqnpart) (rand tpart) of
          NOMATCH => NOMATCH
        | newacc => determine_match newacc (lhand eqnpart) (lhand tpart)
      end
    | (false, false) => compare_pair accmode eqnpart tpart
    | _ => NOMATCH

val cvar = mk_var("c", intSyntax.int_ty)
val xvar = mk_var("x", intSyntax.int_ty)
val yvar = mk_var("y", intSyntax.int_ty)
val gv = genvar int_ty
val handle_negs = PURE_REWRITE_RULE [INT_NEG_ADD, INT_NEG_LMUL, INT_NEGNEG,
                                     INT_NEG_0]
fun EQRWT eqn = let
  val (varpart, numpart) = dest_plus (rand (concl eqn))
  val eq1 = MP (INST [cvar |-> varpart, xvar |-> numpart, yvar |-> gv]
                     eq_context_rwt1) eqn
  val eq2 = handle_negs (MP (INST [cvar |-> varpart, xvar |-> numpart,
                                   yvar |-> gv]
                                  eq_context_rwt2) eqn)
in
  (fn t =>
      if is_eq t then
        case determine_match NOMATCH varpart (lhand (rand t)) of
          NOMATCH => ALL_CONV t
        | POSITIVE => (LAND_CONV (K eqn) THENC REWR_CONV INT_EQ_LADD THENC
                       CooperMath.REDUCE_CONV) t
        | NEGATED => raise Fail "EQRWT : should never happen"
      else if is_leq t then
        case determine_match NOMATCH varpart (lhand (rand t)) of
          NOMATCH => ALL_CONV t
        | POSITIVE => (K (INST [gv |-> rand (rand t)] eq1) THENC
                       CooperMath.REDUCE_CONV) t
        | NEGATED => (K (INST [gv |-> rand (rand t)] eq2) THENC
                      CooperMath.REDUCE_CONV) t
      else ALL_CONV t)
end


fun LTRWT ltthm = let
  val (varpart, numpart) = dest_plus (rand (concl ltthm))
  val n = int_of_term numpart
  val rwt1 = MP (INST [cvar |-> varpart, xvar |-> numpart,
                       yvar |-> gv] le_context_rwt1) ltthm
  val rwt2 = handle_negs (MP (INST [cvar |-> varpart, xvar |-> numpart,
                                    yvar |-> gv] le_context_rwt2) ltthm)
  val rwt3 = MP (INST [cvar |-> varpart, xvar |-> numpart,
                       yvar |-> gv] le_context_rwt3) ltthm
  val rwt4 = handle_negs (MP (INST [cvar |-> varpart, xvar |-> numpart,
                                    yvar |-> gv] le_context_rwt4) ltthm)
  val rwt5 = CONV_RULE (RAND_CONV (TRY_CONV OmegaMath.leaf_normalise))
                       (handle_negs (MP (INST [cvar |-> varpart,
                                               xvar |-> numpart]
                                              le_context_rwt5)
                                        ltthm))
in
  (fn t =>
      if is_eq t then
        case determine_match NOMATCH varpart (lhand (rand t)) of
          NOMATCH => ALL_CONV t
        | POSITIVE => let val tnumpart = rand (rand t)
                      in
                        if Arbint.<(n, int_of_term tnumpart) then
                          MP (CONV_RULE (LAND_CONV CooperMath.REDUCE_CONV)
                                        (INST [gv |-> tnumpart] rwt3)) TRUTH
                        else ALL_CONV t
                      end
        | NEGATED => let val tnumpart = rand (rand t)
                     in
                       if Arbint.<(n, Arbint.~(int_of_term tnumpart)) then
                         MP (CONV_RULE (LAND_CONV CooperMath.REDUCE_CONV)
                                       (INST [gv |-> tnumpart] rwt4)) TRUTH
                       else ALL_CONV t
                     end
      else if is_leq t then
        case determine_match NOMATCH varpart (lhand (rand t)) of
          NOMATCH => ALL_CONV t
        | POSITIVE => let val tnumpart = rand (rand t)
                      in
                        if Arbint.<=(n, int_of_term tnumpart) then
                          MP (CONV_RULE (LAND_CONV CooperMath.REDUCE_CONV)
                                        (INST [gv |-> tnumpart] rwt1)) TRUTH
                        else
                          ALL_CONV t
                      end
        | NEGATIVE => let val tnumpart = rand (rand t)
                          open Arbint
                      in
                        case compare(int_of_term tnumpart, ~ n) of
                          LESS => MP (CONV_RULE
                                        (LAND_CONV CooperMath.REDUCE_CONV)
                                        (INST [gv |-> tnumpart] rwt2))
                                     TRUTH
                        | EQUAL => rwt5
                        | GREATER => ALL_CONV t
                      end
      else ALL_CONV t)
end


fun disj_cong0 t = let
  val (d1, d2) = dest_disj t
  val notd1_t = mk_neg d1
  val notd1_th = ASSUME notd1_t
  val d2_rewritten =
      if is_neg d1 then
        DISCH notd1_t
              (REWRITE_CONV [CONV_RULE (REWR_CONV NOT_NOT_P) notd1_th] d2)
      else if is_divides d1 orelse is_eq d1 then
        DISCH notd1_t (REWRITE_CONV [notd1_th] d2)
      else let
          val notd1_thm = CONV_RULE OmegaMath.leaf_normalise notd1_th
        in
          DISCH notd1_t (CooperMath.BLEAF_CONV (op THENC) (LTRWT notd1_thm) d2)
        end
in
  K (MATCH_MP simple_disj_congruence d2_rewritten) THENC
  TRY_CONV (REWR_CONV T_or_r ORELSEC REWR_CONV F_or_r)
end t

val disj_cong =
    REWR_CONV T_or_l ORELSEC REWR_CONV F_or_l ORELSEC disj_cong0

fun conj_cong0 t = let
  val (c1, c2) = dest_conj t
  val c1_thm = ASSUME c1
  val c2_rewritten =
      if is_eq c1 then
        DISCH c1 (CooperMath.BLEAF_CONV (op THENC) (EQRWT c1_thm) c2)
      else if is_leq c1 then
        DISCH c1 (CooperMath.BLEAF_CONV (op THENC) (LTRWT c1_thm) c2)
      else
        DISCH c1 (REWRITE_CONV [EQT_INTRO c1_thm
                                handle HOL_ERR _ => EQF_INTRO c1_thm] c2)
in
  K (MATCH_MP simple_conj_congruence c2_rewritten) THENC
  TRY_CONV (REWR_CONV T_and_r ORELSEC REWR_CONV F_and_r)
end t

val conj_cong =
    REWR_CONV T_and_l ORELSEC REWR_CONV F_and_l ORELSEC conj_cong0

fun IFP is c tm = if is tm then c tm else ALL_CONV tm

fun csimp tm = let
in
  if is_disj tm then
    if has_atom dest_disj is_conj tm then
      find_atom DISJ_ASSOC DISJ_COMM dest_disj is_conj THENC
      disj_cong THENC IFP is_disj (RAND_CONV csimp)
    else BINOP_CONV csimp
  else if is_conj tm then
    if has_atom dest_conj is_disj tm then
      find_atom CONJ_ASSOC CONJ_COMM dest_conj is_disj THENC
      conj_cong THENC IFP is_conj (RAND_CONV csimp)
    else BINOP_CONV csimp
  else ALL_CONV
end tm

end (* struct *)
