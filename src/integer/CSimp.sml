structure CSimp :> CSimp =
struct

open HolKernel boolLib CooperThms QConv

val (Type,Term) = Parse.parse_from_grammars boolTheory.bool_grammars

val simple_disj_congruence =
  tautLib.TAUT_PROVE (Term`!p q r. (~p ==> (q = r)) ==>
                                   (p \/ q = p \/ r)`)
val simple_conj_congruence =
  tautLib.TAUT_PROVE (Term`!p q r. (p ==> (q = r)) ==>
                                   (p /\ q = p /\ r)`)
infix THENC ORELSEC |->

val lhand = rand o rator

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val BINOP_CONV = BINOP_QCONV
val ALL_CONV = ALL_QCONV

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

fun disj_cong0 c t = let
  val (d1, d2) = dest_disj t
  val notd1_t = mk_neg d1
  val notd1_thm = EQF_INTRO (ASSUME notd1_t)
  val d1_thm0 = AP_TERM boolSyntax.negation notd1_thm
  val d1_thm =
      CONV_RULE (LAND_CONV c THENC RAND_CONV (REWRITE_CONV [])) d1_thm0
  val d2_rewritten = DISCH notd1_t (REWRITE_CONV [notd1_thm, d1_thm] d2)
in
  K (MATCH_MP simple_disj_congruence d2_rewritten) THENC
  TRY_CONV (REWR_CONV T_or_r ORELSEC REWR_CONV F_or_r)
end t

fun disj_cong c =
    REWR_CONV T_or_l ORELSEC REWR_CONV F_or_l ORELSEC disj_cong0 c

fun conj_cong0 c t = let
  val (c1, c2) = dest_conj t
  val c1_thm = EQT_INTRO (ASSUME c1)
  val c1_neg0 = AP_TERM boolSyntax.negation c1_thm
  val c1_neg =
      CONV_RULE (LAND_CONV c THENC RAND_CONV (REWRITE_CONV [])) c1_neg0
  val c2_rewritten = DISCH c1 (REWRITE_CONV [c1_thm, c1_neg] c2)
in
  K (MATCH_MP simple_conj_congruence c2_rewritten) THENC
  TRY_CONV (REWR_CONV T_and_r ORELSEC REWR_CONV F_and_r)
end t

fun conj_cong c =
    REWR_CONV T_and_l ORELSEC REWR_CONV F_and_l ORELSEC conj_cong0 c

fun IFP is c tm = if is tm then c tm else ALL_CONV tm

fun csimp c tm = let
in
  if is_disj tm then
    if has_atom dest_disj is_conj tm then
      find_atom DISJ_ASSOC DISJ_COMM dest_disj is_conj THENC
      disj_cong c THENC IFP is_disj (RAND_CONV (csimp c))
    else BINOP_CONV (csimp c)
    else if is_conj tm then
      if has_atom dest_conj is_disj tm then
        find_atom CONJ_ASSOC CONJ_COMM dest_conj is_disj THENC
        conj_cong c THENC IFP is_conj (RAND_CONV (csimp c))
      else BINOP_CONV (csimp c)
    else ALL_CONV
end tm

end (* struct *)
