signature CooperThms = sig

  include Abbrev
  val elim_le : thm
  val elim_gt : thm
  val elim_ge : thm
  val move_add : thm

  val T_and_l : thm
  val T_and_r : thm
  val F_and_l : thm
  val F_and_r : thm
  val T_or_l : thm
  val T_or_r : thm
  val F_or_l : thm
  val F_or_r : thm

  val NOT_NOT_P : thm
  val NOT_OR : thm
  val NOT_AND : thm

  val NOT_AND_IMP : thm

  val DISJ_NEQ_ELIM : thm
  val cpEU_THM : thm

  val simple_disj_congruence : thm
  val simple_conj_congruence : thm

end
