signature CooperShell = sig
  include Abbrev

  val phase6_CONV : conv

  val pure_goal : conv
  val decide_pure_presburger_term : conv
end;
