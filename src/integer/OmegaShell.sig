signature OmegaShell =
sig
  include Abbrev

  val normalise                : conv
  val decide_strategy          : conv
  val decide_closed_presburger : conv

end;
