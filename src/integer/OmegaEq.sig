signature OmegaEq =
sig
  include Abbrev
  val OmegaEq : term -> thm

end;

(*
    [OmegaEq tm] simplifies an existentially quantified Presburger term,
    (or returns QConv.UNCHANGED) by using the equality elimination
    procedure described in section 2.2 of Pugh's CACM paper.

*)