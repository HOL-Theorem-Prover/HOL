signature OmegaEq =
sig
  include Abbrev
  val OmegaEq : term -> thm

end;

(*
    [OmegaEq tm] simplifies an existentially quantified Presburger term,
    (or returns QConv.UNCHANGED) by using the equality elimination
    procedure described in section 2.2 of Pugh's CACM paper.

    The term tm should be of the form ?v1..vn. T.  If the conversion is
    to do anything other than return UNCHANGED, there should be a
    Omega-normalised equality in (strip_conj T).

*)