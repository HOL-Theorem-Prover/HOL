structure intLib :> intLib =
struct
  type hol_type = Type.hol_type
  type term = Term.term
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic

 open intSyntax intSimps Cooper

end;
