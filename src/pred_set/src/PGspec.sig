signature PGspec =
sig
 type conv = Abbrev.conv
  val SET_SPEC_CONV : Thm.thm -> conv
end;
