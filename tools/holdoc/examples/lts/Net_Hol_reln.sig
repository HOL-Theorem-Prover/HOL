signature Net_Hol_reln = sig
  include Abbrev
  (* provides an inductive definition tool that copes with backwards *)
  (* implications (as well as forwards ones) *)
  val Net_Hol_reln : term quotation -> thm * thm * thm
end;
