signature Extract =
sig
  include Abbrev

  (* extract FV congs (proto_def,WFR) (p,th) *)
  val extract :
     term list ->
     thm list -> term * term -> term * thm -> thm * term list * bool

end
