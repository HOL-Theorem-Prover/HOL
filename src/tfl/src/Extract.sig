signature Extract =
sig
  include Abbrev

  type simpls
  val simpls_of_congs : thm list -> simpls

  (* extract FV congs (proto_def,WFR) (p,th) *)
  val extract :
     term list
      -> simpls
       -> term * term -> term * thm -> thm * term list * bool

end
