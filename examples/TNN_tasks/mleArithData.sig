signature mleArithData =
sig

  include Abbrev

  val eval_numtm      : term -> int
  val random_numtm    : (int * int) -> term

  val create_train : int -> term list
  val create_valid : term list -> int -> term list
  val create_test  : term list -> int -> term list

  val create_export_arithdata : unit -> unit
  val import_arithdata : string -> (term * int) list
  val export_arithfea : string -> unit
    

  (* statistics *)
  val regroup_by_metric : ('a -> int) -> 'a list -> (int * int) list

end
