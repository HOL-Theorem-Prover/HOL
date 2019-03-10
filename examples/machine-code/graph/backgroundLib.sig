signature backgroundLib =
sig

  val max : int * int -> int
  val the : 'a option -> 'a
  val try_map : ('a -> 'b) -> 'a list -> 'b list
  val append_lists : 'a list list -> 'a list
  val diff : ''a list -> ''a list -> ''a list
  val drop : int -> 'a list -> 'a list
  val drop_until : ('a -> bool) -> 'a list -> 'a list
  val every : ('a -> bool) -> 'a list -> bool
  val lines_from_file : string -> string list
  val measure_it : string -> ('a -> 'b) -> 'a -> 'b
  val subset : ''a list -> ''a list -> bool
  val sum : int list -> int
  val take : int -> 'a list -> 'a list
  val take_until : ('a -> bool) -> 'a list -> 'a list
  val dest_tuple : Term.term -> Term.term list
  val BINOP1_CONV : Conv.conv -> Conv.conv
  val REPLACE_CONV : Thm.thm -> Term.term -> Thm.thm
  val expand_conv : Conv.conv
  val index_for : ''a -> ''a list -> int
  val list_dest_pair : Term.term -> Term.term list
  val list_mk_pair : Term.term list -> Term.term
  val skip_proofs : bool ref
  val auto_conv_prove : string -> Term.term -> (Term.term -> Thm.thm) -> Thm.thm
  val auto_prove :
     string ->
     Term.term * ('a list * Term.term -> 'b list * ('c list -> Thm.thm)) ->
     Thm.thm
  val clean_name : string -> string
  val dest_sum_type : Type.hol_type -> Type.hol_type * Type.hol_type
  val is_inl : Term.term -> bool
  val is_inr : Term.term -> bool
  val modify_message : (string -> string) -> exn -> exn
  val print_error : Term.term -> unit
  val report_error : string -> exn -> 'a

  val term_diff : Term.term list -> Term.term list -> Term.term list
  val term_mem : Term.term -> Term.term list -> bool
  val term_intersect : Term.term list -> Term.term list -> Term.term list
  val term_all_distinct : Term.term list -> Term.term list

end
