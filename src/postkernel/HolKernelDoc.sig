signature HolKernelDoc =
sig
  (* This signature file is for documentation purposes only *)

  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type 'a set = 'a Binaryset.set
  type ('a,'b) subst = ('a,'b) Lib.subst

  datatype lambda =
      VAR of string * hol_type
    | CONST of {Name: string, Thy: string, Ty: hol_type}
    | COMB of term * term
    | LAMB of term * term

  val gen_find_term: (term list * term -> 'a option) -> term -> 'a option
  val gen_find_terms: (term list * term -> 'a option) -> term -> 'a list
  val bvk_find_term:
     (term list * term -> bool) -> (term -> 'a) -> term -> 'a option
  val dest_binder: term -> exn -> term -> term * term
  val dest_binop: term -> exn -> term -> term * term
  val dest_monop: term -> exn -> term -> term
  val dest_quadop: term -> exn -> term -> term * term * term
  val dest_term: term -> lambda
  val dest_triop: term -> exn -> term -> term * term * term
  val disch: term * term list -> term list
  val find_maximal_terms: (term -> bool) -> term -> term set
  val find_term: (term -> bool) -> term -> term
  val find_terms: (term -> bool) -> term -> term list
  val ho_match_term0:
     hol_type list -> term set -> term -> term ->
     {redex: term, residue: int} list *
     {redex: term, residue: term} list *
     ((hol_type, hol_type) Lib.subst * hol_type list)
  val ho_match_term:
     hol_type list -> term set -> term -> term ->
     {redex: term, residue: term} list * (hol_type, hol_type) subst
  val list_mk_fun: hol_type list * hol_type -> hol_type
  val list_mk_icomb: term * term list -> term
  val list_mk_lbinop: ('a -> 'a -> 'a) -> 'a list -> 'a
  val list_mk_rbinop: ('a -> 'a -> 'a) -> 'a list -> 'a
  val lspine_binop: ('a -> ('a * 'a) option) -> 'a -> 'a list
  val mk_binder: term -> string -> term * term -> term
  val mk_binop: term -> term * term -> term
  val mk_monop: term -> term -> term
  val mk_quadop: term -> term * term * term * term -> term
  val mk_triop: term -> term * term * term -> term
  val sdest_binder: string * string -> exn -> term -> term * term
  val sdest_binop: string * string -> exn -> term -> term * term
  val sdest_monop: string * string -> exn -> term -> term
  val spine_binop: ('a -> ('a * 'a) option) -> 'a -> 'a list
  val strip_binop: ('a -> ('a * 'a) option) -> 'a -> 'a list
  val strip_comb: term -> term * term list
  val strip_fun: hol_type -> hol_type list * hol_type
  val strip_gen_right_opt : ('a -> ('a * 'b) option) -> 'a -> 'a * 'b list
  val strip_gen_right : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  val strip_gen_left_opt : ('a -> ('b * 'a) option) -> 'a -> 'b list * 'a
  val strip_gen_left : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val subst_occs:
     int list list -> {redex: term, residue: term} list -> term -> term
  val syntax_fns:
     {n: int, make: term -> 'a -> term, dest: term -> exn -> term -> 'b} ->
     string -> string -> term * ('b -> term) * (term -> 'a) * (term -> bool)
  val term_size: term -> int

end
