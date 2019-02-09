signature hhExportLib =
sig

include Abbrev

  val hh_dir : string

  val os : TextIO.outstream -> string -> unit
  val osn : TextIO.outstream -> string -> unit
  val oiter : TextIO.outstream ->
    string -> (TextIO.outstream -> 'a -> unit) -> 'a list -> unit

  (* type *)
  val ttype : string
  val otype : string

  val type_vars_in_term : term -> hol_type list
  val strip_funty_n : int -> hol_type -> hol_type list
  val strip_funty : hol_type -> (hol_type * hol_type list)

  val full_match_type : 
    hol_type -> hol_type -> {redex: hol_type, residue: hol_type} list
  val typearg_of_const : term -> hol_type list
  val typearg_of_var : term -> hol_type list
  val typearg_of_appvar : term -> hol_type list

  (* term *)
  val full_apply_const : term -> term
  
  val atoms_of : term -> term list

  val shared_pred :  
    (TextIO.outstream -> term -> unit) * 
    (TextIO.outstream -> term -> unit) -> 
    TextIO.outstream -> term -> unit
    
  (* thm *)
  val older_than : thm -> 'a * thm -> bool
  val depo_of_thm : thm -> (string * string) list option 
 
  (* theory *)
  val before_elem: ''a -> ''a list -> ''a list

  val sorted_ancestry : string list -> string list

  val write_thy : (TextIO.outstream -> string -> string * int -> unit) *
    (TextIO.outstream -> string * string -> unit) *
    (TextIO.outstream -> string -> (string * thm) * string -> unit) *
    (string * string -> string) -> string -> string -> unit

end
