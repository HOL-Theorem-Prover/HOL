signature hhExportLib =
sig

include Abbrev

  val hh_dir : string

  val os : TextIO.outstream -> string -> unit
  val osn : TextIO.outstream -> string -> unit
  val oiter : TextIO.outstream ->
    string -> (TextIO.outstream -> 'a -> unit) -> 'a list -> unit

  (* naming *)
  val combin_namespace_flag : bool ref
  
  val cid_of : term -> (string * string)

  val name_v : term -> string
  val namea_v : int -> term -> string
  val name_vartype : hol_type -> string

  val name_cid : (string * string) -> string
  val namea_cid : int -> (string * string) -> string
  val name_c: term -> string
  val namea_c : int -> term -> string
  val name_tyop : (string * string) -> string
  
  val namea_cv : int -> term -> string

  val name_thm : (string * string) -> string
  
  (* comparison *)
  val id_compare : (string * string) * (string * string) -> order
  val ida_compare : 
    ((string * string) * int) * ((string * string) * int) -> order
  val compare_namethm : (string * thm) * (string * thm) -> order    

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
  val type_set : term -> hol_type list
  val tyop_set : hol_type -> ((string * string) * int) list
  val const_set : term -> term list 
  val required_def : term list -> 
    ((string * string) * int) list * (string * string) list

  (* thm *)
  val older_than : thm -> 'a * thm -> bool
  val depo_of_thm : thm -> (string * string) list option 
  val fetch_thm : (string * string) -> thm 

  (* theory *)
  val before_elem: ''a -> ''a list -> ''a list
  val sorted_ancestry : string list -> string list
 
  val include_thy : TextIO.outstream -> string -> unit
  val include_thytyopdef : TextIO.outstream -> string -> unit
  val include_thycdef : TextIO.outstream -> string -> unit
  val include_thyax : TextIO.outstream -> string -> unit  
  

  val write_thy_bushy : string -> string list * string list * string list ->
     (TextIO.outstream -> (string * string) * int -> unit) *
     (TextIO.outstream -> string * string -> unit) *
     (string -> TextIO.outstream -> string * string -> unit) ->
       ((string * string) * (string * string) list -> term list) ->
         string -> unit

  val write_thytyopdef : string ->
    (TextIO.outstream -> (string * string) * int -> unit) ->
      string -> unit
  val write_thycdef : string ->
    (TextIO.outstream -> string * string -> unit) ->
      string -> unit
  val write_thyax : string ->
    (string -> TextIO.outstream -> string * string -> unit) ->
      string -> unit
  val write_thy_chainy : string ->
     string list * string list * string list ->
     (string -> TextIO.outstream -> string * string -> unit) ->
     string list -> string -> unit




end
