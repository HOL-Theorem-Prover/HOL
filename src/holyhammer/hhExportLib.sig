signature hhExportLib =
sig

include Abbrev

  val hh_dir : string

  type formula_info = {
    cval : (term * int) list,
    tyopl : ((string * string) * int) list
  }

  val os : TextIO.outstream -> string -> unit
  val osn : TextIO.outstream -> string -> unit
  val oiter : TextIO.outstream ->
    string -> (TextIO.outstream -> 'a -> unit) -> 'a list -> unit

  (* naming *)
  val cid_of : term -> (string * string)

  val name_v : term -> string
  val namea_v : (term * int) -> string
  val name_vartype : hol_type -> string
  val name_cid : (string * string) -> string
  val namea_cid : ((string * string) * int) -> string
  val name_c: term -> string
  val name_cv: term -> string
  val namea_c : (term * int) -> string
  val namea_cv : (term * int) -> string
  val name_tyop : (string * string) -> string
  val name_thm : (string * string) -> string
  
  val name_tyu_mono : hol_type -> string
  val namea_obj_mono : (term * int) -> string
  val namea_obj_poly : (term * int) -> string

  val all_tyop : hol_type -> ((string * string) * int) list

  (* comparison *)
  val id_compare : (string * string) * (string * string) -> order
  val ida_compare : 
    ((string * string) * int) * ((string * string) * int) -> order
  val tma_compare : (term * int) * (term * int) -> order

  val compare_namethm : (string * thm) * (string * thm) -> order    
  val type_set : term -> hol_type list
   
  (* type *)
  val ttype : string
  val otype : string

  val type_vars_in_term : term -> hol_type list
  val strip_funty_n : int -> hol_type -> hol_type list
  val strip_funty : hol_type -> (hol_type * hol_type list)

  val full_match_type : 
    hol_type -> hol_type -> {redex: hol_type, residue: hol_type} list
  val typearg_of_c : term -> hol_type list
  val typearg_of_cvapp : term -> hol_type list
  val add_tyargltag : string -> term -> string

  (* term *)
  val full_apply_const : term -> term
  val apply_cva : (term * int) -> (term * term list) 

  val tyopset_of_tyl : hol_type list -> ((string * string) * int) list
  val add_zeroarity : (term * int) list -> (term * int) list 
  val collect_tyop : term -> ((string * string) * int) list 

  (* thm *)
  val older_than : thm -> 'a * thm -> bool
  val depo_of_thm : thm -> (string * string) list option 
  val depo_of_thmid : (string * string) -> (string * string) list option 

  val fetch_thm : (string * string) -> thm 

  val combin_axioml : (string * term) list
  val p_axioml : (string * thm) list
  val app_axioml : (string * thm) list

  (* definitions *)
  val logic_l1 : (string * string) list
  val quant_l2 : (string * string) list
  val boolop_cval : (term * int) list
  val uniq_cvdef_mgc : (term * int) list -> (term * int) list
  val uniq_cvdef_arity : (term * int) list -> (term * int) list

  (* theory *)
  val before_elem: ''a -> ''a list -> ''a list
  val sorted_ancestry : string list -> string list

  val add_chainy_dep : 
    string list -> string ->
    (string * thm) list ->
    ((string * string) * (string * string) list) list

  val add_bushy_dep :  
    string -> (string * thm) list -> 
    ((string * string) * (string * string) list) list

  val write_thy_bushy : string ->
    (thm -> term * term list) ->
    ((term * int) list -> (term * int) list) ->
    ((string * string) * int) list * (term * int) list ->
      (TextIO.outstream -> unit) *
      (TextIO.outstream -> (string * string) * int -> unit) *
      (TextIO.outstream -> unit) *
      (TextIO.outstream -> (term * int) -> unit) *
      (TextIO.outstream -> unit) *
      (TextIO.outstream -> (term * int) -> unit) *
      (string -> TextIO.outstream -> string * string -> unit) ->
    string -> unit

  val write_thy_chainy : string -> string list ->
    (thm -> term * term list) ->
    ((term * int) list -> (term * int) list) ->
    ((string * string) * int) list * (term * int) list ->
      (TextIO.outstream -> unit) *
      (TextIO.outstream -> (string * string) * int -> unit) *
      (TextIO.outstream -> unit) *
      (TextIO.outstream -> term * int -> unit) *
      (TextIO.outstream -> unit) *
      (TextIO.outstream -> term * int -> unit) *
      (string -> TextIO.outstream -> string * string -> unit) ->
    string -> unit

end
