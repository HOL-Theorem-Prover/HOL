signature DB =
sig

 type term = Term.term
 type thm = Thm.thm
 datatype theory = datatype DB_dtype.theory
 datatype class = datatype DB_dtype.class
 datatype selector = datatype DB_dtype.selector
 datatype thm_src_location = datatype DB_dtype.thm_src_location
 type data = DB_dtype.data
 type public_data = DB_dtype.public_data
 type data_value = DB_dtype.data_value
 type 'a named = 'a DB_dtype.named
 datatype location = datatype DB_dtype.location
 type hol_type = Type.hol_type
 type thminfo = {private:bool,loc:thm_src_location,class:class}

  val thy         : string -> data list
  val fetch       : string -> string -> thm
  val fetch_knm   : KernelSig.kernelname -> thm
  val lookup      : KernelSig.kernelname -> DB_dtype.data_value option
  val thms        : string -> (string * thm) list

  val theorem     : string -> thm
  val definition  : string -> thm
  val axiom       : string -> thm

  val axioms      : string -> (string * thm) list
  val theorems    : string -> (string * thm) list
  val definitions : string -> (string * thm) list
  val find_all    : string -> data list (* includes private theorems *)
  val find        : string -> public_data list
  val find_in     : string -> 'a named list -> 'a named list
  val matchp      : (thm -> bool) -> string list -> public_data list
  val matcher     : (term -> term -> 'a) -> string list -> term ->
                    public_data list
  val match       : string list -> term -> public_data list
  val matches     : term -> thm -> bool
  val apropos     : term -> public_data list
  val apropos_in  : term -> public_data list -> public_data list
  val selectDB    : selector list -> public_data list
  val listDB      : unit -> data list
  val revlookup   : thm -> location list

  val polarity_search : bool -> term -> public_data list

  val store_local : thminfo -> string -> thm -> unit
  val local_thm   : string -> thm option

  val dest_theory  : string -> theory
  val bindl : string -> (string * thm * thminfo) list -> unit

  (* Derived search functions *)
  val find_consts_thy : string list -> hol_type -> term list
  val find_consts : hol_type -> term list

end
