signature SharingTables =
sig

  structure Map : Binarymap
  exception SharingTables of string

  type id = {Thy : string, Other : string}
  datatype raw_type = datatype RawTheory_dtype.raw_type
  type thminfo = DB_dtype.thminfo
  datatype raw_term = datatype RawTheory_dtype.raw_term

  type stringtable =
       {size : int, map : (string,int) Map.dict, list : string list}
  type idtable = {idsize : int,
                  idmap : (id, int) Map.dict,
                  idlist : (int * int) list}
  type typetable = {tysize : int,
                    tymap : (Type.hol_type, int)Map.dict,
                    tylist : raw_type list}
  type termtable = {termsize : int,
                    termmap : (Term.term, int)Map.dict,
                    termlist : raw_term list}

  val empty_strtable : stringtable
  val empty_idtable : idtable
  val empty_tytable : typetable
  val empty_termtable : termtable

  val enc_strtable : stringtable HOLsexp.encoder
  val enc_idtable  : idtable HOLsexp.encoder
  val enc_tytable  : typetable HOLsexp.encoder
  val enc_tmtable  : termtable HOLsexp.encoder

  val dec_ids      : string Vector.vector -> id Vector.vector HOLsexp.decoder

  val make_raw_type : Type.hol_type -> stringtable -> idtable -> typetable ->
                         (int * stringtable * idtable * typetable)

  val make_raw_term : Term.term ->
                         (stringtable * idtable * typetable * termtable) ->
                         int * (stringtable * idtable * typetable * termtable)

  val build_id_vector   : string Vector.vector -> (int * int) list ->
                          id Vector.vector
  val build_type_vector : id Vector.vector -> raw_type list ->
                          Type.hol_type Vector.vector

  val build_term_vector : id Vector.vector -> Type.hol_type Vector.vector ->
                          raw_term list -> Term.term Vector.vector

  type sharing_data_in
  type sharing_data_out
  type extract_data = {named_terms : (string * Term.term) list,
                       unnamed_terms : Term.term list,
                       named_types : (string * Type.hol_type) list,
                       unnamed_types : Type.hol_type list,
                       theorems : (string * Thm.thm * thminfo) list}
  val build_sharing_data : extract_data -> sharing_data_in
  val add_strings : string list -> sharing_data_in -> sharing_data_in
  val add_types : Type.hol_type list -> sharing_data_in -> sharing_data_in
  val add_terms : Term.term list -> sharing_data_in -> sharing_data_in
  val write_string : sharing_data_in -> string -> int
  val write_type : sharing_data_in -> Type.hol_type -> int
  val write_term : sharing_data_in -> Term.term -> string
  val enc_sdata : sharing_data_in HOLsexp.encoder

  val dec_sdata :
      {before_types: unit -> unit,
       before_terms: Type.hol_type Vector.vector -> unit,
       tables : RawTheory_dtype.sharing_tables,
       exports : string RawTheory_dtype.raw_exports} ->
      sharing_data_out
  val export_from_sharing_data : sharing_data_out -> extract_data
  val read_term : sharing_data_out -> string -> Term.term
  val read_string : sharing_data_out -> int -> string

end

(*
    [export_from_sharing_data{data,with_strings,with_stridty}] will
    return the represented data. The functions with_strings and
    with_stridty give the caller a chance to update the state of the
    theory context before types and then terms are constructed. This
    is necessary in the theory-loading situation where the desired
    values may depend on new type operators and new term constants
    that have to be defined before the rest of the process can be
    continued.
*)
