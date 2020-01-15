signature SharingTables =
sig

  structure Map : Binarymap
  exception SharingTables of string

  type id = {Thy : string, Other : string}
  datatype shared_type = TYV of string
                       | TYOP of int list

  val shared_type_decode : shared_type HOLsexp.decoder
  val shared_type_encode : shared_type HOLsexp.encoder

  datatype shared_term = TMV of string * int
                       | TMC of int * int
                       | TMAp of int * int
                       | TMAbs of int * int
  val shared_term_decode : shared_term HOLsexp.decoder
  val shared_term_encode : shared_term HOLsexp.encoder

  type stringtable =
       {size : int, map : (string,int) Map.dict, list : string list}
  type idtable = {idsize : int,
                  idmap : (id, int) Map.dict,
                  idlist : (int * int) list}
  type typetable = {tysize : int,
                    tymap : (Type.hol_type, int)Map.dict,
                    tylist : shared_type list}
  type termtable = {termsize : int,
                    termmap : (Term.term, int)Map.dict,
                    termlist : shared_term list}

  val empty_strtable : stringtable
  val empty_idtable : idtable
  val empty_tytable : typetable
  val empty_termtable : termtable

  val enc_strtable : stringtable HOLsexp.encoder
  val enc_idtable  : idtable HOLsexp.encoder
  val enc_tytable  : typetable HOLsexp.encoder
  val enc_tmtable  : termtable HOLsexp.encoder

  val dec_strings  : string Vector.vector HOLsexp.decoder
  val dec_ids      : string Vector.vector -> id Vector.vector HOLsexp.decoder

  val make_shared_type : Type.hol_type -> stringtable -> idtable -> typetable ->
                         (int * stringtable * idtable * typetable)

  val make_shared_term : Term.term ->
                         (stringtable * idtable * typetable * termtable) ->
                         int * (stringtable * idtable * typetable * termtable)

  val build_id_vector   : string Vector.vector -> (int * int) list ->
                          id Vector.vector
  val build_type_vector : id Vector.vector -> shared_type list ->
                          Type.hol_type Vector.vector

  val build_term_vector : id Vector.vector -> Type.hol_type Vector.vector ->
                          shared_term list -> Term.term Vector.vector

end
