signature SharingTables =
sig


  structure Map : Binarymap
  type id = {Thy : string, Other : string}
  datatype shared_type = TYV of string
                       | TYOP of int list
  datatype shared_term = TMV of string * int
                       | TMC of int * int
                       | TMAp of int * int
                       | TMAbs of int * int

  type idtable = {idsize : int,
                  idmap : (id, int) Map.dict,
                  idlist : id list}
  type typetable = {tysize : int,
                    tymap : (Type.hol_type, int)Map.dict,
                    tylist : shared_type list}
  type termtable = {termsize : int,
                    termmap : (Term.term, int)Map.dict,
                    termlist : shared_term list}

  val empty_idtable : idtable
  val empty_tytable : typetable
  val empty_termtable : termtable

  val make_shared_type : Type.hol_type -> idtable -> typetable ->
                         (int * idtable * typetable)

  val make_shared_term : Term.term -> (idtable * typetable * termtable) ->
                         int * (idtable * typetable * termtable)

  val output_idtable : Portable.ppstream -> string -> idtable -> unit

  val build_type_vector : id Vector.vector -> shared_type list ->
                          Type.hol_type Vector.vector

  val output_typetable : Portable.ppstream ->
                         {idtable_nm : string, tytable_nm : string} ->
                         typetable -> unit


  val build_term_vector : id Vector.vector -> Type.hol_type Vector.vector ->
                          shared_term list -> Term.term Vector.vector

  val output_termtable : Portable.ppstream ->
                         {idtable_nm : string, tytable_nm : string,
                          termtable_nm : string} ->
                         termtable -> unit


end;
