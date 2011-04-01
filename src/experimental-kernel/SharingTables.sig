signature SharingTables =
sig


  structure Map : Binarymap
  type id = {Thy : string, Other : string}
  datatype shared_kind = KDTY of Rank.rank
                       | KDV of string * Rank.rank
                       | KDARR of int * int
  datatype shared_type = TYV of string * int
                       | TYC of int * int
                       | TYAp of int * int
                       | TYAbs of int * int
                       | TYUni of int * int
  datatype shared_term = TMV of string * int
                       | TMC of int * int
                       | TMAp of int * int
                       | TMAbs of int * int
                       | TMTAp of int * int
                       | TMTAbs of int * int

  type idtable = {idsize : int,
                  idmap : (id, int) Map.dict,
                  idlist : id list}
  type kindtable = {kdsize : int,
                    kdmap : (Kind.kind, int)Map.dict,
                    kdlist : shared_kind list}
  type typetable = {tysize : int,
                    tymap : (Type.hol_type, int)Map.dict,
                    tylist : shared_type list}
  type termtable = {termsize : int,
                    termmap : (Term.term, int)Map.dict,
                    termlist : shared_term list}

  val empty_idtable : idtable
  val empty_kdtable : kindtable
  val empty_tytable : typetable
  val empty_termtable : termtable

  val make_shared_kind : Kind.kind -> kindtable ->
                         int * kindtable

  val make_shared_type : Type.hol_type -> (idtable * kindtable * typetable) ->
                         int * (idtable * kindtable * typetable)

  val make_shared_term : Term.term -> (idtable * kindtable * typetable * termtable) ->
                         int * (idtable * kindtable * typetable * termtable)

  val output_idtable : Portable.ppstream -> string -> idtable -> unit

  val build_kind_vector : shared_kind list ->
                          Kind.kind Vector.vector

  val output_kindtable : Portable.ppstream ->
                         {kdtable_nm : string} ->
                         kindtable -> unit

  val build_type_vector : id Vector.vector -> Kind.kind Vector.vector ->
                          shared_type list -> Type.hol_type Vector.vector

  val output_typetable : Portable.ppstream ->
                         {idtable_nm : string, kdtable_nm : string, tytable_nm : string} ->
                         typetable -> unit


  val build_term_vector : id Vector.vector -> Type.hol_type Vector.vector ->
                          shared_term list -> Term.term Vector.vector

  val output_termtable : Portable.ppstream ->
                         {idtable_nm : string, tytable_nm : string,
                          termtable_nm : string} ->
                         termtable -> unit


end;
