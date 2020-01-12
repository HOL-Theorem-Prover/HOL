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

  val theoryout_strtable : stringtable PP.pprinter
  val make_shared_type : Type.hol_type -> stringtable -> idtable -> typetable ->
                         (int * stringtable * idtable * typetable)

  val make_shared_term : Term.term ->
                         (stringtable * idtable * typetable * termtable) ->
                         int * (stringtable * idtable * typetable * termtable)

  val theoryout_idtable    : idtable PP.pprinter

  val build_id_vector   : string Vector.vector -> (int * int) list ->
                          id Vector.vector
  val build_type_vector : id Vector.vector -> shared_type list ->
                          Type.hol_type Vector.vector

  val output_typetable : {idtable_nm : string, tytable_nm : string} ->
                         typetable -> PP.pretty
  val theoryout_typetable    : typetable PP.pprinter

  val build_term_vector : id Vector.vector -> Type.hol_type Vector.vector ->
                          shared_term list -> Term.term Vector.vector

  val output_termtable : {idtable_nm : string, tytable_nm : string,
                          termtable_nm : string} ->
                         termtable -> PP.pretty

  val theoryout_termtable    : termtable PP.pprinter

end
