structure TheoryReader_dtype =
struct


type raw_name = {thy : string, tstamp1 : Arbnum.num, tstamp2 : Arbnum.num}
datatype encoded_type = TYV of string
                      | TYOP of {opn : int (* ref to idtable *),
                                 args : int list (* refs to earlier types *)}
datatype encoded_term = TMV of string * int
                      | TMC of int * int
                      | TMAp of int * int
                      | TMAbs of int * int

type sharing_tables = {stringt : string Vector.vector,
                       idt : (int * int) list,
                       typet : encoded_type list,
                       termt : encoded_term list}

type 'thy raw_dep = {
  me : 'thy * int, (* thy, thm-number *)
  deps : ('thy * int list) list (* per theory thm numbers *)
}

datatype raw_loc =
         rlUnknown | rlLocated of {path:int list, linenum : int, exact:bool}

type raw_thm = {
  name : int, (* reference to string table *)
  deps : int raw_dep,
  tags : string list,
  class : DB_dtype.class (* Thm | Axm | Def *),
  private : bool,
  loc : raw_loc,
  concl : string,
  hyps : string list
}

type raw_exports = {
  (* for types, ints are references into accompanying type-vector *)
  unnamed_types : int list,
  named_types : (string * int) list,
  (* for terms, strings are encoded with write_raw *)
  unnamed_terms : string list,
  named_terms : {name:string, encoded_term: string} list,
  thms : raw_thm list
}

type raw_core = {tables : sharing_tables, exports : raw_exports}

type raw_theory = {
  name : raw_name,
  parents : raw_name list,
  tables : sharing_tables,
  newsig : {
    types : (string * int) list, (* names and arities *)
    consts : (string * int) list (* names and (encoded) types *)
  },
  exports : raw_exports,
  thydata : HOLsexp.t
}


end (* struct *)
