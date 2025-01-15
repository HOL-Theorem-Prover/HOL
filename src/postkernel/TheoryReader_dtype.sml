structure TheoryReader_dtype =
struct


type raw_name = {thy : string, tstamp1 : string, tstamp2 : string}
datatype encoded_type = TYV of string
                      | TYOP of {opn : int (* ref to idtable *),
                                 args : int list (* refs to earlier types *)}
datatype encoded_term = TMV of string * int
                      | TMC of int * int
                      | TMAp of int * int
                      | TMAbs of int * int

type sharing_tables = {stringt : string list,
                       idt : (int * int) list,
                       typet : encoded_type list,
                       termt : encoded_term list}
type raw =
     { name : raw_name,
       ancestors : raw_name list,
       tables : sharing_tables
     }


end (* struct *)
