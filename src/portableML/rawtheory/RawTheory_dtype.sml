structure RawTheory_dtype =
struct

datatype class = Thm | Axm | Def
fun class_toString Thm = "Thm"
  | class_toString Axm = "Axm"
  | class_toString Def = "Def"


type vec = Word8Vector.vector
val hashLength = 20
val minHash = Word8Vector.tabulate(hashLength, fn _ => 0wx0)
fun hashToString h = String.concat(List.tabulate(hashLength,
  fn i => StringCvt.padLeft #"0" 2 (
            Word8.toString (Word8Vector.sub(h, i)))))
fun hashFromString s =
  if String.size s <> 2 * hashLength then NONE
  else SOME (
    Word8Vector.tabulate(hashLength, fn i =>
      Option.valOf (Word8.fromString (
        String.substring(s, 2 * i, 2)))))
  handle Option => NONE
fun hash_to_list h = List.tabulate(
  Word8Vector.length h, Portable.curry Word8Vector.sub h)
val hash_compare =
  Portable.inv_img_cmp hash_to_list
    (Portable.list_compare Word8.compare)

type raw_name = {thy : string, hash : Word8Vector.vector}
fun raw_name_compare (r1:raw_name, r2:raw_name) =
    case String.compare(#thy r1, #thy r2) of
        EQUAL => hash_compare(#hash r1, #hash r2)
      | x => x
fun raw_name_toString {thy,hash} =
    "{" ^ thy ^ "," ^ hashToString hash ^ "}"

datatype raw_type = TYV of string
                  | TYOP of {opn : int (* ref to idtable *),
                             args : int list (* refs to earlier types *)}

(* TMAp and TMAbs constructors unused by SharingTables infrastructure *)
datatype raw_term = TMV of string * int
                  | TMC of int * int
                  | TMAp of int * int
                  | TMAbs of int * int

type sharing_tables = {stringt : string Vector.vector,
                       idt : (int * int) list,
                       typet : raw_type list,
                       termt : raw_term list}

type 'thy raw_dep = {
  me : 'thy * int, (* thy, thm-number *)
  deps : ('thy * int list) list (* per theory thm numbers *)
}

datatype raw_loc =
         rlUnknown | rlLocated of {path:int list, linenum : int, exact:bool}

type 'a raw_thm = {
  name : 'a , (* reference to string table *)
  deps : 'a raw_dep,
  tags : string list,
  class : class (* Thm | Axm | Def *),
  private : bool,
  loc : raw_loc,
  concl : string,  (* encoded term, decode with Term.read_raw *)
  hyps : string list (* encoded terms, as above *)
}

type 'a raw_exports = {
  (* for types, ints are references into accompanying type-vector *)
  unnamed_types : int list,
  named_types : (string * int) list,
  (* for terms, strings are encoded with write_raw *)
  unnamed_terms : string list,
  named_terms : {name:string, encoded_term: string} list,
  thms : 'a raw_thm list
}

type 'a raw_core = {tables : sharing_tables, exports : 'a raw_exports}

type raw_theory = {
  name : string,
  parents : raw_name list,
  tables : sharing_tables,
  newsig : {
    types : (string * int) list, (* names and arities *)
    consts : (string * int) list (* names and (encoded) types *)
  },
  exports : string raw_exports,
  thydata : HOLsexp.t
}


end
