signature ProofTraceParser = sig

eqtype 'a ptr
type heap
type ('a,'A) gparser = 'a ptr -> 'A
type 'a parser = ('a,'a) gparser
type root
val parse: string -> root ptr * heap

datatype 'a any = Int of int | Bytes of string | Obj of 'a list | Other
val any: heap -> (unit, 'A) gparser -> ('b, 'A any) gparser

val shVariant: heap -> 'a ptr -> int * unit ptr list

val tuple2: heap -> ('a,'A) gparser * ('b,'B) gparser -> ('a * 'b, 'A * 'B) gparser
val tuple3: heap -> ('a,'A) gparser * ('b,'B) gparser * ('c,'C) gparser ->
  ('a * 'b * 'c, 'A * ('B * 'C)) gparser
val tuple4: heap -> ('a,'A) gparser * ('b,'B) gparser * ('c,'C) gparser * ('d,'D) gparser ->
  ('a * 'b * 'c * 'd, 'A * ('B * ('C * 'D))) gparser

val appList: heap -> ('a, 'b) gparser -> ('a list, unit) gparser
val appSet: heap -> ('a, 'b) gparser -> ('a HOLset.set, unit) gparser
val option: heap -> ('a, 'A) gparser -> ('a option, 'A option) gparser

val str: heap -> string parser
val int: int parser
val ptr: 'a ptr -> int
val castPtr: 'a ptr -> 'b ptr

type ident
val ident: heap -> ident ptr -> string * string

datatype sh_type =
  Tyapp of ident ptr * hol_type list ptr
| Tyv of string
val shType: heap -> hol_type ptr -> sh_type

datatype sh_term =
  Abs of term ptr * term ptr
| Bv of int
| Clos of term Subst.subs ptr * term ptr
| Comb of term ptr * term ptr
| Const of ident ptr * hol_type ptr
| Fv of string * hol_type ptr
val shTerm: heap -> term ptr -> sh_term

datatype 'a sh_subs =
  Cons of 'a Subst.subs ptr * 'a ptr
| Id
| Lift of int * 'a Subst.subs ptr
| Shift of int * 'a Subst.subs ptr
val shSubs: heap -> 'a Subst.subs ptr -> 'a sh_subs

type proof
val shThm: heap -> thm ptr -> term HOLset.set ptr * term ptr * proof ptr

val shRoot: heap -> root ptr ->
  { theory: string,
    parents: (string * string) list ptr,
    types: (string * int) list ptr,
    constants: (string * hol_type) list ptr,
    all_thms: (string * thm * thminfo) list ptr,
    mldeps: string list ptr }

val shThmInfo: heap -> (thminfo, {private: bool}) gparser

end
