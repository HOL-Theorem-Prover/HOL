signature ProofTraceParser = sig

type thm          = Thm.thm
type thm_id       = Thm.thm_id
type compute_args = Thm.compute_args
type term         = Term.term
type hol_type     = Type.hol_type
type thminfo      = RawTheory_dtype.thminfo

eqtype 'a ptr
type heap
type ('a,'A) gparser = 'a ptr -> 'A
type 'a parser = ('a,'a) gparser
type root
val parse: string -> root ptr * heap

val heapSize: heap -> int

datatype 'a any = Int of int | Bytes of Word8VectorSlice.slice | Obj of 'a list | Other
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
val list: heap -> ('a, 'A) gparser -> ('a list, 'A list) gparser

val str: heap -> string parser
val int: int parser
val ptr: 'a ptr -> int
val castPtr: 'a ptr -> 'b ptr
val isPtr: 'a ptr -> bool

type ident
val ident: heap -> (ident, string * string) gparser

val thmId: heap -> thm_id parser

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

datatype sh_proof =
  ABS_prf of term ptr * thm ptr
| ALPHA_prf of term ptr * term ptr
| AP_TERM_prf of term ptr * thm ptr
| AP_THM_prf of thm ptr * term ptr
| ASSUME_prf of term ptr
| Axiom_prf
| BETA_CONV_prf of term ptr
| Beta_prf of thm ptr
| CCONTR_prf of term ptr * thm ptr
| CHOOSE_prf of term ptr * thm ptr * thm ptr
| CONJUNCT1_prf of thm ptr
| CONJUNCT2_prf of thm ptr
| CONJ_prf of thm ptr * thm ptr
| DISCH_prf of term ptr * thm ptr
| DISJ1_prf of thm ptr * term ptr
| DISJ2_prf of term ptr * thm ptr
| DISJ_CASES_prf of thm ptr * thm ptr * thm ptr
| Def_const_list_prf of thm ptr * term list ptr
| Def_const_prf of term ptr * term ptr
| Def_spec_prf of thm ptr * term list ptr
| Def_tyop_prf of hol_type list ptr * thm ptr * hol_type ptr
| Disk_prf of string * thm_id ptr
| EQ_IMP_RULE1_prf of thm ptr
| EQ_IMP_RULE2_prf of thm ptr
| EQ_MP_prf of thm ptr * thm ptr
| EXISTS_prf of term ptr * term ptr * thm ptr
| Exported_prf of string * thm_id ptr
| GENL_prf of term list ptr * thm ptr
| GEN_ABS_prf of term option ptr * term list ptr * thm ptr
| GEN_prf of term ptr * thm ptr
| INST_TYPE_prf of (hol_type * hol_type) list ptr * thm ptr
| INST_prf of (term * term) list ptr * thm ptr
| MK_COMB_prf of thm ptr * thm ptr
| MP_prf of thm ptr * thm ptr
| Mark_prf of string * thm ptr
| Mk_abs_prf of thm ptr * term ptr * thm ptr
| Mk_comb_prf of thm ptr * thm ptr * thm ptr
| NOT_ELIM_prf of thm ptr
| NOT_INTRO_prf of thm ptr
| REFL_prf of term ptr
| SPEC_prf of term ptr * thm ptr
| SUBST_prf of (term * thm) list ptr * term ptr * thm ptr
| SYM_prf of thm ptr
| Specialize_prf of term ptr * thm ptr
| TRANS_prf of thm ptr * thm ptr
| compute_prf of (compute_args * thm list) ptr * term ptr
| deductAntisym_prf of thm ptr * thm ptr
| deleted_prf
| save_dep_prf of thm ptr
val shProof: heap -> proof ptr -> sh_proof

val shComputeArgs: heap -> compute_args ptr ->
  { cval_terms : (string * term) list ptr,
    cval_type  : hol_type ptr,
    num_type   : hol_type ptr,
    char_eqns  : (string * thm) list ptr }

val shRoot: heap -> root ptr ->
  { theory: string,
    parents: (string * string) list ptr,
    types: (string * int) list ptr,
    constants: (string * hol_type) list ptr,
    all_thms: (string * thm * thminfo) list ptr,
    anon_thms: thm list ptr,
    mldeps: string list ptr }

val shThmInfo: heap -> (thminfo, {private: bool}) gparser

end
