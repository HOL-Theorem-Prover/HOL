signature Term =
sig

  include FinalTerm where type hol_type = KernelTypes.hol_type
                          and type term = KernelTypes.term
                          and type kind = KernelTypes.kind
                          and type rank = KernelTypes.rank

  val termsig       : KernelTypes.holty KernelSig.symboltable

  val lazy_beta_conv : term -> term
  val imp            : term
  val dest_eq_ty     : term -> term * term * hol_type
  val prim_mk_eq     : hol_type -> term -> term -> term
  val prim_mk_imp    : term -> term -> term
  val break_const    : term -> KernelTypes.id * hol_type
  val break_abs      : term -> term
  val break_tyabs    : term -> term

  val trav           : (hol_type -> unit) -> (term -> unit) -> term -> unit
  val ty2tm          : hol_type -> term
  val ty2tmE         : hol_type -> kind list -> term
  val pp_raw_term    : (hol_type -> int) -> (term -> int) -> Portable.ppstream -> term -> unit
  val is_bvar        : term -> bool
  val is_poly_const : term -> bool

  val get_type_kind_rank_insts : kind list -> hol_type list ->
                      {redex : term, residue : term} list ->
                      ({redex : hol_type, residue : hol_type} list * hol_type list) *
                      ({redex : kind, residue : kind} list * kind list) * (rank * bool) ->
                      ({redex : hol_type, residue : hol_type} list * hol_type list) *
                      ({redex : kind, residue : kind} list * kind list) * (rank * bool)

end;
