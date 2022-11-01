signature relation_extraSyntax =
sig
    include Abbrev

    val delift_tm      : term
    val rcross_tm      : term
    val restr_rel_tm   : term
    val rminus_tm      : term
    val seq_tm         : term

    val mk_delift      : term * term -> term
    val mk_rcross      : term * term -> term
    val mk_restr_rel   : term * term -> term
    val mk_rminus      : term * term -> term
    val mk_seq         : term * term -> term

    val dest_delift    : term -> term * term
    val dest_rcross    : term -> term * term
    val dest_restr_rel : term -> term * term
    val dest_rminus    : term -> term * term
    val dest_seq       : term -> term * term

    val is_delift      : term -> bool
    val is_rcross      : term -> bool
    val is_restr_rel   : term -> bool
    val is_rminus      : term -> bool
    val is_seq         : term -> bool

end
