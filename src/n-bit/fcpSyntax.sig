signature fcpSyntax =
sig
    include Abbrev

    val mk_numeric_type       : Arbnum.num -> hol_type
    val mk_int_numeric_type   : int -> hol_type
    val mk_cart_type          : hol_type * hol_type -> hol_type

    val dest_numeric_type     : hol_type -> Arbnum.num
    val dest_int_numeric_type : hol_type -> int
    val dest_cart_type        : hol_type -> hol_type * hol_type

    val is_numeric_type       : hol_type -> bool
    val is_cart_type          : hol_type -> bool

    val dim_of                : term -> hol_type

    val fcp_tm                : term
    val fcp_index_tm          : term
    val dimindex_tm           : term

    val mk_fcp                : term * hol_type -> term
    val mk_fcp_index          : term * term -> term
    val mk_dimindex           : hol_type -> term

    val dest_fcp              : term -> term * hol_type
    val dest_fcp_index        : term -> term * term
    val dest_dimindex         : term -> hol_type

    val is_fcp                : term -> bool
    val is_fcp_index          : term -> bool
    val is_dimindex           : term -> bool

end
