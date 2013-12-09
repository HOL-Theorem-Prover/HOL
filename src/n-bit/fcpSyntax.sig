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
    val fcp_update_tm         : term
    val fcp_hd_tm             : term
    val fcp_tl_tm             : term
    val fcp_cons_tm           : term
    val fcp_map_tm            : term
    val fcp_exists_tm         : term
    val fcp_every_tm          : term
    val v2l_tm                : term
    val l2v_tm                : term

    val mk_fcp                : term * hol_type -> term
    val mk_fcp_index          : term * term -> term
    val mk_dimindex           : hol_type -> term
    val mk_fcp_update         : term * term * term -> term  (* A[i] := v is mk_fcp_update (A,i,v)  *)
    val mk_fcp_hd             : term -> term
    val mk_fcp_tl             : term -> term
    val mk_fcp_cons           : term * term -> term
    val mk_fcp_map            : term * term -> term
    val mk_fcp_exists         : term * term -> term
    val mk_fcp_every          : term * term -> term
    val mk_v2l                : term -> term
    val mk_l2v                : term -> term

    val dest_fcp              : term -> term * hol_type
    val dest_fcp_index        : term -> term * term
    val dest_dimindex         : term -> hol_type
    val dest_fcp_update       : term -> term * term * term
    val dest_fcp_hd           : term -> term
    val dest_fcp_tl           : term -> term
    val dest_fcp_cons         : term -> term * term
    val dest_fcp_map          : term -> term * term
    val dest_fcp_exists       : term -> term * term
    val dest_fcp_every        : term -> term * term
    val dest_v2l              : term -> term
    val dest_l2v              : term -> term

    val is_fcp                : term -> bool
    val is_fcp_index          : term -> bool
    val is_dimindex           : term -> bool
    val is_fcp_update         : term -> bool
    val is_fcp_hd             : term -> bool
    val is_fcp_tl             : term -> bool
    val is_fcp_cons           : term -> bool
    val is_fcp_map            : term -> bool
    val is_fcp_exists         : term -> bool
    val is_fcp_every          : term -> bool
    val is_v2l                : term -> bool
    val is_l2v                : term -> bool

end
