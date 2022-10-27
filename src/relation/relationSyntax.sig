signature relationSyntax =
sig
    include Abbrev

    val antisymmetric_tm     : term
    val cr_tm                : term
    val diag_tm              : term
    val diamond_tm           : term
    val empty_rel_tm         : term
    val eqc_tm               : term
    val equivalence_tm       : term
    val idem_tm              : term
    val inv_image_tm         : term
    val inv_tm               : term
    val invol_tm             : term
    val irreflexive_tm       : term
    val linearorder_tm       : term
    val o_tm                 : term
    val order_tm             : term
    val preorder_tm          : term
    val rc_tm                : term
    val rcdiamond_tm         : term
    val rcompl_tm            : term
    val rdom_tm              : term
    val reflexive_tm         : term
    val restrict_tm          : term
    val rinter_tm            : term
    val rrange_tm            : term
    val rrestrict_tm         : term
    val rsubset_tm           : term
    val rtc_tm               : term
    val runion_tm            : term
    val runiv_tm             : term
    val sc_tm                : term
    val sn_tm                : term
    val stronglinearorder_tm : term
    val strongorder_tm       : term
    val strord_tm            : term
    val symmetric_tm         : term
    val tc_tm                : term
    val total_tm             : term
    val transitive_tm        : term
    val wcr_tm               : term
    val weaklinearorder_tm   : term
    val weakorder_tm         : term
    val wf_tm                : term
    val wfp_tm               : term

    val mk_antisymmetric     : term -> term
    val mk_cr                : term -> term
    val mk_diag              : term -> term
    val mk_diamond           : term -> term
    val mk_empty_rel         : hol_type -> term
    val mk_eqc               : term -> term
    val mk_equivalence       : term -> term
    val mk_idem              : term -> term
    val mk_inv_image         : term * term -> term
    val mk_inv               : term -> term
    val mk_invol             : term -> term
    val mk_irreflexive       : term -> term
    val mk_linearorder       : term -> term
    val mk_o                 : term * term -> term
    val mk_order             : term -> term
    val mk_preorder          : term -> term
    val mk_rc                : term -> term
    val mk_rcdiamond         : term -> term
    val mk_rcompl            : term -> term
    val mk_rdom              : term -> term
    val mk_reflexive         : term -> term
    val mk_restrict          : term * term -> term
    val mk_rinter            : term * term -> term
    val mk_rrange            : term -> term
    val mk_rrestrict         : term * term -> term
    val mk_rsubset           : term * term -> term
    val mk_rtc               : term -> term
    val mk_runion            : term * term -> term
    val mk_runiv             : hol_type * hol_type -> term
    val mk_sc                : term -> term
    val mk_sn                : term -> term
    val mk_stronglinearorder : term -> term
    val mk_strongorder       : term -> term
    val mk_strord            : term -> term
    val mk_symmetric         : term -> term
    val mk_tc                : term -> term
    val mk_total             : term -> term
    val mk_transitive        : term -> term
    val mk_wcr               : term -> term
    val mk_weaklinearorder   : term -> term
    val mk_weakorder         : term -> term
    val mk_wf                : term -> term
    val mk_wfp               : term -> term

    val dest_antisymmetric     : term -> term
    val dest_cr                : term -> term
    val dest_diag              : term -> term
    val dest_diamond           : term -> term
    val dest_eqc               : term -> term
    val dest_equivalence       : term -> term
    val dest_idem              : term -> term
    val dest_inv_image         : term -> term * term
    val dest_inv               : term -> term
    val dest_invol             : term -> term
    val dest_irreflexive       : term -> term
    val dest_linearorder       : term -> term
    val dest_o                 : term -> term * term
    val dest_order             : term -> term
    val dest_preorder          : term -> term
    val dest_rc                : term -> term
    val dest_rcdiamond         : term -> term
    val dest_rcompl            : term -> term
    val dest_rdom              : term -> term
    val dest_reflexive         : term -> term
    val dest_restrict          : term -> term * term
    val dest_rinter            : term -> term * term
    val dest_rrange            : term -> term
    val dest_rrestrict         : term -> term * term
    val dest_rsubset           : term -> term * term
    val dest_rtc               : term -> term
    val dest_runion            : term -> term * term
    val dest_sc                : term -> term
    val dest_sn                : term -> term
    val dest_stronglinearorder : term -> term
    val dest_strongorder       : term -> term
    val dest_strord            : term -> term
    val dest_symmetric         : term -> term
    val dest_tc                : term -> term
    val dest_total             : term -> term
    val dest_transitive        : term -> term
    val dest_wcr               : term -> term
    val dest_weaklinearorder   : term -> term
    val dest_weakorder         : term -> term
    val dest_wf                : term -> term
    val dest_wfp               : term -> term

    val is_antisymmetric     : term -> bool
    val is_cr                : term -> bool
    val is_diag              : term -> bool
    val is_diamond           : term -> bool
    val is_empty_rel         : term -> bool
    val is_eqc               : term -> bool
    val is_equivalence       : term -> bool
    val is_idem              : term -> bool
    val is_inv_image         : term -> bool
    val is_inv               : term -> bool
    val is_invol             : term -> bool
    val is_irreflexive       : term -> bool
    val is_linearorder       : term -> bool
    val is_o                 : term -> bool
    val is_order             : term -> bool
    val is_preorder          : term -> bool
    val is_rc                : term -> bool
    val is_rcdiamond         : term -> bool
    val is_rcompl            : term -> bool
    val is_rdom              : term -> bool
    val is_reflexive         : term -> bool
    val is_restrict          : term -> bool
    val is_rinter            : term -> bool
    val is_rrange            : term -> bool
    val is_rrestrict         : term -> bool
    val is_rsubset           : term -> bool
    val is_rtc               : term -> bool
    val is_runion            : term -> bool
    val is_runiv             : term -> bool
    val is_sc                : term -> bool
    val is_sn                : term -> bool
    val is_stronglinearorder : term -> bool
    val is_strongorder       : term -> bool
    val is_strord            : term -> bool
    val is_symmetric         : term -> bool
    val is_tc                : term -> bool
    val is_total             : term -> bool
    val is_transitive        : term -> bool
    val is_wcr               : term -> bool
    val is_weaklinearorder   : term -> bool
    val is_weakorder         : term -> bool
    val is_wf                : term -> bool
    val is_wfp               : term -> bool

end
