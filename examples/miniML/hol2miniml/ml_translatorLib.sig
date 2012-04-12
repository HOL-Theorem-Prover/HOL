signature ml_translatorLib =
sig

    include Abbrev

    (* main functionality *)

    val translate  : thm -> thm    (* e.g. try translate listTheory.MAP *)
    val hol2deep   : term -> thm   (* e.g. try hol2deep ``\x.x`` *)
    val hol2val    : term -> term  (* e.g. try hol2val ``5:num`` *)

    (* wrapper functions *)

    val mlDefine   : term quotation -> thm
    val mltDefine  : string -> term quotation -> tactic -> thm

    (* interface for teaching the translator about new types *)

    val add_type_inv   : term -> hol_type -> unit
    val store_eval_thm : thm -> thm
    val store_eq_thm   : thm -> thm
    val register_type  : hol_type -> unit

    (* loading state of translator *)

    val translation_extends  : string -> unit

    (* simplification of preconditions / sideconditions *)

    val update_precondition  : thm -> thm

end
