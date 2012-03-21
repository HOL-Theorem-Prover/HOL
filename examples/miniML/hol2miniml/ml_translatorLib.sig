signature ml_translatorLib =
sig

    include Abbrev

    (* main functionality *)

    val translate  : thm -> thm   (* e.g. try translate listTheory.MAP *)
    val hol2deep   : term -> thm  (* e.g. try hol2deep ``\x.x`` *)

    (* wrapper functions *)

    val mlDefine   : term quotation -> thm
    val mltDefine  : string -> term quotation -> tactic -> thm

    (* interface for teaching the translator about new types *)

    val add_type_inv   : term -> hol_type -> unit
    val store_eval_thm : thm -> thm
    val store_eq_thm   : thm -> thm
    val register_type  : hol_type -> unit
    val set_inv_def    : hol_type * thm -> unit

    (* interface for producing output from translations *)

    val clear_filename : unit -> unit
    val set_filename   : string -> unit

end
