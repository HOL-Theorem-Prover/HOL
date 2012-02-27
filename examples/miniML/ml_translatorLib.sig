signature ml_translatorLib =
sig

    include Abbrev

    (* main functionality *)

    val translate  : thm -> thm

    (* wrapper functions *)

    val mlDefine   : term quotation -> thm * thm
    val mltDefine  : string -> term quotation -> tactic -> thm * thm

end
