signature lisp_extractLib =
sig

    include Abbrev

    (* main functions *)

    val pure_extract              : string -> tactic option -> thm
    val pure_extract_mutual_rec   : string list -> tactic option -> thm
    val impure_extract            : string -> tactic option -> thm
    val impure_extract_cut        : string -> tactic option -> thm

    (* setting the state *)

    val set_lookup_thm    : thm -> unit
    val install_assum_eq  : thm -> unit
    val atbl_install      : string -> thm -> unit

end
