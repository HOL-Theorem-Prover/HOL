signature Defn0 =
sig
  type hol_type     = Type.hol_type
  type term         = Term.term
  type thm          = Thm.thm
  type conv         = Abbrev.conv
  type tactic       = Abbrev.tactic

  datatype defn
     = NONREC  of {eqs:thm, ind: thm option}
     | PRIMREC of {eqs:thm, ind:thm}
     | STDREC  of {eqs:thm, ind:thm, R:term, SV:term list}
     | NESTREC of {eqs:thm, ind:thm, R:term, SV:term list,aux:defn}
     | MUTREC  of {eqs:thm, ind:thm, R:term, SV:term list,union:defn}


  val is_nonrec  : defn -> bool
  val is_primrec : defn -> bool
  val is_nestrec : defn -> bool
  val is_mutrec  : defn -> bool

  val eqns_of    : defn -> thm
  val eqnl_of    : defn -> thm list
  val ind_of     : defn -> thm option
  val tcs_of     : defn -> term list
  val reln_of    : defn -> term option
  val params_of  : defn -> term list

  val aux_defn   : defn -> defn option
  val union_defn : defn -> defn option

  val inst_defn  : defn -> (term,term)Lib.subst * 
                           (hol_type,hol_type)Lib.subst -> defn
  val set_reln   : defn -> term -> defn

  (* val simp_defn  : defn -> conv -> defn *)

  val elim_tcs   : defn -> thm list -> defn
  val simp_tcs   : defn -> conv -> defn
  val prove_tcs  : defn -> tactic -> defn

  val pp_defn    : ppstream -> defn -> unit


  (* Tracking context for termination condition extraction *)

  val read_context  : unit -> thm list
  val write_context : thm list -> unit

end
