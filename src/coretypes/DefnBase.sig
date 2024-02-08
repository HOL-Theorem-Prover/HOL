signature DefnBase =
sig
  include DefnBaseCore
  datatype defn
   = ABBREV  of {eqn:thm, bind:string}
   | PRIMREC of {eqs:thm, ind:thm, bind:string}
   | NONREC  of {eqs:thm, ind:thm, SV:term list, stem:string}
   | STDREC  of {eqs:thm list, ind:thm, R:term,SV:term list,stem:string}
   | MUTREC  of {eqs:thm list, ind:thm, R:term,SV:term list,
                 stem:string,union:defn}
   | NESTREC of {eqs:thm list, ind:thm, R:term,SV:term list,
                 stem:string,aux:defn}
   | TAILREC of {eqs:thm list, ind:thm, R:term, SV:term list, stem:string}


  val pp_defn : defn Parse.pprinter
  val all_terms : defn -> term list
    (* conclusions of theorems, SV variables, R *)

  (* Used to control context tracking during termination
     condition extraction *)

  val read_congs  : unit -> thm list
  val write_congs : thm list -> unit
  val add_cong    : thm -> unit
  val drop_cong   : term -> thm

  val export_cong : string -> unit

  (* record various flavours of definition, keyed by constant and a
     "tag", which is a user-choosable string. Assume that "user" and
     "compute" exist for example.

     Another might be "PMATCH", which would be the definition with
     case constants translated into PMATCH versions.

     For the moment, as per all the names that talk of "userdefs", the
     only useful tag is "user".
  *)

  val const_eq_ref : Abbrev.conv ref
  val elim_triv_literal_CONV : Abbrev.conv
  val one_line_ify : PmatchHeuristics.pmatch_heuristic option -> thm -> thm
  val LIST_HALF_MK_ABS : thm -> thm

end
