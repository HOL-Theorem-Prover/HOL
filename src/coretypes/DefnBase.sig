signature DefnBase =
sig
  type term = Term.term
  type thm  = Thm.thm

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
  *)
  val register_defn : string -> thm -> unit
  val lookup_defn : term -> string -> thm option

  val register_indn : thm * term list -> unit
  val lookup_indn : term -> (thm * term list) option

  (* register_defn is given a tag and a theorem which is a conjunction of
     possibly universally quantified equations.  The machinery here
     will create a sub-conjunction of the clauses per constant (and this is
     what is returned by lookup_defn).

     Induction theorems have some number of induction variables (P1,
     P2, ..) where each corresponds to a defined constant. This list
     of constants is what is passed into register_indn alongside the
     induction theorem. When a term is looked up, if lookup_indn t
     returns SOME (th, ts), then t will be among the ts.
   *)

  val const_eq_ref : Abbrev.conv ref
  val elim_triv_literal_CONV : Abbrev.conv
  val one_line_ify : PmatchHeuristics.pmatch_heuristic option -> thm -> thm

end
