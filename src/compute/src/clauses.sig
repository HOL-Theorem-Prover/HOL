signature clauses =
sig

  include Abbrev
  datatype pattern =
           Pvar of int
         | Papp of { Head : term, Args : pattern list}

  datatype 'a fterm = (* order of Args: outermost ahead *)
      CST of { Head : term,
               Args : (term * 'a fterm) list,
               Rws  : 'a,
               Skip : int option }
    | NEUTR
    | CLOS of { Env : 'a fterm list, Term : 'a dterm }
  and 'a dterm =
      Bv of int
    | Fv
    | Cst of term * ('a * int option) ref
    | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
    | Abs of 'a dterm

  val is_skip : 'a * 'b fterm -> bool
  val inst_type_dterm : (hol_type,hol_type) subst * 'a dterm -> 'a dterm


  datatype action =
           Rewrite of rewrite list
         | Conv of (term -> Thm.thm * db fterm)

  and db =
      EndDb
    | Try of { Hcst : term, Rws : action, Tail : db }
    | NeedArg of db

  and rewrite =
      RW of { cst: term,          (* constant which the rule applies to *)
              lhs: pattern list,  (* patterns = constant args in lhs of thm *)
	      npv: int,           (* number of distinct pat vars in lhs *)
	      rhs: db dterm,
              thm: Thm.thm }      (* thm we use for rewriting *)

  type comp_rws
  val empty_rws : unit -> comp_rws
  val from_list : thm list -> comp_rws
  val add_extern : term * int * (term -> thm * db fterm) -> comp_rws -> unit
  val add_thms : thm list -> comp_rws -> unit

  val scrub_const : comp_rws -> term -> unit
  val scrub_thms : thm list -> comp_rws -> unit
  val from_term : comp_rws * term list * term -> db dterm
  val set_skip : comp_rws -> string * string -> int option -> unit

end
