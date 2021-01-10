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
  val partition_skip : int option -> (term * 'b fterm) list ->
                       (term * 'b fterm) list * (term * 'b fterm) list
  val inst_type_dterm : (hol_type,hol_type) subst * 'a dterm -> 'a dterm


  datatype action =
           Rewrite of rewrite list
         | Conv of (term -> Thm.thm * db fterm)

  and db =
      EndDb
    | Try of { Hcst : term, Rws : action, Tail : db }
    | NeedArg of db

  and rewrite =
      RW of { cst: term,           (* constant which the rule applies to *)
              ants: db dterm list, (* Antecedents of the `thm` *)
              lhs: pattern list,   (* patterns = constant args in lhs of thm *)
              npv: int,            (* number of distinct pat vars in lhs *)
              rhs: db dterm,
              thm: Thm.thm };      (* thm we use for rewriting *)

  type compset
  val empty_rws : unit -> compset
  val from_list : thm list -> compset
  val add_extern : term * int * (term -> thm * db fterm) -> compset -> unit
  val add_thms : thm list -> compset -> unit
  val add_thmset : string -> compset -> unit

  val scrub_const : compset -> term -> unit
  val scrub_thms : thm list -> compset -> unit
  val from_term : compset * term list * term -> db dterm
  val set_skip : compset -> string * string -> int option -> unit

  datatype transform
    = Conversion of (term -> thm * db fterm)
    | RRules of thm list

  val deplist : compset -> ((string * string) * transform list) list
  val no_transform : compset -> (string * string) list

end
