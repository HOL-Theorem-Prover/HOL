signature clauses =
sig

  include Abbrev
  datatype pattern =
           Pvar of int
         | Papp of { Head : term, Args : pattern list}

  datatype 'a fterm = (* order of Args: outermost ahead *)
      CST of { Head : term,
               Args : (term * 'a fterm * Thm.thm) list,
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
  val partition_skip : int option -> (term * 'b fterm * Thm.thm) list ->
                       (term * 'b fterm * Thm.thm) list * (term * 'b fterm * Thm.thm) list
  val inst_type_dterm : (hol_type,hol_type) subst * 'a dterm -> 'a dterm


  datatype action =
           Rewrite of rewrite list
         | Conv of (term -> Thm.thm)

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
  val empty_rws : compset
  val seal : compset -> compset
  val copy : compset -> compset
  val from_list : thm list -> compset
  val add_extern : term * int * (term -> thm) -> compset -> compset
  val add_thms : thm list -> compset -> compset
  val add_thmset : string -> compset -> compset

  val scrub_const : compset -> term -> compset
  val scrub_thms : thm list -> compset -> compset
  val from_term : compset * term list * term -> compset * db dterm
  val set_skip : compset -> string * string -> int option -> compset

  datatype transform
    = Conversion of (term -> thm)
    | RRules of thm list

  val deplist : compset -> ((string * string) * transform list) list
  val no_transform : compset -> (string * string) list

end
