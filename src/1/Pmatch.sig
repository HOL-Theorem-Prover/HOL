signature Pmatch =
sig

  type term = Term.term
  type thm = Thm.thm
  type thry = {Thy : string, Tyop : string} ->
              {case_const : term, constructors : term list} option

   datatype pattern
        = GIVEN   of term * int
        | OMITTED of term * int

   val allow_new_clauses : bool ref

   val choose_pat_col_fun : (Term.term list list -> int) ref
   val skip_irrelevant_pat_rows : bool ref

   val choose_pat_col___first_non_var : (Term.term list list -> int)
   val choose_pat_col___first_col : (Term.term list list -> int)
   val pat_of : pattern -> term
   val givens : pattern list -> term list

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}
   val mk_pattern_fn : thry -> (term * term) list -> term

   (* case expression manipulation functions *)
   val mk_case : thry -> term * (term * term) list -> term
   val dest_case : thry -> term -> term * term * (term * term) list
   val is_case : thry -> term -> bool
   val strip_case : thry -> term -> term * (term * term) list

end
