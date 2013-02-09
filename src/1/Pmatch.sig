signature Pmatch =
sig

  type term = Term.term
  type thm = Thm.thm
  type thry = {Thy : string, Tyop : string} ->
              {case_const : term, constructors : term list} option
  type pmatch_heuristic = {skip_rows : bool, (* skip splitting for redundant rows? *)
                          (* given a list of rows of patterns, which column to split on? *) 
                           col_fun : thry -> term list list -> int }

   datatype pattern
        = GIVEN   of term * int
        | OMITTED of term * int

   val allow_new_clauses : bool ref
   val pat_of : pattern -> term
   val givens : pattern list -> term list

   val mk_functional : pmatch_heuristic -> thry -> term -> {functional:term, pats: pattern list}
   val mk_pattern_fn : pmatch_heuristic -> thry -> (term * term) list -> term

   (* case expression manipulation functions *)
   val mk_case : thry -> term * (term * term) list -> term
   val dest_case : thry -> term -> term * term * (term * term) list
   val is_case : thry -> term -> bool
   val strip_case : thry -> term -> term * (term * term) list

   (* some predefined heuristics *)  
   val pheu_classic : pmatch_heuristic (* HOL 4's old heuristic *)
   val pheu_first_row : pmatch_heuristic
   val pheu_constr_prefix : pmatch_heuristic

   val pheu_rank : (thry -> term list -> int) list -> pmatch_heuristic
   val prheu_first_row : thry -> term list -> int
   val prheu_constr_prefix : thry -> term list -> int

   val default_pheu : pmatch_heuristic ref (* The one used by default *)

end
