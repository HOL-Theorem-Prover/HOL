signature Pmatch =
sig

  type term = Term.term
  type thm = Thm.thm
  type thry = {Thy : string, Tyop : string} ->
              {case_const : term, constructors : term list} option
  type pmatch_heuristic = {skip_rows : bool, (* skip splitting for redundant rows? *)
                           collapse_cases : bool, (* collapse cases that lead to the same result ? *)
                          (* given a list of rows of patterns, which column to split on? *) 
                           col_fun : thry -> term list list -> int }

   datatype pattern
        = GIVEN   of term * int
        | OMITTED of term * int

   val allow_new_clauses : bool ref
   val pat_of : pattern -> term
   val givens : pattern list -> term list

   val mk_functional : thry -> term -> {functional:term, pats: pattern list}
   val mk_pattern_fn : thry -> (term * term) list -> term

   (* case expression manipulation functions *)
   val mk_case : thry -> term * (term * term) list -> term
   val dest_case : thry -> term -> term * term * (term * term) list
   val is_case : thry -> term -> bool
   val strip_case : thry -> term -> term * (term * term) list

   (* some predefined heuristics *)  
   val pheu_classic : pmatch_heuristic (* HOL 4's old heuristic *)
   val pheu_first_row : pmatch_heuristic
   val pheu_constr_prefix : pmatch_heuristic
   val pheu_qba : pmatch_heuristic  (* the recommended one *)
   val pheu_cqba : pmatch_heuristic  
   val pheu_first_col : pmatch_heuristic  
   val pheu_last_col : pmatch_heuristic  

   val pheu_rank : (thry -> term list -> int) list -> pmatch_heuristic
   val prheu_first_row : thry -> term list -> int
   val prheu_constr_prefix : thry -> term list -> int
   val prheu_small_branching_factor : thry -> term list -> int
   val prheu_arity : thry -> term list -> int

   (* Stateful function that can provide one after another a list of
      heuristics, which are all tried. The best result is then used. *)
   type pmatch_heuristic_res_compare = ((term list * ((term * int -> pattern) * int) * term list) list * term) Lib.cmp
   type pmatch_heuristic_fun = unit -> pmatch_heuristic_res_compare * (unit -> pmatch_heuristic option)

   val pmatch_heuristic_cases_cmp : pmatch_heuristic_res_compare
   val pmatch_heuristic_size_cmp : pmatch_heuristic_res_compare
   val pmatch_heuristic : pmatch_heuristic_fun ref 

   (* construct the stateful function to try all the given heuristics *)
   val pmatch_heuristic_list : pmatch_heuristic_res_compare -> pmatch_heuristic list -> pmatch_heuristic_fun

   val default_heuristic_list : pmatch_heuristic list
   val default_heuristic_fun : pmatch_heuristic_fun
   val classic_heuristic_fun : pmatch_heuristic_fun

   (* An exhaustive heuristic_fun. It tries all possibilities and very quickly blows up!
      Only usable for very small examples! *)
   val exhaustive_heuristic_fun : pmatch_heuristic_res_compare -> pmatch_heuristic_fun 

   val set_heuristic : pmatch_heuristic -> unit
   val set_heuristic_fun : pmatch_heuristic_fun -> unit
   val set_heuristic_list_size : pmatch_heuristic list -> unit
   val set_heuristic_list_cases : pmatch_heuristic list -> unit
   val set_default_heuristic : unit -> unit
   val set_classic_heuristic : unit -> unit

   val with_classic_heuristic : ('a -> 'b) -> ('a -> 'b)
   val with_heuristic : pmatch_heuristic -> ('a -> 'b) -> ('a -> 'b)
end
