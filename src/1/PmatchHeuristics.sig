signature PmatchHeuristics =
sig

   type term = Term.term
   type thm = Thm.thm
   type thry = {Thy : string, Tyop : string} ->
               {case_const : term, constructors : term list} option
   type pmatch_heuristic = {skip_rows : bool, (* skip splitting for redundant rows? *)
                            collapse_cases : bool, (* collapse cases that lead to the same result ? *)
                            (* given a list of rows of patterns, which column to split on? *) 
                            col_fun : thry -> term list list -> int }

   (* some predefined heuristics *)  
   val pheu_classic : pmatch_heuristic (* HOL 4's old heuristic *)
   val pheu_first_row : pmatch_heuristic 
   val pheu_constr_prefix : pmatch_heuristic
   val pheu_qba : pmatch_heuristic  (* the recommended one *)
   val pheu_cqba : pmatch_heuristic  
   val pheu_first_col : pmatch_heuristic  
   val pheu_last_col : pmatch_heuristic  

   (* A heuristic based on column ranks. Given a pattern match matrix like

      p_11 ... p_1n
      ... 
      p_m1 --- p_mn

      and a list of ranking functions prheuL = [r_1, ... r_j]. The 
      heuristic pheu_rank applies all ranking functions to all columns.
      Let's denote the result of "r_i current_thyr [p_k1, ... pkm]" with
      c_ik. It then picks column i such that [c_1i, ... c_ji] is maximal
      accroding to the lexicographic ordering of integers.
   *)
   val pheu_rank : (thry -> term list -> int) list -> pmatch_heuristic

   (* some ranking functions *)
   val prheu_first_row : thry -> term list -> int
   val prheu_constr_prefix : thry -> term list -> int
   val prheu_small_branching_factor : thry -> term list -> int
   val prheu_arity : thry -> term list -> int

   (* A comparison for the results of heuristic application 
      (list of pattern lists, resulting decision tree) *)
   type pmatch_heuristic_res_compare = (term list list * term) Lib.cmp
   val pmatch_heuristic_cases_cmp : pmatch_heuristic_res_compare (* few cases are good *)
   val pmatch_heuristic_size_cmp : pmatch_heuristic_res_compare (* small terms are good *)

   (* Using such comparisons, we can supply multiple heuristics and choose the best results.
      For technical reasons, this function might be stateful and therefore get's unit arguments.

      The usage of a heu_fun by the Pmatch library is as follows. Heu_fun initialises the functions and returns a 
      compare function and a function heu_fun' which provides heuristics. As long as
      heu_fun' () provides fresh heuristics these are tried. Then the best result of all these
      heuristics according to the compare function is choosen. *)
   type pmatch_heuristic_fun = unit -> pmatch_heuristic_res_compare * (unit -> pmatch_heuristic option)

   val default_heuristic_fun : pmatch_heuristic_fun
   val classic_heuristic_fun : pmatch_heuristic_fun

   (* An exhaustive heuristic_fun. It tries all possibilities and very quickly blows up!
      Only usable for very small examples! *)
   val exhaustive_heuristic_fun : pmatch_heuristic_res_compare -> pmatch_heuristic_fun 

   (* custom pmatch_heuristic_fun can be easiest constructed by an explicit list of heuristics and
      a compare function *)
   val pmatch_heuristic_list : pmatch_heuristic_res_compare -> pmatch_heuristic list -> pmatch_heuristic_fun

   (* A list of useful heuristics to be used with pmatch_heuristic_list *)
   val default_heuristic_list : pmatch_heuristic list


   (* The pmatch_heuristic_fun to be used by default and various functions to set it *)
   val pmatch_heuristic : pmatch_heuristic_fun ref 

   val set_heuristic : pmatch_heuristic -> unit
   val set_heuristic_fun : pmatch_heuristic_fun -> unit
   val set_heuristic_list_size : pmatch_heuristic list -> unit
   val set_heuristic_list_cases : pmatch_heuristic list -> unit
   val set_default_heuristic : unit -> unit
   val set_classic_heuristic : unit -> unit

   val with_classic_heuristic : ('a -> 'b) -> ('a -> 'b)
   val with_heuristic : pmatch_heuristic -> ('a -> 'b) -> ('a -> 'b)
   val is_classic : unit -> bool
end
