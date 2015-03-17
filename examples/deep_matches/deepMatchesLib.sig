signature deepMatchesLib =
sig
  include Abbrev
  type ssfrag = simpLib.ssfrag
  (********************************)
  (* eliminating select           *)
  (********************************)

  (* PMATCH leads to selects consisting of
     conjunctions that determine the value of one
     component of the variable. An example is

     @x. SND (SND x = ..) /\ (FST x = ..) /\ (FST (SND x) = ..)

     by resorting these conjunctions, one can
     easily derive a form

     @x. x = ..

     and therefore eliminate the select operator.
     This is done by the following conversion + ssfrag. *)
  val ELIM_FST_SND_SELECT_CONV : conv
  val elim_fst_snd_select_ss : ssfrag


  (********************************)
  (* convert between              *)
  (* case and pmatch              *)
  (********************************)

  (* without proof convert a case to a pmatch expression.
     If the flag is set, optimise the result by
     introducing wildcards reordering rows ... *)
  val case2pmatch : bool -> term -> term

  (* convert a pmatch expression to a case expression.
     Fails, if the pmatch expression uses guards or
     non-constructor patterns. *)
  val pmatch2case : term -> term

  val PMATCH_INTRO_CONV : conv
  val PMATCH_INTRO_CONV_NO_OPTIMISE : conv
  val PMATCH_ELIM_CONV : conv


  (********************************)
  (* simplify PMATCH-terms        *)
  (********************************)

  (* There are various ways of simplifying
     PMATCH. One can e.g. remove redundant rows
     or partially evaluate it. The conversion
     PMATCH_SIMP_CONV does this. *)
  val PMATCH_SIMP_CONV : conv

  (* There is also a more generic version that
     allows to provide extra ssfrags. This might
     be handy, if the PMATCH contains functions
     not known by the default methods. *)
  val PMATCH_SIMP_CONV_GEN : ssfrag list -> conv

  (* corresponding ssfrags *)
  val PMATCH_SIMP_GEN_ss : ssfrag list -> ssfrag
  val PMATCH_SIMP_ss : ssfrag

  (* PMATCH_SIMP_CONV consists of various
     component conversions. These can be used
     independently as well. *)
  val PMATCH_REMOVE_ARB_CONV : conv
  val PMATCH_REMOVE_ARB_CONV_GEN : ssfrag list -> conv

  val PMATCH_CLEANUP_PVARS_CONV : conv

  val PMATCH_CLEANUP_CONV : conv
  val PMATCH_CLEANUP_CONV_GEN : ssfrag list -> conv

  val PMATCH_SIMP_COLS_CONV : conv
  val PMATCH_SIMP_COLS_CONV_GEN : ssfrag list -> conv

  val PMATCH_EXPAND_COLS_CONV : conv


  (********************************)
  (* removing double variable     *)
  (* bindings                     *)
  (********************************)

  val PMATCH_REMOVE_DOUBLE_BIND_CONV_GEN : ssfrag list -> conv
  val PMATCH_REMOVE_DOUBLE_BIND_CONV : conv
  val PMATCH_REMOVE_DOUBLE_BIND_GEN_ss : ssfrag list -> ssfrag
  val PMATCH_REMOVE_DOUBLE_BIND_ss : ssfrag


  (********************************)
  (* removing GUARDS              *)
  (********************************)

  val PMATCH_REMOVE_GUARDS_CONV_GEN : ssfrag list -> conv
  val PMATCH_REMOVE_GUARDS_CONV : conv
  val PMATCH_REMOVE_GUARDS_GEN_ss : ssfrag list -> ssfrag
  val PMATCH_REMOVE_GUARDS_ss : ssfrag




  (********************************)
  (* removing PMATCH-terms        *)
  (* via lifting it to the nearest*)
  (* boolean term and then        *)
  (* unfolding                    *)
  (********************************)

  (* One can eliminate PMATCHs by unfolding all
     cases explicitly. This is often handy to
     prove properties about functions defined
     via pattern matches without the need to
     do the case-splits manually. 

     This tactic looks for the smallest wrapper
     around a PMATCH such that the term is of type
     bool. This term is then expanded into a big
     conjunction. For each case of the pattern match,
     one conjunct is created. *)
  val PMATCH_LIFT_BOOL_CONV : conv

  (* There is also a more generic version that
     allows to provide extra ssfrags. This might
     be handy, if the PMATCH contains functions
     not known by the default methods. *)
  val PMATCH_LIFT_BOOL_CONV_GEN : ssfrag list -> conv

  (* corresponding ssfrags *)
  val PMATCH_LIFT_BOOL_GEN_ss : ssfrag list -> ssfrag
  val PMATCH_LIFT_BOOL_ss : ssfrag

  (* A special case of lifting are function definitons,
     which use PMATCH. In order to use such definitions
     with the rewritig tools, it is often handy to
     move the PMATCH to the toplevel and introduce
     multiple cases, one case for each row of the
     PMATCH. This is automated by the following rules. *)

  val PMATCH_TO_TOP_RULE_GEN : ssfrag list -> rule
  val PMATCH_TO_TOP_RULE : rule


  (********************************)
  (* CASE SPLIT (pattern compile) *)
  (********************************)

  (*------------*)
  (* Heuristics *)
  (*------------*)

  (* A column heuristic is used to figure out, in
     which order to process columns. It gets a list of columns
     and returns, which one to pick. *)  
  type column_heuristic = (term * (term list * term) list) list -> int

  (* Many heuristics are build on ranking funs.
     A ranking fun assigns an integer to a column. Larger
     numbers are prefered. If two columns have the same
     value, either another ranking fun is used to decide or
     just the first one is used, if no ranking fun is available. *)
  type column_ranking_fun = term * (term list * term) list -> int
  val colHeu_rank : column_ranking_fun list -> column_heuristic

  val colRank_first_row : column_ranking_fun
  val colRank_first_row_constr : constrFamiliesLib.pmatch_compile_db -> column_ranking_fun
  val colRank_arity : constrFamiliesLib.pmatch_compile_db -> column_ranking_fun
  val colRank_constr_prefix : column_ranking_fun
  val colRank_small_branching_factor : constrFamiliesLib.pmatch_compile_db -> column_ranking_fun

  (* Some heuristics *)
  val colHeu_first_col : column_heuristic
  val colHeu_last_col : column_heuristic
  val colHeu_first_row : column_heuristic
  val colHeu_constr_prefix : column_heuristic
  val colHeu_cqba : constrFamiliesLib.pmatch_compile_db -> column_heuristic
  val colHeu_qba : constrFamiliesLib.pmatch_compile_db -> column_heuristic

  (* the default heuristic, currently it is
     colHeu_qba applied to the default db. However,
     this might change. You can just rely on a decent heuristic,
     that often works. No specific properties guarenteed. *)
  val colHeu_default : column_heuristic

  (*-------------*)
  (* COMPILATION *)
  (*-------------*)

  (* [PMATCH_CASE_SPLIT_CONV_GEN ssl db col_heu]
     is a conversion that tries to compile PMATCH expressions
     to decision trees using database [db], column heuristic
     [col_heu] and additional ssfrags [ssl]. *)
  val PMATCH_CASE_SPLIT_CONV_GEN :
     ssfrag list ->
     constrFamiliesLib.pmatch_compile_db ->
     column_heuristic -> conv

  (* A simplified version of PMATCH_CASE_SPLIT_CONV that
     uses the default database and default column heuristic as
     well as no extra ssfrags. *)
  val PMATCH_CASE_SPLIT_CONV : conv

  (* lets choose at least the heuristic *)
  val PMATCH_CASE_SPLIT_CONV_HEU : column_heuristic -> conv

  (* ssfrag corresponding to PMATCH_CASE_SPLIT_CONV_GEN *)
  val PMATCH_CASE_SPLIT_GEN_ss :
     ssfrag list ->
     constrFamiliesLib.pmatch_compile_db ->
     column_heuristic -> ssfrag

  (* ssfrag corresponding to PMATCH_CASE_SPLIT_CONV, since
     it needs to get the current version of the default db,
     it gets a unit argument. *)
  val PMATCH_CASE_SPLIT_ss : unit -> ssfrag

  (* lets choose at least the heuristic *)
  val PMATCH_CASE_SPLIT_HEU_ss : column_heuristic -> ssfrag

end
