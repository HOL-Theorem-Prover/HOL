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
  (* turn shallow case-terms into *)
  (* deeply embedded ones         *)
  (********************************)

  val convert_case : term -> term
  val PMATCH_INTRO_CONV : conv


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

  val PMATCH_CASE_SPLIT_CONV :
     ((term * (term list * term) list) list -> int) -> term -> thm

  val PMATCH_CASE_SPLIT_CONV_GEN :
     ssfrag list ->
     constrFamiliesLib.pmatch_compile_db ->
     ((term * (term list * term) list) list -> int) -> term -> thm

  val PMATCH_CASE_SPLIT_CONV_GENCALL :
     ssfrag list * (term -> thm) option ->
     constrFamiliesLib.pmatch_compile_db ->
     ((term * (term list * term) list) list -> int) -> term -> thm

end
