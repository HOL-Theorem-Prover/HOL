signature constrFamiliesLib =
sig
  include Abbrev


  (**********************)
  (* Constructors       *)
  (**********************)

  (* A constructor is a combination of a term with
     a list of names for all it's arguments *)
  type constructor 

  (* [mk_constructor c arg_names] generate a constructor [c]
     with argument names [arg_names] *)
  val mk_constructor : term -> string list -> constructor

  (* check whether a constructor has no arguments *)
  val constructor_is_const : constructor -> bool

  (* [mk_constructor_term vs constr] construct a term 
     corresponding to [constr]. For the arguments
     variables are generated. These variables are
     distinct from the ones provided in the argument [vs].
     The resulting term as well the used argument vars are
     returned. *)
  val mk_constructor_term : term list -> constructor -> (term * term list)
  (* [match_constructor constr t] tries destruct [t] as a constructor
     of [constr]. It returns NONE, if there is no match. Otherwise
     the main constructor functions + labelled args. *)
  val match_constructor : constructor -> term -> (term * (string * term) list) option

  (* We usually consider lists of constructors. It is an abstract
     type that should only be used via [make_constructorList]. *)
  type constructorList

  (* [mk_constructorList exh constrs] makes a new constructorList.
     [exh] states whether the list is exhaustive, i.e. wether all values
     of the type can be constructed  via a constructor in this list *)
  val mk_constructorList : bool -> constructor list -> constructorList

  (* [make_constructorList exh constrs] is a convenience functions
     that maps [mk_constructor] over constrs before calling
     [mk_constructorList]. *) 
  val make_constructorList : bool -> (term * string list) list -> constructorList

  (************************)
  (* Constructor Families *)
  (************************)

  (* a constructor family is a list of constructors,
     a case-split function and various theorems *)
  type constructorFamily

  (* Get the rewrites stored in a constructor family, these
     are theorems that use that all constructors are distinct
     to each other and injective. *)
  val constructorFamily_get_rewrites : constructorFamily -> thm

  (* Get the case-cong stored in a constructor family. *)
  val constructorFamily_get_case_cong : constructorFamily -> thm

  (* Get the ssfrag resulting form all the stuff 
     in a constructor family. *)
  val constructorFamily_get_ssfrag : constructorFamily -> simpLib.ssfrag

  (* Get the case-split theorem for the family. *)
  val constructorFamily_get_case_split : constructorFamily -> thm

  (* If the constructor family is exhaustive, a theorem stating
     this exhaustiveness. *)
  val constructorFamily_get_nchotomy_thm_opt : constructorFamily -> thm option

  (* Get the constructors of the family. *)
  val constructorFamily_get_constructors : constructorFamily -> bool * (term * string list) list

  (* [mk_constructorFamily (constrL, case_split_tm, tac)]
     make a new constructor family. It consists of the constructors
     [constrL], the case split constant [case_split_tm]. The
     resulting proof obligations are proofed by tactic [tac]. *)
  val mk_constructorFamily : constructorList * term * tactic -> constructorFamily

  (* [get_constructorFamily_proofObligations] returns the
     proof obligations that occur when creating a new constructor family 
     via [mk_constructorFamily]. *) 
  val get_constructorFamily_proofObligations : constructorList * term -> term

  (* [set_constructorFamily] sets the proof obligations that occur when
     ruung [mk_constructorFamily] using goalStack. *)
  val set_constructorFamily : constructorList * term -> Manager.proofs

  (* [constructorFamily_of_typebase ty] extracts the constructor family
     for the given type [ty] from typebase. *)
  val constructorFamily_of_typebase : hol_type -> constructorFamily
 

  (************************)
  (* Compile DBs          *)
  (************************)

  (* A compile database combines constructor families,
     an ssfrag and arbitrary compilation funs. *) 
     

  (* A compilation fun gets a column, i.e. a list of
     terms together with a list of free variables in this term.
     For this column a expansion theorem of the form
     ``!ff x. ff x = ...``, the number of  cases in this expansion
     theorem and an ssfrag should be returned. *)
  type pmatch_compile_fun = (term list * term) list -> (thm * int * simpLib.ssfrag) option

  (* A compilation fun gets a column, i.e. a list of
     terms together with a list of free variables in this term.
     For this column an nchotomy theorem as well as the number of
     entries in this nchotomy should be returned. *)
  type pmatch_nchotomy_fun = (term list * term) list -> (thm * int) option

  (* A database for pattern compilation *)
  type pmatch_compile_db = {
    pcdb_compile_funs  : pmatch_compile_fun list,
    pcdb_nchotomy_funs : pmatch_nchotomy_fun list,
    pcdb_constrFams    : (constructorFamily list) TypeNet.typenet,
    pcdb_ss            : simpLib.ssfrag
  }

  (* empty db *)
  val empty : pmatch_compile_db 

  (* a default db implemented as a reference *)
  val thePmatchCompileDB : pmatch_compile_db ref

  (* A database represents essentially a compile fun. 
     This functions combines all the contents of a db to
     turn it into a compile fun.  *)
  val pmatch_compile_db_compile : pmatch_compile_db -> pmatch_compile_fun
  (* This tries to find the family used by a call to 
     [pmatch_compile_db_compile]. If this call picks a
     use a hand-written compile-fun, [NONE] is returned. Similarly,
     if no constructor family is found for this column. *)
  val pmatch_compile_db_compile_cf : pmatch_compile_db ->
     (term list * term) list -> constructorFamily option

  (* This tries to find an nchotony theorem for the given column. *)
  val pmatch_compile_db_compile_nchotomy : pmatch_compile_db ->
     (term list * term) list -> thm option

  (* This tries to destruct a term as a destructor. It looks
     up in the given DB all possible constructors and tries to
     apply match_constructor. *)
  val pmatch_compile_db_dest_constr_term : pmatch_compile_db ->
     term -> (term * (string * term) list) option

  (* add a compile fun to a db *)
  val pmatch_compile_db_add_compile_fun :
     pmatch_compile_db -> pmatch_compile_fun -> pmatch_compile_db

  (* add an nchotomy fun to a db *)
  val pmatch_compile_db_add_nchotomy_fun :
     pmatch_compile_db -> pmatch_nchotomy_fun -> pmatch_compile_db

  (* add a constructorFamily to a db *)
  val pmatch_compile_db_add_constrFam :
     pmatch_compile_db -> constructorFamily -> pmatch_compile_db

  (* add a ssfrag to a db *)
  val pmatch_compile_db_add_ssfrag :
     pmatch_compile_db -> simpLib.ssfrag -> pmatch_compile_db

  (* add a congruence rules to a db *)
  val pmatch_compile_db_add_congs : pmatch_compile_db -> thm list -> pmatch_compile_db

  (* removes all information for type from a db *)
  val pmatch_compile_db_remove_type : pmatch_compile_db -> hol_type -> pmatch_compile_db

  (* add a compile_fun to default db *)
  val pmatch_compile_db_register_compile_fun : pmatch_compile_fun -> unit

  (* add a nchotomy_fun to default db *)
  val pmatch_compile_db_register_nchotomy_fun : pmatch_nchotomy_fun -> unit

  (* add a constructor family to default db *)
  val pmatch_compile_db_register_constrFam : constructorFamily -> unit

  (* add a ssfrag to default db *)
  val pmatch_compile_db_register_ssfrag : simpLib.ssfrag -> unit

  (* add a congruence rules to default db *)
  val pmatch_compile_db_register_congs : thm list -> unit

  (* removes all information for type from default db *)
  val pmatch_compile_db_clear_type : hol_type -> unit


  (************************)
  (* Compile Funs         *)
  (************************)
  
  (* Compilation fun that turns a column of literals into
     a large if-then-else case distinction. It is
     present automatically in the default db. *)
  val literals_compile_fun : pmatch_compile_fun

end
