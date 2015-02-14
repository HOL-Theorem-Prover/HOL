signature constrFamiliesLib =
sig
  include Abbrev


  (**********************)
  (* Constructors       *)
  (**********************)

  (* A constructor is a combination of a term with
     a list of names for all it's arguments *)
  type constructor 

  (* check whether a constructor has no arguments *)
  val constructor_is_const : constructor -> bool

  (* [mk_constructor_term vs constr] construct a term 
     corresponding to [constr]. For the arguments
     variables are generated. These variables are
     distinct from the ones provided in the argument [vs].
     The resulting term as well the used argument vars are
     returned. *)
  val mk_constructor_term : term list -> constructor -> (term * term list)

  (* We usually consider lists of constructors. It is an abstract
     type that should only be used via [make_constructorList]. *)
  type constructorList

  (* [make_constructorList exh constrs] makes a new constructorList.
  *)
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

  (* Get the case-split theorem for the family. *)
  val constructorFamily_get_case_split : constructorFamily -> thm

  (* If the constructor family is exhaustive, a theorem stating
     this exhaustiveness. *)
  val constructorFamily_get_nchotomy_thm_opt : constructorFamily -> thm option


  (* [mk_constructorFamily (constrL, case_split_tm, tac)]
     make a new constructor family. It consists of the constructors
     [constrL], the case split constant [case_split_tm]. The
     resulting proof obligations are proofed by tactic [tac]. *)
  val mk_constructorFamily : constructorList * term * tactic -> constructorFamily

  (* [get_constructorFamily_proofObligations] returns the
     proof obligations that occur when creating a new constructor family. *) 
  val get_constructorFamily_proofObligations : constructorList * term -> term

  (* [set_constructorFamily] sets the proof obligations
     using goalStack *)
  val set_constructorFamily : constructorList * term -> Manager.proof




  val constructorFamily_of_typebase : hol_type -> constructorFamily
 
end
