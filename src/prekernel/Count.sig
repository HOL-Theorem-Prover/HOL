(* ===================================================================== *)
(* FILE          : Count.sig                                             *)
(* DESCRIPTION   : Signature for inference counting.                     *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : 1998                                                  *)
(* ===================================================================== *)


signature Count =
sig

  datatype rule = Assume | Refl | Beta | Subst | Abs | Disch | Mp | InstType
                | MkComb | ApTerm | ApThm | Alpha
                | Sym | Trans | EqMp | EqImpRule | Inst
                | Spec | Gen
                | Exists | Choose
                | Conj | Conjunct1 | Conjunct2
                | Disj1 | Disj2 | DisjCases
                | NotIntro | NotElim  | Ccontr | GenAbs
                | Definition | Axiom | Disk | Oracle;

  val counting_thms   : bool -> unit
  val reset_thm_count : unit -> unit
  val inc_count       : rule -> unit

  val thm_count : unit ->
   {ASSUME : int, REFL : int,
    BETA_CONV : int, SUBST : int,
    ABS : int, DISCH : int,
    MP : int, INST_TYPE : int,
    MK_COMB : int, AP_TERM : int,
    AP_THM : int, ALPHA : int,
    SYM : int, TRANS : int,
    EQ_MP : int, EQ_IMP_RULE : int,
    INST : int, SPEC : int, GEN : int,
    EXISTS : int, CHOOSE : int,
    CONJ : int, CONJUNCT1 : int,
    CONJUNCT2 : int, DISJ1 : int,
    DISJ2 : int, DISJ_CASES : int,
    NOT_INTRO : int, NOT_ELIM : int,
    CCONTR : int, GEN_ABS : int,
    definition : int, axiom : int,
    from_disk : int, oracle :int,
    total :int }

  type meter
  val mk_meter  : unit -> meter
  val read   : meter -> {axioms:int,defns:int,oracles:int,disk:int,prims:int}
  val report : {axioms:int,defns:int,oracles:int,disk:int,prims:int} -> unit
  val apply  : ('a -> 'b) -> 'a -> 'b

end;
