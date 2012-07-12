(* ===================================================================== *)
(* FILE          : Count.sig                                             *)
(* DESCRIPTION   : Signature for inference counting.                     *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : 1998                                                  *)
(* ===================================================================== *)

signature Count =
sig

  datatype rule =
     Abs
   | Alpha
   | ApTerm
   | ApThm
   | Assume
   | Axiom
   | Beta
   | Ccontr
   | Choose
   | Conj
   | Conjunct1
   | Conjunct2
   | Definition
   | Disch
   | Disj1
   | Disj2
   | DisjCases
   | Disk
   | EqImpRule
   | EqMp
   | Exists
   | Gen
   | GenAbs
   | Inst
   | InstType
   | MkComb
   | Mp
   | NotElim
   | NotIntro
   | Oracle
   | Refl
   | Spec
   | Subst
   | Sym
   | Trans

  val counting_thms: bool -> unit
  val reset_thm_count: unit -> unit
  val inc_count: rule -> unit

  val thm_count:
     unit -> {ABS: int,
              ALPHA: int,
              AP_TERM: int,
              AP_THM: int,
              ASSUME: int,
              BETA_CONV: int,
              CCONTR: int,
              CHOOSE: int,
              CONJ: int,
              CONJUNCT1: int,
              CONJUNCT2: int,
              DISCH: int,
              DISJ1: int,
              DISJ2: int,
              DISJ_CASES: int,
              EQ_IMP_RULE: int,
              EQ_MP: int,
              EXISTS: int,
              GEN: int,
              GEN_ABS: int,
              INST: int,
              INST_TYPE: int,
              MK_COMB: int,
              MP: int,
              NOT_ELIM: int,
              NOT_INTRO: int,
              REFL: int,
              SPEC: int,
              SUBST: int,
              SYM: int,
              TRANS: int,
              axiom: int,
              definition: int,
              from_disk: int,
              oracle: int,
              total: int}

  type meter

  val mk_meter: unit -> meter
  val read:
     meter -> {axioms: int, defns: int, oracles: int, disk: int, prims: int}
  val report:
     {axioms: int, defns: int, oracles: int, disk: int, prims: int} -> unit
  val apply: ('a -> 'b) -> 'a -> 'b

end
