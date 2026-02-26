structure trace_step_dtype =
struct

(* Proof trace step: typed representation of each inference rule application.
   Parameterized on ('a, 'b, 'c) = (thm, term, hol_type) to avoid
   opaque-type-identity issues across the kernel/signature boundary. *)
datatype ('a, 'b, 'c) trace_step =
    TR_ASSUME      of 'a * 'b
  | TR_REFL        of 'a * 'b
  | TR_BETA_CONV   of 'a * 'b
  | TR_SUBST       of 'a * {redex: 'b, residue: 'a} list * 'b * 'a
  | TR_ABS         of 'a * 'a * 'b
  | TR_GEN_ABS     of 'a * 'a * 'b option * 'b list
  | TR_INST_TYPE   of 'a * 'a * {redex: 'c, residue: 'c} list
  | TR_DISCH       of 'a * 'a * 'b
  | TR_MP          of 'a * 'a * 'a
  | TR_ALPHA       of 'a * 'b * 'b
  | TR_SYM         of 'a * 'a
  | TR_TRANS       of 'a * 'a * 'a
  | TR_MK_COMB     of 'a * 'a * 'a
  | TR_AP_TERM     of 'a * 'a * 'b
  | TR_AP_THM      of 'a * 'a * 'b
  | TR_EQ_MP       of 'a * 'a * 'a
  | TR_EQ_IMP_RULE1 of 'a * 'a
  | TR_EQ_IMP_RULE2 of 'a * 'a
  | TR_SPEC        of 'a * 'a * 'b
  | TR_GEN         of 'a * 'a * 'b
  | TR_GENL        of 'a * 'a * 'b list
  | TR_EXISTS      of 'a * 'a * 'b * 'b
  | TR_CHOOSE      of 'a * 'a * 'a * 'b
  | TR_CONJ        of 'a * 'a * 'a
  | TR_CONJUNCT1   of 'a * 'a
  | TR_CONJUNCT2   of 'a * 'a
  | TR_DISJ1       of 'a * 'a * 'b
  | TR_DISJ2       of 'a * 'a * 'b
  | TR_DISJ_CASES  of 'a * 'a * 'a * 'a
  | TR_NOT_INTRO   of 'a * 'a
  | TR_NOT_ELIM    of 'a * 'a
  | TR_CCONTR      of 'a * 'a * 'b
  | TR_INST        of 'a * 'a * {redex: 'b, residue: 'b} list
  | TR_Beta        of 'a * 'a
  | TR_Mk_comb     of 'a * 'a * 'a * 'a
  | TR_Mk_abs      of 'a * 'a * 'a * 'b
  | TR_Specialize  of 'a * 'a * 'b
  | TR_ORACLE      of 'a * string
  | TR_AXIOM       of 'a * 'b
  | TR_DEF_TYOP    of 'a * 'a * string * string
  | TR_DEF_SPEC    of 'a * 'a * string * string list
  | TR_NAME        of 'a * string * string  (* thm, source_theory, name *)
  | TR_LOAD        of 'a * string * int     (* thm, source_theory, src_trace_id *)
  | TR_COMPUTE_INIT of (string * 'b) list  (* cval_terms *)
                     * 'c                   (* cval_type *)
                     * 'c                   (* num_type *)
                     * (string * 'a) list   (* char_eqns *)
  | TR_COMPUTE     of 'a * 'a list * 'b    (* result, code_eqn_thms, input *)

end
