signature nomdatatype =
sig

  include Abbrev
  val new_type_step1 : string -> {vp:term,lp:term} ->
                       {term_ABS_pseudo11 : thm,
                        term_REP_11 : thm,
                        term_REP_t : term,
                        term_ABS_t : term,
                        absrep_id : thm,
                        repabs_pseudo_id : thm,
                        genind_term_REP : thm,
                        genind_exists : thm,
                        newty : hol_type,
                        termP : term}

  val termP_removal :
      {elimth : thm, absrep_id : thm, tpm_def : thm, termP : term, repty : hol_type} ->
      term -> thm

  (* datatype utility functions *)
  val rpt_hyp_dest_conj : thm -> thm
  val elim_unnecessary_atoms : {finite_fv:thm} -> thm list -> thm -> thm
  val sort_uvars : conv
  val rename_vars : (string * string) list -> conv
  val lift_exfunction : {repabs_pseudo_id : thm, term_REP_t : term,
                         cons_info : {con_termP : thm, con_def : thm} list} ->
                        thm -> thm
  val prove_alpha_fcbhyp : {ppm:term, alphas: thm list, rwts: thm list} ->
                           thm -> thm

end


