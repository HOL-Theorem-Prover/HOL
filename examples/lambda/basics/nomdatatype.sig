signature nomdatatype =
sig

  include Abbrev
  type coninfo = {con_termP : thm, con_def : thm}

  val new_type_step1 : string -> {vp:term,lp:term,existence:thm} ->
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
      {elimth : thm, absrep_id : thm, tpm_def : thm, termP : term,
       repty : hol_type} ->
      term -> thm
      (* tpm_def should be a theorem of the form
           pm pi t = ABS (gtpm pi (REP t))
         where pm is the term that the user expects to see as the
         permutation action for the new type.  I.e., this will presumably
         be something like ``pmact something``. *)


  val define_permutation : { name_pfx : string, name : string,
                             term_REP_t : term, term_ABS_t : term,
                             absrep_id : thm, repabs_pseudo_id : thm,
                             cons_info : coninfo list, newty : hol_type,
                             genind_term_REP : thm} ->
                           { tpm_thm : thm, term_REP_tpm : thm,
                             t_pmact_t : term, tpm_t : term}

  (* datatype utility functions *)
  val rpt_hyp_dest_conj : thm -> thm
  val elim_unnecessary_atoms : {finite_fv:thm} -> thm list -> thm -> thm
  val sort_uvars : conv
  val rename_vars : (string * string) list -> conv
  val lift_exfunction : {repabs_pseudo_id : thm, term_REP_t : term,
                         cons_info : coninfo list} ->
                        thm -> thm
  val prove_alpha_fcbhyp : {ppm:term, alphas: thm list, rwts: thm list} ->
                           thm -> thm
  val defined_const : thm -> term

end


