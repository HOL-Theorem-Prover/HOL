open preamble intSimps;
open MiniMLTheory Print_astTheory;

val _ = new_theory "Print_astTermination";

(* ----------------- Termination proofs for Print_astTheory --------------- *)

fun register name def ind = 
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [(name ^ "_def", def)];
  in
    ()
  end


val (num_to_string_def, num_to_string_ind) =
  tprove_no_defn ((num_to_string_def, num_to_string_ind),
  wf_rel_tac `measure (\x.x)` >>
  srw_tac [ARITH_ss] []);
val _ = register "num_to_string" num_to_string_def num_to_string_ind;

val (join_strings_def, join_strings_ind) =
  tprove_no_defn ((join_strings_def, join_strings_ind),
  wf_rel_tac `measure (\(_,x).LENGTH x)` >>
  srw_tac [ARITH_ss] []);
val _ = register "join_strings" join_strings_def join_strings_ind;

val (pat_to_stree_def, pat_to_stree_ind) =
  tprove_no_defn ((pat_to_stree_def, pat_to_stree_ind),
  wf_rel_tac `measure (\(_,x). pat_size x)` >>
  rw [] >|
  [decide_tac,
   induct_on `v8` >>
       rw [] >>
       fs [pat_size_def] >>
       decide_tac]);
val _ = register "pat_to_stree" pat_to_stree_def pat_to_stree_ind;

val (exp_to_stree_def, exp_to_stree_ind) =
  tprove_no_defn ((exp_to_stree_def, exp_to_stree_ind),
  wf_rel_tac `measure (\x. case x of INL (_,_,e) => exp_size e
                                   | INR (INL (_,_,p,e)) => exp_size e + 1
                                   | INR (INR (_,_,v1,v2,e)) => exp_size e + 1)` >>
  rw [] >>
  TRY (induct_on `funs`) >>
  TRY (induct_on `pes`) >>
  TRY (induct_on `es`) >>
  TRY (induct_on `v51`) >>
  rw [exp_size_def] >>
  fs [exp_size_def] >>
  rw [exp_size_def] >>
  decide_tac);
val _ = register "exp_to_stree" exp_to_stree_def exp_to_stree_ind;

val (type_to_stree_def, type_to_stree_ind) =
  tprove_no_defn ((type_to_stree_def, type_to_stree_ind),
  wf_rel_tac `measure t_size` >>
  srw_tac [ARITH_ss] [] >>
  cases_on `ts` >>
  fs [] >>
  induct_on `t` >>
  rw [] >>
  fs [t_size_def] >>
  decide_tac);
val _ = register "type_to_stree" type_to_stree_def type_to_stree_ind;

val _ = export_theory ();
