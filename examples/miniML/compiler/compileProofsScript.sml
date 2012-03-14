open preamble MiniMLTheory CompileTheory evaluateEquationsTheory

val _ = new_theory "compileProofs"

val (remove_ctors_def,remove_ctors_ind) =
  tprove_no_defn ((remove_ctors_def,remove_ctors_ind),
  WF_REL_TAC
  `inv_image $< (\x. case x of INL (x,y) => exp_size y
                         | INR (INL (x,y)) => v_size y
                         | INR (INR (INL (x,y))) => exp3_size y
                         | INR (INR (INR (INL (x,y)))) => exp1_size y
                         | INR (INR (INR (INR (x,y)))) => exp6_size y)` >>
  rw [] >>
  TRY decide_tac >|
  [induct_on `es` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `vs` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac,
   induct_on `es` >>
       rw [exp_size_def] >>
       res_tac >>
       decide_tac]);
val _ = save_thm ("remove_ctors_def", remove_ctors_def);
val _ = save_thm ("remove_ctors_ind", remove_ctors_ind);

(*
This is too awful! Try a simpler definition of fold_consts.
val (fold_consts_def,fold_consts_ind) =
  tprove_no_defn ((fold_consts_def,fold_consts_ind),
  WF_REL_TAC
  `inv_image $< (λx. case x of
                     | INL x => exp_size x
                     | INR (INL x) => v_size x
                     | INR (INR (INL x)) => exp3_size x
                     | INR (INR (INR (INL x))) => exp1_size x
                     | INR (INR (INR (INR (INL x)))) => 1 + exp6_size x
                     | INR (INR (INR (INR (INR (_,x))))) => exp6_size x)` >>
  fs [Once fold_consts_UNION_AUX_def]
*)

(* ------------------------------------------------------------------------- *)

(* TODO: Where should this go? *)

val map_result_def = Define`
  (map_result f (Rval v) = Rval (f v)) ∧
  (map_result f (Rerr e) = Rerr e)`;
val _ = export_rewrites["map_result_def"];

(* ------------------------------------------------------------------------- *)

(* Prove compiler phases preserve semantics *)

(*
val remove_ctors_thm = store_thm(
"remove_ctors_thm",
``∀cnmap envc env exp r.
  (∀x y. (v_remove_ctors cnmap x = v_remove_ctors cnmap y) ⇒ (x = y)) ⇒
  (evaluate envc env (remove_ctors cnmap exp) (map_result (v_remove_ctors cnmap) r) =
   evaluate envc env exp r)``,
rw [] >>
qid_spec_tac `exp` >>
Induct >- (
  rw [evaluate_raise,remove_ctors_def] >>
  Cases_on `r` >> rw [] )
>- (
  rw [evaluate_val,remove_ctors_def] >>
  Cases_on `r` >> rw [] >> metis_tac [])
>- (
  Cases >- (
    rw [evaluate_con,remove_ctors_def,do_con_check_def] >>
    Cases_on `r` >> rw []
*)

val _ = export_theory ()
