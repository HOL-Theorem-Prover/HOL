Theory refutePersistentType
Ancestors
  refute
Libs
  quotient

Theorem api_stream_exists[local]:
  ?f : num -> 'a. (\f. T) f
Proof
  qexists_tac `\n. ARB` >> simp []
QED

val api_stream_tydef =
  new_type_definition ("api_stream", api_stream_exists);

val api_stream_absrep = define_new_type_bijections
  {name = "api_stream_absrep", ABS = "api_stream_abs",
   REP = "api_stream_rep", tyax = api_stream_tydef};

Theorem api_stream_repabs[local]:
  !r. api_stream_rep (api_stream_abs r) = r
Proof
  simp [GSYM api_stream_absrep]
QED

Theorem api_stream_rep_11[local]:
  !x y. (api_stream_rep x = api_stream_rep y) <=> (x = y)
Proof
  metis_tac [CONJUNCT1 api_stream_absrep]
QED

Definition api_scons_def:
  api_scons (a : 'a) (s : 'a api_stream) : 'a api_stream =
    api_stream_abs (\n. if n = 0 then a else api_stream_rep s (n - 1))
End

Definition api_shd_def:
  api_shd (s : 'a api_stream) : 'a = api_stream_rep s 0
End

Definition api_stl_def:
  api_stl (s : 'a api_stream) : 'a api_stream =
    api_stream_abs (\n. api_stream_rep s (n + 1))
End

Definition api_stream_CASE_def:
  api_stream_CASE (s : 'a api_stream)
                  (f : 'a -> 'a api_stream -> 'b) : 'b =
    f (api_shd s) (api_stl s)
End

(* The stream eta law: every stream is its own head/tail reassembly. *)
Theorem api_stream_eta:
  !s. s = api_scons (api_shd s) (api_stl s)
Proof
  simp [GSYM api_stream_rep_11, api_scons_def, api_shd_def,
        api_stl_def, api_stream_repabs, FUN_EQ_THM] >>
  rw []
QED

(* The registration witness: the constant stream of [a] is cyclic under
   [api_scons], which is exactly what justifies dropping acyclicity. *)
Theorem api_stream_witness:
  ?s. s = api_scons a s
Proof
  qexists_tac `api_stream_abs (\n. a)` >>
  simp [GSYM api_stream_rep_11, api_scons_def, api_stream_repabs]
QED


Theorem api_pair_exists[local]:
  ?r : 'a # 'b. (\r. T) r
Proof
  qexists_tac `ARB` >> simp []
QED

val api_pair_tydef = new_type_definition ("api_pair", api_pair_exists);
val api_pair_bij = define_new_type_bijections
  {name = "api_pair_bij", ABS = "api_pair_abs", REP = "api_pair_rep",
   tyax = api_pair_tydef};

Theorem api_small_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val api_small_tydef = new_type_definition ("api_small", api_small_exists);
val api_small_bij = define_new_type_bijections
  {name = "api_small_bij", ABS = "api_small_abs", REP = "api_small_rep",
   tyax = api_small_tydef};

val api_batch_tydef = new_type_definition ("api_batch", api_small_exists);
val api_batch_bij = define_new_type_bijections
  {name = "api_batch_bij", ABS = "api_batch_abs", REP = "api_batch_rep",
   tyax = api_batch_tydef};
val _ = Theory.delete_binding "api_batch_bij";

Definition api_rel_def:
  api_rel (x : bool) y = (x = y)
End

Theorem api_equiv:
  !x y. api_rel x y = (api_rel x = api_rel y)
Proof
  simp [api_rel_def, FUN_EQ_THM, EQ_IMP_THM] >> metis_tac []
QED

val api_quot_def = define_quotient_type "api_quot"
  "api_quot_abs" "api_quot_rep" api_equiv;

(* Custom codata without a typedef or database discovery path. *)
val _ = new_type ("api_local", 0);
val _ = new_constant ("api_local_cons", ``:api_local -> api_local``);
val _ = new_constant ("api_local_case",
  ``:api_local -> (api_local -> 'a) -> 'a``);

val _ = new_constant ("api_small_cons", ``:api_small -> api_small``);
val _ = new_constant ("api_small_case",
  ``:api_small -> (api_small -> 'a) -> 'a``);

val _ = new_type ("api_missing", 0);
val _ = new_constant ("api_missing_cons", ``:api_missing -> api_missing``);
val _ = new_constant ("api_missing_case",
  ``:api_missing -> (api_missing -> 'a) -> 'a``);

Theorem api_partial_thm = api_quot_def

val _ = new_constant ("api_local_other", ``:api_local -> api_local``);
val _ = new_constant ("api_local_other_case",
  ``:api_local -> (api_local -> 'a) -> 'a``);
