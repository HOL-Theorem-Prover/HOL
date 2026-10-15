Theory refutePersist
Ancestors
  arithmetic
Libs
  Refute quotient

val _ = new_type ("persist_codata", 1);
val _ = new_constant ("persist_cons",
  ``:'a -> 'a persist_codata -> 'a persist_codata``);
val _ = new_constant ("persist_case",
  ``:'a persist_codata -> ('a -> 'a persist_codata -> 'b) -> 'b``);
val _ = Refute.export_codatatype
  {tyop = {Thy = "refutePersist", Tyop = "persist_codata"},
   case_const = ``persist_case``, constructors = [``persist_cons``],
   witness = NONE};

val _ = new_type ("persist_local", 1);
val _ = new_constant ("persist_local_cons",
  ``:'a -> 'a persist_local -> 'a persist_local``);
val _ = new_constant ("persist_local_case",
  ``:'a persist_local -> ('a -> 'a persist_local -> 'b) -> 'b``);
val _ = Refute.register_codatatype
  {tyop = {Thy = "refutePersist", Tyop = "persist_local"},
   case_const = ``persist_local_case``,
   constructors = [``persist_local_cons``], witness = NONE};

Theorem persist_exists[local]:
  ?n : num. (\n. n < 2) n
Proof
  qexists_tac `0` >> simp []
QED

val persist_tydef = new_type_definition ("persist_sub", persist_exists);
val persist_bij = define_new_type_bijections
  {name = "persist_bij", ABS = "persist_abs", REP = "persist_rep",
   tyax = persist_tydef};
(* Delete the DB binding and embed a derived anonymous proof. *)
val _ = Theory.delete_binding "persist_bij";
val _ = Refute.export_typedef
  {ty = ``:persist_sub``, abs = ``persist_abs``, rep = ``persist_rep``,
   absrep_thms = [CONJ (CONJUNCT1 persist_bij) (CONJUNCT2 persist_bij)]};

val persist_control_tydef =
  new_type_definition ("persist_control", persist_exists);
val persist_control_bij = define_new_type_bijections
  {name = "persist_control_bij", ABS = "persist_control_abs",
   REP = "persist_control_rep", tyax = persist_control_tydef};
val _ = Theory.delete_binding "persist_control_bij";

Definition persist_rel_def:
  persist_rel (x : bool) y = (x = y)
End

Theorem persist_equiv:
  !x y. persist_rel x y = (persist_rel x = persist_rel y)
Proof
  simp [persist_rel_def, FUN_EQ_THM, EQ_IMP_THM] >> metis_tac []
QED

val persist_partial = quotient.define_quotient_type "persist_partial"
  "persist_partial_abs" "persist_partial_rep" persist_equiv;
val _ = Refute.export_quotient
  {qty = ``:persist_partial``, rty = ``:bool``,
   abs = ``persist_partial_abs``, rep = ``persist_partial_rep``,
   equiv_thm = persist_partial};

val persist_total = quotient.define_quotient_type "persist_total"
  "persist_total_abs" "persist_total_rep" persist_equiv;
val _ = Refute.export_quotient
  {qty = ``:persist_total``, rty = ``:bool``, abs = ``persist_total_abs``,
   rep = ``persist_total_rep``, equiv_thm = persist_equiv};

val persist_harvested_tydef =
  new_type_definition ("persist_harvested", persist_exists);
val persist_harvested_bij = define_new_type_bijections
  {name = "persist_harvested_bij", ABS = "persist_harvested_abs",
   REP = "persist_harvested_rep", tyax = persist_harvested_tydef};
val _ = Refute.harvest_registrations ();
val second_harvest = Refute.harvest_registrations ();
val _ = if null (#typedefs second_harvest) andalso
           null (#quotients second_harvest) then ()
        else raise Fail "a second harvest reported old registrations";
val _ = Theory.delete_binding "persist_harvested_bij";
val _ = Refute.export_registrations [``:persist_harvested``];

val persist_discovered_tydef =
  new_type_definition ("persist_discovered", persist_exists);
val persist_discovered_bij = define_new_type_bijections
  {name = "persist_discovered_bij", ABS = "persist_discovered_abs",
   REP = "persist_discovered_rep", tyax = persist_discovered_tydef};
val _ = Refute.export_registrations [``:persist_discovered``];
val _ = Theory.delete_binding "persist_discovered_bij";

Theorem persist_domain_exists[local]:
  ?b : bool. (\b. b) b
Proof
  qexists_tac `T` >> simp []
QED

val persist_domain_tydef =
  new_type_definition ("persist_domain", persist_domain_exists);
val persist_domain_bij = define_new_type_bijections
  {name = "persist_domain_bij", ABS = "persist_domain_abs",
   REP = "persist_domain_rep", tyax = persist_domain_tydef};
Theorem persist_domain_rep_true[local]:
  !a. persist_domain_rep a
Proof
  gen_tac >>
  mp_tac (SPEC ``persist_domain_rep a`` (CONJUNCT2 persist_domain_bij)) >>
  simp [CONJUNCT1 persist_domain_bij]
QED

Theorem persist_domain_quotient[local]:
  QUOTIENT (\x y : bool. x /\ y) persist_domain_abs persist_domain_rep
Proof
  simp [quotientTheory.QUOTIENT_def, CONJUNCT1 persist_domain_bij,
        persist_domain_rep_true] >>
  qx_gen_tac `r` >> qx_gen_tac `s` >>
  Cases_on `r` >> Cases_on `s` >> simp []
QED

val _ = Refute.export_quotient
  {qty = ``:persist_domain``, rty = ``:bool``, abs = ``persist_domain_abs``,
   rep = ``persist_domain_rep``, equiv_thm = persist_domain_quotient};
val _ = Theory.delete_binding "persist_domain_bij";

Theorem persist_stream_exists[local]:
  ?f : num -> 'a. (\f. T) f
Proof
  qexists_tac `\n. ARB` >> simp []
QED

val persist_stream_tydef =
  new_type_definition ("persist_stream", persist_stream_exists);

val persist_stream_absrep = define_new_type_bijections
  {name = "persist_stream_absrep", ABS = "persist_stream_abs",
   REP = "persist_stream_rep", tyax = persist_stream_tydef};

Theorem persist_stream_repabs[local]:
  !r. persist_stream_rep (persist_stream_abs r) = r
Proof
  simp [GSYM persist_stream_absrep]
QED

Theorem persist_stream_rep_11[local]:
  !x y. (persist_stream_rep x = persist_stream_rep y) <=> (x = y)
Proof
  metis_tac [CONJUNCT1 persist_stream_absrep]
QED

Definition persist_scons_def:
  persist_scons (a : 'a) (s : 'a persist_stream) : 'a persist_stream =
    persist_stream_abs (\n. if n = 0 then a else persist_stream_rep s (n - 1))
End

Definition persist_shd_def:
  persist_shd (s : 'a persist_stream) : 'a = persist_stream_rep s 0
End

Definition persist_stl_def:
  persist_stl (s : 'a persist_stream) : 'a persist_stream =
    persist_stream_abs (\n. persist_stream_rep s (n + 1))
End

Definition persist_stream_CASE_def:
  persist_stream_CASE (s : 'a persist_stream)
                  (f : 'a -> 'a persist_stream -> 'b) : 'b =
    f (persist_shd s) (persist_stl s)
End

(* The registration witness: the constant stream of [a] is cyclic under
   [persist_scons], which is exactly what justifies dropping acyclicity. *)
Theorem persist_stream_witness:
  ?s. s = persist_scons a s
Proof
  qexists_tac `persist_stream_abs (\n. a)` >>
  simp [GSYM persist_stream_rep_11, persist_scons_def, persist_stream_repabs]
QED

val _ = Refute.export_codatatype
  {tyop = {Thy = "refutePersist", Tyop = "persist_stream"},
   case_const = ``persist_stream_CASE``, constructors = [``persist_scons``],
   witness = SOME persist_stream_witness};

val persist_halves_tydef =
  new_type_definition ("persist_halves", persist_exists);
val persist_halves_bij = define_new_type_bijections
  {name = "persist_halves_bij", ABS = "persist_halves_abs",
   REP = "persist_halves_rep", tyax = persist_halves_tydef};
val _ = Theory.delete_binding "persist_halves_bij";
val _ = Refute.export_typedef
  {ty = ``:persist_halves``, abs = ``persist_halves_abs``,
   rep = ``persist_halves_rep``, absrep_thms =
     [CONJUNCT1 persist_halves_bij, CONJUNCT2 persist_halves_bij]};

Theorem persist_generic_exists[local]:
  ?r : 'a # bool. (\r. T) r
Proof
  qexists_tac `ARB` >> simp []
QED
val persist_generic_tydef =
  new_type_definition ("persist_generic", persist_generic_exists);
val persist_generic_bij = define_new_type_bijections
  {name = "persist_generic_bij", ABS = "persist_generic_abs",
   REP = "persist_generic_rep", tyax = persist_generic_tydef};
val _ = Theory.delete_binding "persist_generic_bij";
val _ = Refute.export_typedef
  {ty = ``:'a persist_generic``, abs = ``persist_generic_abs``,
   rep = ``persist_generic_rep``, absrep_thms = [persist_generic_bij]};
