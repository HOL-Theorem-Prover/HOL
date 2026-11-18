(* The unified HolyHammer problem generator.  The IR keeps the original HOL
   terms until generate_problem first-orderizes them into
   hhTptpProblem.tptp_term values. *)
signature hhProblemGen =
sig

  type term = Term.term
  type thm = Thm.thm

  (* Every intermediate fact has the caller's nickname and a HOL formula.
     Lambda definitions introduced by pass_lambda are ordinary facts named
     lam.<n>. *)
  type named_terms = {conjecture : term, facts : (string * term) list}

  (* This deliberately has the shape of hhTptpProblem.tptp_formula, except
     that atoms still contain HOL terms. *)
  datatype hol_formula =
      HQuant of bool * term list * hol_formula
    | HConn of hhTptpProblem.conn * hol_formula list
    | HAtom of term
  type formula_ir = {conjecture : hol_formula,
                     facts : (string * hol_formula) list}
  type proxy_ir = {conjecture : hol_formula,
                   facts : (string * hol_formula) list,
                   proxies : string list}

  (* Beta-eta contraction, unfolding LET when the flag is set. *)
  val beta_eta_contract : bool -> term -> term

  (* Pass 1.  Beta-eta contract every formula and unfold LET exactly when
     the target syntax lacks $let.  COND remains for the helper/$ite pass. *)
  val presimp : hhTptpProblem.format -> named_terms -> named_terms

  (* Pass 2.  Runs lambda translation jointly over the conjecture and facts;
     keep_lams is downgraded to lifting outside THF. *)
  val pass_lambda :
    hhTptpProblem.format -> hhLamTrans.mode -> named_terms -> named_terms

  (* Pass 3.  Only mono encodings invoke hhMonomorph; polymorphic native and
     legacy encodings preserve the ranked premise list unchanged. *)
  val pass_monomorph : hhTypeEnc.type_enc ->
    {max_iters : int, max_new_instances : int} -> named_terms -> named_terms

  (* The same on premises alone, against a reusable ground pool; polymorphic
     encodings leave the pool untouched. *)
  val pass_monomorph_pool : hhTypeEnc.type_enc ->
    {max_iters : int, max_new_instances : int} ->
    hhMonomorph.pool -> (string * Term.term) list ->
    (string * Term.term) list

  (* Pass 4 turns the outer HOL logical skeleton into formula constructors.
     Boolean equality is represented by Iff. *)
  val formula_skeleton : named_terms -> formula_ir

  (* Pass 5 changes logical constants in term position to proxies or native
     builtins, according to the target's HO/FOOL/syntax capabilities. *)
  val introduce_proxies : hhTptpProblem.format -> formula_ir -> proxy_ir

  type problem_options =
    {format : hhTptpProblem.format, type_enc : hhTypeEnc.type_enc,
     lam_trans : hhLamTrans.mode, mono_iters : int, mono_instances : int}

  (* The compositional front end consumed by the remaining generator passes. *)
  val translate_front : problem_options -> named_terms -> proxy_ir

  (* Passes 6--8: first-orderize, run the ?? monotonicity oracle, and apply
     the selected type encoding.  This is pure so pass-level selftests can
     inspect the TPTP AST before it is written to a file. *)
  val generate_problem :
    problem_options -> named_terms -> hhTptpProblem.problem

  (* A memo is local to one scheduler export pass.  It deliberately has no
     process-global backing: lambda translation is goal-dependent. *)
  type export_memo
  val new_export_memo : unit -> export_memo
  val memo_lambda_runs : export_memo -> int

  (* An abstraction survived first-order lambda handling; the labels are
     the context prefixes ("fact NAME", "conjecture"), innermost first.
     The tail of a prepared problem raises this instead of the Fail text,
     which needs the term grammar and so is produced by describe_failure
     on the calling thread: describe_failure maps it to the Fail
     exception of the same text the caller-side first-orderization
     raises, and every other exception to itself. *)
  exception Lambda_survived of string list * term
  val describe_failure : exn -> exn

  (* export_pb_in writes format_pb of force_tail of prepare_pb.  prepare_pb
     runs on the caller: it draws the fresh names and reads the memo,
     theorem data and caches (its own failures are final).  It returns the
     tail of make_problem: the final first-orderization and the build of
     the AST, which draw no names and use no shared state but read the live
     signature and type database.  A tail may run on another thread, only
     where no context is pinned (see hhSchedule), and fails with the raw
     exception (Lambda_survived, not its text); force_tail runs a tail on
     the calling thread and applies describe_failure.  format_pb touches no
     HOL state. *)
  type tail = unit -> hhTptpProblem.problem
  val prepare_pb : export_memo -> problem_options
    -> term * (string * thm) list -> tail
  val force_tail : tail -> hhTptpProblem.problem
  val format_pb : problem_options -> hhTptpProblem.problem -> string

  val export_pb_in : export_memo -> problem_options -> string
    -> term * (string * thm) list
    -> unit

  val export_pb : problem_options -> string
    -> term * (string * thm) list
    -> unit

end
