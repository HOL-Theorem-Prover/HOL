(* The HolyHammer problem generator: a goal and its premises to a TPTP
   problem in a slice's format, type encoding and lambda translation.  The
   IR keeps HOL terms until first-orderization turns them into
   hhTptpProblem.tptp_term values. *)
signature hhProblemGen =
sig

  type term = Term.term
  type thm = Thm.thm

  (* Every intermediate fact has the caller's nickname and a HOL formula.
     Lambda definitions introduced by pass_lambda are ordinary facts named
     lam.<n> (and lam.<n>.combs). *)
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

  (* Beta-eta contraction; with the flag set, it also unfolds each LET
     whose unfolding copies nothing: its argument is a variable or a
     constant, or its variable occurs at most once. *)
  val beta_eta_contract : bool -> term -> term

  (* Pass 1.  beta_eta_contract true on every formula, whatever the
     format.  COND remains for the helper/$ite pass. *)
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

  (* Passes 1--5 composed, to inspect the IR.  generate_problem runs the
     same passes, but monomorphizes before the lambda pass under combs
     with a monomorphic encoding. *)
  val translate_front : problem_options -> named_terms -> proxy_ir

  (* The whole pipeline: passes 1--5, the helper facts, then passes 6--8
     (first-orderize, run the ?? monotonicity oracle, apply the type
     encoding).  It returns the TPTP AST and writes no file. *)
  val generate_problem :
    problem_options -> named_terms -> hhTptpProblem.problem

  (* A memo is local to one scheduler export pass.  It deliberately has no
     process-global backing: lambda translation is goal-dependent.
     memo_lambda_runs counts the lambda translations it has run. *)
  type export_memo
  val new_export_memo : unit -> export_memo
  val memo_lambda_runs : export_memo -> int

  (* An abstraction survived first-order lambda handling; the labels are
     the context prefixes ("fact NAME", "conjecture"), innermost first.
     A tail (below) raises it instead of a Fail, whose text needs the term
     grammar.  describe_failure, run on the calling thread, maps it to the
     Fail that the caller-side first-orderization raises, and every other
     exception to itself. *)
  exception Lambda_survived of string list * term
  val describe_failure : exn -> exn

  (* export_pb_in writes format_pb of force_tail of prepare_pb.  prepare_pb
     runs on the caller: it draws the fresh names and reads the memo and
     theorem data (its failures carry their text).  It returns the tail: the
     final first-orderization and the build of the AST, which draw no
     names and use no shared state but read the live signature and type
     database.  A tail may run on another thread, only where no context is
     pinned (see hhSchedule), and fails with the raw exception
     (Lambda_survived, not its text); force_tail runs a tail on the calling
     thread and applies describe_failure.  format_pb touches no HOL state.
     export_pb is export_pb_in with a fresh memo. *)
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
