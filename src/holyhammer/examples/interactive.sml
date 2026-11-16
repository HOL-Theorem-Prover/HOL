(* ========================================================================= *)
(* FILE          : interactive.sml                                           *)
(* DESCRIPTION   : HolyHammer examples: an annotated interactive session     *)
(*                                                                           *)
(* This is not a theory script.  Paste the commands into an interactive      *)
(* HOL4 session one at a time (or run "hol < interactive.sml" to see them    *)
(* all).  The comments show abridged output from a real session on a        *)
(* 16-core machine with E 3.2.5, Vampire 5.0.1 and Zipperposition 2.1.       *)
(* Your timings, slice lists and even lemma choices will differ.             *)
(* ========================================================================= *)

load "holyHammer"; open holyHammer;

(* -------------------------------------------------------------------------
   1. Which provers can HolyHammer see?

   hhProver.all () lists the supported provers; hhProver.probe looks for
   the binary and asks it for its version.
   ------------------------------------------------------------------------- *)

fun show_prover (c : hhProver.prover_config) =
  case hhProver.probe c of
      NONE => print (#name c ^ ": not installed\n")
    | SOME {path, version, tested} =>
        print (#name c ^ ": " ^ path ^ " (" ^
               (case version of SOME v => v | NONE => "unknown version") ^
               (if tested then ", tested" else ", untested") ^ ")\n");
List.app show_prover (hhProver.all ());

(*  e: /home/user/.local/bin/eprover (3.2.5-ho, tested)
    vampire: /home/user/.local/bin/vampire (5.0.1, tested)
    zipperposition: /home/user/.local/bin/zipperposition (2.1, tested)
    z3: /home/user/.opam/default/bin/z3_tptp (4.11.2.0, tested)

    "tested" means the version is one HolyHammer's output parsers were
    tested against.  z3 is supported but not in the default prover list. *)

(* -------------------------------------------------------------------------
   2. The current settings
   ------------------------------------------------------------------------- *)

hhConfig.print_params ();

(*  timeout = 30 (default) -- overall wall-clock budget in seconds
    max_proofs = 4 (default) -- maximum number of reconstructed proofs
    provers = e vampire zipperposition (default) -- provers eligible ...
    ...
    minimize = true (default) -- minimize reconstructed proofs
    preplay_timeout = 1.0 (default) -- proof reconstruction timeout ...
    ...
    cache = false (default) -- enable the result cache
    ...
    debug_dir =  (default) -- directory for retained prover output     *)

(* -------------------------------------------------------------------------
   3. A first call
   ------------------------------------------------------------------------- *)

val th1 = holyhammer ``MEM x l /\ EVERY P l ==> P x``;

(*    starting vampire slice (96 facts)
      starting e slice (128 facts)
      starting zipperposition slice (128 facts)
      starting vampire slice (512 facts)
      ...                                    (one line per core)
      vampire slice: Theorem (0.252441 s)
      proof found by vampire:
        metis_tac [listTheory.EVERY_MEM]
      verified proof (replays in 0.00 s):
        metis_tac [listTheory.EVERY_MEM]
      zipperposition slice: Timeout (0.17836 s)
      e slice: Timeout (0.286808 s)
      ...                                    (the other slices stopping)

    Prove the statement in a script with:
      metis_tac [listTheory.EVERY_MEM]
    val th1 = ⊢ MEM x l ∧ EVERY P l ⇒ P x: thm

   The last message is the one to act on: it comes after every slice
   has reported.                                                        *)

(* -------------------------------------------------------------------------
   4. Inside a goalstack proof
   ------------------------------------------------------------------------- *)

g `!l1 l2. ALL_DISTINCT (l1 ++ l2) ==> DISJOINT (set l1) (set l2)`;
e (rpt strip_tac);
e hh;

(*      verified proof (replays in 0.00 s):
          metis_tac [listTheory.ALL_DISTINCT_APPEND']
      ...

    Replace `hh` with:
      metis_tac [listTheory.ALL_DISTINCT_APPEND']
    Goal proved.
     [.] ⊢ DISJOINT (set l1) (set l2)                                     *)

(* -------------------------------------------------------------------------
   5. Options: time limit and provers

   hh_get returns the current value as a string; hh_unset restores the
   default.
   ------------------------------------------------------------------------- *)

hhConfig.hh_set ("timeout", "10");
hhConfig.hh_get "timeout";                 (* val it = "10": string *)

hhConfig.hh_set ("provers", "vampire");
val th2 =
  holyhammer ``REVERSE (l1 ++ [x] ++ l2) = REVERSE l2 ++ x :: REVERSE l1``;

(*      starting vampire slice (96 facts)
        starting vampire slice (512 facts)
        ...                                  (only Vampire slices now)
        proof found by vampire:
          metis_tac [listTheory.REVERSE_REVERSE, listTheory.REVERSE_DEF,
                     listTheory.REVERSE_APPEND, listTheory.APPEND]
        verified proof (replays in 0.00 s):
          metis_tac [listTheory.REVERSE_DEF, listTheory.REVERSE_APPEND,
                     listTheory.APPEND]

    Minimisation removed REVERSE_REVERSE, which Vampire used but Metis
    does not need. *)

hhConfig.hh_unset "provers";

(* Bad values are rejected immediately, with the list of valid ones: *)

hhConfig.hh_set ("filter", "magic")
  handle e => print (General.exnMessage e ^ "\n");

(*  HOL_ERR (at hhConfig.hh_set: invalid value 'magic' for HolyHammer
    option 'filter'; expected empty, knn, mepo, mash, mesh, or none; ...) *)

(* -------------------------------------------------------------------------
   6. Premise selection: filters and the number of facts

   Every slice has its own premise selector and fact count.  Setting
   "filter" or "max_facts" overrides them for all slices.
   ------------------------------------------------------------------------- *)

hhConfig.hh_set ("filter", "mepo");
val th3 = holyhammer ``LENGTH (FILTER P l) <= LENGTH l``;
(*      verified proof (replays in 0.00 s):
          metis_tac [rich_listTheory.LENGTH_FILTER_LEQ]                   *)
hhConfig.hh_unset "filter";

hhConfig.hh_set ("max_facts", "16");
val th4 = holyhammer ``LENGTH (FILTER P l) <= LENGTH l``;
(*      starting e slice (16 facts)
        starting zipperposition slice (16 facts)
        ...
        verified proof (replays in 0.00 s):
          metis_tac [th3]

    Note the proof: th3, the theorem bound by the previous command, is
    a premise like any other.  The hammer sees theorems bound at the top
    level of the session, so be careful what you bind: see the FAQ in
    README.md about theorems with assumptions.                           *)
hhConfig.hh_unset "max_facts";

(* -------------------------------------------------------------------------
   7. Choosing the premises yourself: hh_pb

   hh_pb dir provers premises goal runs the given provers with exactly
   the given premises (fully qualified names).  It is the HOL4 analogue
   of Sledgehammer's "sledgehammer (facts)".  The first argument is the
   directory below which the problem files are written; they are deleted
   when the call returns.
   ------------------------------------------------------------------------- *)

val pb_goal =
  ([] : term list,
   ``SURJ f s t <=> IMAGE f s = t /\ (!x. x IN s ==> f x IN t)``);
val th6 = TAC_PROOF (pb_goal,
  hh_pb (hhConfig.state_dir ()) ["e", "vampire"]
    ["pred_setTheory.IMAGE_SURJ", "pred_setTheory.IN_IMAGE"] pb_goal)
  handle HOL_ERR _ => TRUTH;

(*      vampire slice: Theorem (0.751689 s)
        proof found by vampire:
          metis_tac [pred_setTheory.IMAGE_SURJ, pred_setTheory.IN_IMAGE]
      ...
      ATPs found proofs, but reconstruction failed for:
      vampire: [pred_setTheory.IMAGE_SURJ, pred_setTheory.IN_IMAGE]
      e: [pred_setTheory.IMAGE_SURJ, pred_setTheory.IN_IMAGE]
      ...

    The two premises are enough, and both provers prove the goal from
    them, but Metis cannot replay the proof within preplay_timeout.  This
    is the second kind of failure; hh10_troubleshootingScript.sml shows
    how to finish such a proof by hand. *)

(* -------------------------------------------------------------------------
   8. Keeping the minimisation off

   With minimize = false the verified proof keeps every fact the prover
   used, in the form the prover reported it.
   ------------------------------------------------------------------------- *)

hhConfig.hh_set ("minimize", "false");
val th7 = holyhammer ``LENGTH (REVERSE l ++ l) = 2 * LENGTH l``;
(*      verified proof (replays in 0.01 s):
          metisTools.METIS_TAC [arithmeticTheory.NUMERAL_DEF ,
            arithmeticTheory.ALT_ZERO , arithmeticTheory.ADD_SYM ,
            arithmeticTheory.TIMES2 , listTheory.LENGTH_REVERSE ,
            listTheory.LENGTH_APPEND]

    With the default (minimize = true) the same call prints
          metis_tac [arithmeticTheory.TIMES2, listTheory.LENGTH_REVERSE,
                     listTheory.LENGTH_APPEND]                            *)
hhConfig.hh_unset "minimize";

(* -------------------------------------------------------------------------
   9. Looking at the problems: debug_dir

   Normally the TPTP problems are deleted when the call returns.  With
   debug_dir set, they are kept in the given directory, together with
   the raw output of every prover run.  Theories loaded at any point
   are visible to later calls; here transcTheory brings in the real
   numbers.
   ------------------------------------------------------------------------- *)

load "transcTheory";
hhConfig.hh_set ("debug_dir", "/tmp/hh-debug");
val th8 = holyhammer ``x < y ==> (x + y) / 2r < y``;
(*      verified proof (replays in 0.01 s):
          metis_tac [realTheory.REAL_HALF_DOUBLE, realTheory.REAL_LT_ADD2,
                     realaxTheory.REAL_LT_RADD,
                     realaxTheory.REAL_LT_TOTAL]

    /tmp/hh-debug now contains one file per prover run (e-2.out,
    vampire-7.out, ...) with the prover's own output.  The matching
    problems are in directories such as
      /tmp/hh-debug/problems/<call>/
        vampire.knn.tx0.mono__native__fool.lifting.96
    (prover, premise selector, encoding, number of facts), each with
    the problem in atp_in.

    Note the seven-lemma proof of a goal that realLib.REAL_ARITH_TAC
    proves at once: see tip 6 in README.md.  On another run the same
    call failed with "reconstruction failed"; linear arithmetic is not
    the hammer's job. *)
hhConfig.hh_unset "debug_dir";

(* -------------------------------------------------------------------------
   10. A false goal
   ------------------------------------------------------------------------- *)

val th9 = holyhammer ``LENGTH (l1 ++ l2) = LENGTH l1``
  handle HOL_ERR e => (print (Feedback.format_ERR e); TRUTH);
(*      ATPs could not find a proof
    Exception raised at holyHammer.main_hh: ATPs could not find a proof

    The hammer cannot tell a false goal from a hard one.  Before trying
    harder, test the goal on an example:                                   *)

EVAL ``LENGTH ([] ++ [1]) = LENGTH ([] : num list)``;
(*  val it = ⊢ LENGTH ([] ⧺ [1]) = LENGTH [] ⇔ F: thm                      *)

(* -------------------------------------------------------------------------
   11. Reusing lemmas you proved earlier in the session
   ------------------------------------------------------------------------- *)

val th12 =
  holyhammer ``EVERY P l /\ EVERY Q l /\ MEM x l ==> P x /\ Q x``;
(*      verified proof (replays in 0.01 s):
          metis_tac [th1]

    th1 (section 3) is exactly the lemma needed.  In a script, give such
    lemmas names with Theorem so that later hammer calls can find them. *)

hhConfig.hh_unset "timeout";
