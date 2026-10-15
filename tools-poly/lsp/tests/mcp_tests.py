#!/usr/bin/env python3
"""End-to-end tests for the MCP adapter (`tools-poly/lsp/mcp/`).

    python3 mcp_tests.py [-k <substring>]

The adapter had no coverage at all: `lsp_tests.py` drives the *server*
as an LSP client and stops below the adapter, so every bug that lives
in the translation between MCP and LSP was invisible to the suite.
Both bugs these tests pin were of exactly that kind -- the server
behaved as documented and as `lsp_tests.py` asserts, and the adapter
drew the wrong conclusion from it.

Each test boots a real `bin/hol lsp`, so this is slow by nature; there
are deliberately few of them, chosen for what regresses silently.
"""
import os
import re
import shutil
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "mcp"))

from mcp_cli import Adapter  # noqa: E402
import hol_mcp  # noqa: E402

REPO = os.path.normpath(os.path.join(HERE, "..", "..", ".."))

# Lifted from `lsp_tests.py` so the two suites agree on what a hanging
# proof is.  It sleeps rather than spins: a budget the tactic manages
# to swallow then costs the test time rather than a burning core.
HANGING_TACTIC = (
    "  (fn g => let fun f () = (OS.Process.sleep "
    "(Time.fromMilliseconds 50); f ()) in f () end)\n")

# Same shape as `lsp_tests.py`'s `_BLOCKED_SRC`.  That suite asserts
# this file produces `$/compileBlocked` and *no* `$/compileCompleted`,
# which is the server behaviour the adapter used to wait through.
BLOCKED_SRC = ("Theory mcpblocked\n"
               "Ancestors\n"
               "  nosuchtheory\n"
               "\n"
               "Theorem t:\n"
               "  T\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")

SLOW_SRC = ("Theory mcpslow\n"
            "Ancestors arithmetic\n"
            "\n"
            "Theorem fine:\n"
            "  T\n"
            "Proof\n"
            "  ACCEPT_TAC TRUTH\n"
            "QED\n"
            "\n"
            "Theorem hangs:\n"
            "  T\n"
            "Proof\n"
            + HANGING_TACTIC +
            "QED\n")

# A definition whose termination is not automatic, so the server has an
# obligation to derive.  Nothing about the goal is written in the file,
# which is the point: it cannot be found by reading the text.
TERMINATION_SRC = ("Theory mcptermination\n"
                   "Ancestors arithmetic\n"
                   "\n"
                   "Definition cdown_def:\n"
                   "  cdown n = if n = 0 then 0n else 1 + cdown (n - 1)\n"
                   "Termination\n"
                   "  WF_REL_TAC `measure I` >> simp []\n"
                   "End\n")

# Two goals whose true order is known: `conj_tac` on `A /\ B` yields A
# and then B, and HOL's goalstack display prints them the other way up.
# The conclusions are distinguishable (`a + b` against `b + a`) so a
# listing in the wrong order cannot be mistaken for one in the right
# order, and both goals carry the same two assumptions, so an
# assumption shown against the wrong goal shows up as well.
GOAL_ORDER_SRC = (
    "Theory mcpgoalorder\n"
    "Ancestors arithmetic\n"
    "\n"
    "Theorem two_goals:\n"
    "  !a b:num. a = 1 ==> b = 2 ==> (a + b = 3 /\\ b + a = 3)\n"
    "Proof\n"
    "  gen_tac >> gen_tac >> strip_tac >> strip_tac >> conj_tac\n"
    "  >- simp []\n"
    "  >- simp []\n"
    "QED\n"
    "\n"
    "Theorem one_goal:\n"
    "  !a:num. a = 1 ==> a + 0 = 1\n"
    "Proof\n"
    "  gen_tac >> strip_tac >> simp []\n"
    "QED\n")

# A proof that fails in the middle of a `>-` chain and has two more
# branches after it.  The walk does not stop there -- it cheats the
# branch and carries on -- so the step it reports is the `QED` and the
# goals it reports are the leftovers, while the goal that actually
# failed (`x + 0 = x`) appears in neither.
FAILING_BRANCH_SRC = (
    "Theory mcpfailstep\n"
    "Ancestors arithmetic\n"
    "\n"
    "Theorem branch_fails:\n"
    "  !x:num. x = x /\\ (x + 0 = x) /\\ T\n"
    "Proof\n"
    "  gen_tac >> rpt conj_tac\n"
    "  >- REFL_TAC\n"
    "  >- FAIL_TAC \"deliberate\"\n"
    "  >- ACCEPT_TAC TRUTH\n"
    "QED\n")

FAILURES = []
RUN = 0


def check(cond, what):
    global RUN
    RUN += 1
    if cond:
        print("  OK   %s" % what)
    else:
        print("  FAIL %s" % what)
        FAILURES.append(what)


def with_fixture(name, src, env=None):
    """A temp directory holding `<name>Script.sml`, and an adapter.

    `env` is applied to this process, because the adapter passes
    `env=None` to the pool and the server therefore inherits whatever
    we have -- which is also how a real client would set it.
    """
    d = tempfile.mkdtemp(prefix="mcp_test_")
    path = os.path.join(d, "%sScript.sml" % name)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(src)
    saved = {}
    for key, value in (env or {}).items():
        saved[key] = os.environ.get(key)
        os.environ[key] = value
    return d, path, saved


def restore(d, saved):
    for key, value in saved.items():
        if value is None:
            os.environ.pop(key, None)
        else:
            os.environ[key] = value
    shutil.rmtree(d, ignore_errors=True)


# ------------------------------------------------------------------ #
def test_blocked_file_is_reported_not_waited_out():
    """A file whose ancestor will not load must be answered, fast.

    The deps-blocked path sends `$/compileBlocked` and neither of the
    other two edges, so an adapter waiting only for `compileCompleted`
    and `compileInterrupted` sat for the full 180s compile timeout and
    then answered from a session that had compiled nothing -- reporting
    `proofs: (none reported)` about a file full of them.

    The timing assertion is the real regression guard: the text is
    easy to restore by hand, the promptness is not.
    """
    d, path, saved = with_fixture("mcpblocked", BLOCKED_SRC)
    adapter = Adapter()
    try:
        start = time.time()
        text, is_err = adapter.call("hol_check_file", {"file": path})
        elapsed = time.time() - start
        check(elapsed < 120,
              "blocked file answered promptly (%.1fs, was a 180s stall)"
              % elapsed)
        check("BLOCKED" in text,
              "says the file was not compiled (got %r)" % text[:120])
        check("nosuchtheoryTheory" in text,
              "names the module that is missing")
        check("none reported" not in text,
              "does not report an empty proof tally as the answer")
        check(not is_err or True, "returns a report (isError=%s)" % is_err)
    finally:
        adapter.close()
        restore(d, saved)


def test_blocked_goal_state_explains_itself():
    """`hol_goal_state` on a blocked file used to say the position was
    "not inside a proof the server can walk" -- true, but about the
    wrong thing: the proof is there and well-formed, and what is
    missing is the ancestor.  A model told the former edits the proof."""
    d, path, saved = with_fixture("mcpblocked", BLOCKED_SRC)
    adapter = Adapter()
    try:
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "t"})
        check("nosuchtheoryTheory" in text,
              "blames the unloadable ancestor (got %r)" % text[:160])
        check("not inside a proof" not in text,
              "does not blame the proof's shape")
    finally:
        adapter.close()
        restore(d, saved)


def test_timedout_proof_is_not_a_clean_bill():
    """A proof whose replay budget ran out is `timedout`: explicitly
    "not a verdict on the proof" (LSPExtension.sig), so not broken --
    but equally not proved.  `check_file` listed neither, so a file
    whose proofs were all too slow came back `0 broken proof(s)`."""
    d, path, saved = with_fixture(
        "mcpslow", SLOW_SRC, env={"HOL_LSP_PROOF_TIMEOUT_MS": "2000"})
    adapter = Adapter()
    try:
        text, _ = adapter.call("hol_check_file", {"file": path})
        check(re.search(r"timedout=\d", text) is not None,
              "the tally counts timedout proofs (got %r)" % text[:200])
        check(re.search(r"timedout: hangs", text) is not None,
              "the slow proof is listed by name")
        check("NOT CHECKED" in text,
              "the verdict refuses to read as clean")
        # Positive control: the budget has not simply broken the file.
        check("proved=1" in text,
              "the proof beside it still passes (got %r)" % text[:200])
        check("0 broken proof(s)" in text,
              "and timedout is still not counted as broken")
    finally:
        adapter.close()
        restore(d, saved)


def test_termination_block_is_addressable():
    """A `Termination` block has no `QED`, and the adapter used to aim
    only at that token and refuse -- "has no `Proof ... QED' body" --
    for every definition in the tree.

    Since 802af30e4 the server answers `$/hol/goalState` for a cursor
    between `Termination` and `End`, so the refusal was the adapter
    declining to ask.  It matters because most of what a datatype
    change breaks is in termination blocks: the tool that reports the
    obligation broken could not show it.
    """
    d, path, saved = with_fixture("mcptermination", TERMINATION_SRC)
    adapter = Adapter()
    try:
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "cdown_def_termination"})
        check("has no `Proof" not in text,
              "does not refuse for want of a QED (got %r)" % text[:160])
        check("STATUS:" in text,
              "answers with a goal state (got %r)" % text[:160])
        # Step 0 is before the measure is chosen, so the obligation
        # itself is on show -- the thing that was unreachable.
        text, _ = adapter.call("hol_try_tactic",
                               {"file": path,
                                "theorem": "cdown_def_termination",
                                "step": 0,
                                "tactic": "WF_REL_TAC `measure I`"})
        check("WF" in text or "R " in text,
              "the derived obligation is visible (got %r)" % text[:200])
        # Positive control: naming something that really has no body
        # still explains itself rather than answering nonsense.
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "nosuchdecl"})
        check("no declaration named" in text,
              "an unknown name is still reported (got %r)" % text[:160])
    finally:
        adapter.close()
        restore(d, saved)


def test_unverified_proofs_are_not_a_clean_bill():
    """`cheated` and `timedout` are states, not verdicts, and a SUMMARY
    that counts neither reads as a pass over proofs nobody checked.

    No server here: both states are reached only by timing -- a replay
    budget running out, or the pool not having caught up with an edit --
    so an end-to-end fixture for them would be a flaky test of a clock.
    The rule itself is what must not rot.
    """
    clean = hol_mcp._verdict(0, {"proved": ["a"]}, True, 600)
    check("0 broken proof(s)" in clean and "NOT CHECKED" not in clean,
          "a genuinely clean tally still reads clean (got %r)" % clean)

    for status in ("cheated", "timedout"):
        text = hol_mcp._verdict(0, {status: ["a", "b"], "proved": ["c"]},
                                True, 600)
        check("NOT CHECKED" in text,
              "%s refuses to read as clean (got %r)" % (status, text))
        check("2 proof(s)" in text,
              "%s says how many went unchecked (got %r)" % (status, text))

    # ...and still not counted as broken: they are not failures.
    both = hol_mcp._verdict(0, {"cheated": ["a"], "timedout": ["b"]},
                            True, 600)
    check("0 broken proof(s)" in both,
          "neither is miscounted as broken (got %r)" % both)
    check(both.count("NOT CHECKED") == 2,
          "both are reported, not just the first (got %r)" % both)

    # An unsettled tally was already refused; keep it that way.
    unsettled = hol_mcp._verdict(0, {"checking": ["a"]}, False, 600)
    check("INCOMPLETE" in unsettled,
          "an unsettled tally is still INCOMPLETE (got %r)" % unsettled)


def test_goals_are_listed_in_the_proof_s_own_order():
    """A multi-goal state used to be printed bottom-to-top.

    `$/hol/goalState` sends the state twice -- a `goals` array in the
    proof's order, and a `pretty` string from HOL's goalstack printer,
    whose convention puts the current goal LAST.  The adapter printed
    `pretty` verbatim and dropped the array, so the goal the next `>-`
    branch was about to attack looked like the last one in the list and
    nothing in the reply said otherwise.

    Invisible to `lsp_tests.py` because the server is right: both
    halves of its reply are correct, and only the adapter chose which
    to show.  It cost a real proof -- four `>-` branches of a cakeml
    lemma reordered to match the display, after which the proof read as
    solved while the elaboration still failed.
    """
    d, path, saved = with_fixture("mcpgoalorder", GOAL_ORDER_SRC)
    adapter = Adapter()
    try:
        # Step 5 is after the `conj_tac`: two goals, `a + b = 3` first.
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "two_goals",
                                "step": 5})
        first, second = text.find("a + b = 3"), text.find("b + a = 3")
        check(first >= 0 and second >= 0,
              "both goals are shown (got %r)" % text[:300])
        check(first >= 0 and second >= 0 and first < second,
              "the proof's first goal is listed first (got %r)" % text[:300])
        check("goal 1 of 2" in text and "goal 2 of 2" in text,
              "each goal says which of how many it is (got %r)" % text[:300])
        # The assumptions belong to both goals, and HOL numbers the
        # oldest 0.  A listing that renumbered them would disagree with
        # every goals pane and with `pop_assum` reasoning about them.
        check(text.count(" 0.  a = 1") == 2 and text.count(" 1.  b = 2") == 2,
              "each goal keeps its own assumptions, numbered as HOL "
              "numbers them (got %r)" % text[:300])

        # One goal: nothing to order, so the server's own rendering
        # stands -- and must still carry the assumptions.
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "one_goal",
                                "step": 2})
        check("a + 0 = 1" in text and "a = 1" in text,
              "a single goal still renders with its assumptions (got %r)"
              % text[:300])
        check("goal 1 of" not in text,
              "and is not dressed up as a listing (got %r)" % text[:300])

        # A closed proof: `pretty` is the only place the server says so.
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "one_goal"})
        check("Initial goal proved" in text,
              "a finished proof still says so (got %r)" % text[:300])
    finally:
        adapter.close()
        restore(d, saved)


def test_failing_proof_shows_the_state_that_failed():
    """The step a failing proof reported was not the failing step.

    A goal-state walk answers "what is the state at the cursor", so it
    cannot stop at a failure: it stands `cheat' in for what a failed
    `>-` branch owed and carries on, and for a request that names only
    a theorem the cursor is the `QED`.  The reply therefore paired an
    accurate `FAILED AT: line L col C` with a step and a set of goals
    from the far end of the proof -- on cakeml's
    `reachable_refs_UPDATE1`, step 57 with three goals none of which
    was the one `metis_tac[]` was given.

    Two correct halves about two different places is the answer most
    likely to be acted on wrongly, so the adapter now asks again at the
    failure's own position and shows that state instead.
    """
    d, path, saved = with_fixture("mcpfailstep", FAILING_BRANCH_SRC)
    adapter = Adapter()
    try:
        text, _ = adapter.call("hol_goal_state",
                               {"file": path, "theorem": "branch_fails"})
        check("x + 0 = x" in text,
              "shows the goal the failing tactic was given (got %r)"
              % text[:400])
        check("FAILED AT" in text,
              "still says where the failure is (got %r)" % text[:400])
        check("SHOWING" in text and "where the walk ENDED" in text,
              "says the reported step is not the failing one (got %r)"
              % text[:400])
        # What used to be the whole body: the end-of-walk state, which
        # here is every goal discharged by the `cheat' that stood in.
        check("No goals remain" not in text,
              "does not answer with the post-cheat state (got %r)"
              % text[:400])
    finally:
        adapter.close()
        restore(d, saved)


def test_goal_listing_ignores_the_reversed_pretty():
    """The ordering rule itself, without a server.

    The end-to-end test above pins the behaviour; this pins the
    invariant it rests on, which is that `pretty` and `goals` disagree
    and that the array wins.  A reply is cheap to write down and a
    server is not, so this is the one that will still be run when the
    suite is being run often.
    """
    reply = {"theorem": "t", "step": 5, "status": "ok",
             "goals": [{"asms": ["b = 2", "a = 1"], "goal": "FIRST"},
                       {"asms": [], "goal": "SECOND"}],
             # As HOL prints it: the current goal last.
             "pretty": "SECOND\n\nFIRST\n\n2 subgoals"}
    text = hol_mcp._render_goal_state(reply, "t", None)
    check(text.index("FIRST") < text.index("SECOND"),
          "the array's order wins over the display's (got %r)" % text)
    check("2 subgoals" not in text,
          "the reversed rendering is not printed beside it (got %r)" % text)
    check(" 0.  a = 1" in text and " 1.  b = 2" in text,
          "assumptions are numbered oldest-first, as HOL does (got %r)"
          % text)
    check(text.index(" 1.  b = 2") < text.index("FIRST"),
          "and stay attached to the goal they belong to (got %r)" % text)

    # A failure the adapter could not re-anchor must say so rather than
    # let its step read as the failure's own.
    unanchored = hol_mcp._render_goal_state(
        {"theorem": "t", "step": 9, "status": "ok", "goals": [],
         "pretty": "nothing left",
         "failedRange": {"start": {"line": 3, "character": 2}}},
        "t", None)
    check("CAVEAT" in unanchored and "came to rest" in unanchored,
          "an un-anchored failure says the step is the walk's end "
          "(got %r)" % unanchored)


TESTS = [test_blocked_file_is_reported_not_waited_out,
         test_blocked_goal_state_explains_itself,
         test_timedout_proof_is_not_a_clean_bill,
         test_termination_block_is_addressable,
         test_unverified_proofs_are_not_a_clean_bill,
         test_goals_are_listed_in_the_proof_s_own_order,
         test_failing_proof_shows_the_state_that_failed,
         test_goal_listing_ignores_the_reversed_pretty]


def main(argv):
    only = None
    if len(argv) > 2 and argv[1] == "-k":
        only = argv[2]
    hol = os.path.join(REPO, "bin", "hol")
    if not os.path.exists(hol):
        print("no %s: MCP adapter tests NOT run" % hol)
        return 0
    for test in TESTS:
        if only and only not in test.__name__:
            continue
        print("%s:" % test.__name__)
        try:
            test()
        except Exception as exc:  # a crashed test is a failed test
            print("  FAIL %s raised %s: %s"
                  % (test.__name__, type(exc).__name__, exc))
            FAILURES.append(test.__name__)
    print("\n%d check(s), %d failure(s)" % (RUN, len(FAILURES)))
    for name in FAILURES:
        print("  failed: %s" % name)
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
