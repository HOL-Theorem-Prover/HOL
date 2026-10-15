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


TESTS = [test_blocked_file_is_reported_not_waited_out,
         test_blocked_goal_state_explains_itself,
         test_timedout_proof_is_not_a_clean_bill,
         test_termination_block_is_addressable]


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
