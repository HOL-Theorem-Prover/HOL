#!/usr/bin/env python3
"""An MCP server over HOL4's LSP server.

    hol_mcp.py [--hol <path to bin/hol>]

Speaks MCP (JSON-RPC 2.0, newline-delimited, over stdio) to a model,
and LSP to one `bin/hol lsp` per script.  The LSP half lives in
`lsp_session.py`; this file knows no LSP.

Why an adapter rather than a second front-end inside the SML: the
protocol-neutral seam in the server (`LSPExtension.sig`) sits *below*
the compile driver, so re-entering there would mean duplicating the
document model, the incremental-resume logic, the global-state locking
and the diagnostics publishing -- the hard parts.  Encoding JSON twice
is much the cheaper of the two.

Four things this layer owns, because the server cannot:

  * Addressing.  Every server hook takes a URI and a position, because
    it was built for a human with a cursor.  A model has a *name*.
    `textDocument/documentSymbol` is the authoritative declaration
    index, so name -> position is a lookup here and needs no server
    change.

  * Waiting.  Compiles are debounced and asynchronous and the proof
    tally arrives as a transition stream with no full-state message.
    A tool call is synchronous, so each one opens the document, waits
    for the pass, and accumulates the stream.

  * Budget.  A goal with ninety assumptions will not fit in a reply
    worth sending, and the thing that gets cut must never be the
    diagnosis.  `_budget` keeps head and tail; every caller puts its
    diagnosis in the footer, which is appended after the cut.

  * Convention.  The server's other clients are editor panes, where
    the proof is on screen beside the answer and the reader can see
    what it is about.  Two of its conventions rely on that and mislead
    without it: goals are listed in HOL's goalstack order, current one
    LAST, and a goal-state walk reports where it came to rest rather
    than where the proof failed -- it cheats past a failed `>-` branch
    by design, because a cursor asks what the state *here* is.  A
    model has no pane, so `_render_goal_state` numbers the goals from
    the structured array instead, and `_state_at_failure` asks again
    at the failure's own position.  Nothing changes in the server:
    both conventions are right for the clients they were built for.
"""
import argparse
import json
import os
import re
import sys
import threading
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from lsp_session import (  # noqa: E402
    LspError, SessionDead, SessionPool, path_to_uri)

# The version of MCP this server implements.  A client asking for a
# different one is answered with this, per spec -- it then decides
# whether it can live with it.
PROTOCOL_VERSION = "2025-06-18"
SERVER_NAME = "hol4"
SERVER_VERSION = "0.1.0"

# Characters, not tokens: close enough, and exact is not the point.
DEFAULT_BUDGET = 8000


def log(msg):
    """stdout is the protocol channel.  Everything human goes here."""
    sys.stderr.write("[hol-mcp] %s\n" % msg)
    sys.stderr.flush()


# The server renders through a pretty-printer whose default backend
# emits VT100 colour, because its other two clients are editors with a
# terminal to put it in.  A model has none: the escapes survive as
# literal noise, cost tokens, and break any attempt to match on the
# text.  Stripping is the adapter's job -- the same decision as width
# and tally accumulation.
_ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")


def plain(text):
    return _ANSI.sub("", text or "")


# ---------------------------------------------------------------- #
# Output budgeting
# ---------------------------------------------------------------- #
def _budget(text, limit=DEFAULT_BUDGET, footer=""):
    """Fit `text` into `limit`, keeping head and tail, then append
    `footer` whole.

    The footer is appended *after* the cut and is not itself counted,
    which is the whole point: the attribution for a failure is the
    shortest and most valuable thing in the reply, and a truncation
    that eats it does so in exactly the case that needed it.
    """
    if len(text) > limit:
        head = limit * 2 // 3
        tail = limit - head
        cut = len(text) - head - tail
        text = ("%s\n\n... [%d characters elided] ...\n\n%s"
                % (text[:head], cut, text[-tail:]))
    return text + footer if footer else text


# ---------------------------------------------------------------- #
# Positions
# ---------------------------------------------------------------- #
# The session negotiates positionEncoding utf-8, so a `character` is a
# byte offset within its line, not a codepoint index.  Every HOL script
# using the term quotes is full of multibyte characters, so counting
# str indices here would mis-place a position by the width of every
# quote before it on the line -- silently, and only in files that use
# the notation, which is all of them.
def _offset_of(text, pos):
    """LSP (line, character) -> byte offset into `text`."""
    raw = text.encode("utf-8")
    off = 0
    for _ in range(pos.get("line", 0)):
        nxt = raw.find(b"\n", off)
        if nxt < 0:
            return len(raw)
        off = nxt + 1
    return min(off + pos.get("character", 0), len(raw))


def _position_at(text, offset):
    """Byte offset -> LSP (line, character)."""
    head = text.encode("utf-8")[:offset]
    return {"line": head.count(b"\n"),
            "character": offset - (head.rfind(b"\n") + 1)}



def _verdict(num_diags, by_status, settled, proof_timeout):
    """The SUMMARY line for a tally.

    Pulled out of `check_file` because the two statuses that must not
    read as clean are reached only by timing -- a replay budget running
    out, or a pool that has not caught up -- and a rule that cannot be
    exercised is a rule that rots.

    `broken` is `failed` and `diverged` only.  The other two are not
    verdicts on a proof, but they are not clean bills either, and the
    one answer this adapter must never give is a confident "nothing is
    broken" about proofs nobody checked.
    """
    broken = sum(len(by_status.get(s, [])) for s in ("failed", "diverged"))
    if not settled:
        # Never claim a clean file from an unsettled tally: that is a
        # confident "nothing is broken" about a file nobody has
        # finished checking.
        still = len(by_status.get("checking", []))
        return ("\n\nSUMMARY: INCOMPLETE -- %d proof(s) still being "
                "checked after %ss. %d diagnostic(s) and %d broken "
                "proof(s) SO FAR; call again for the rest."
                % (still, proof_timeout, num_diags, broken))
    verdict = ("\n\nSUMMARY: %d diagnostic(s), %d broken proof(s)."
               % (num_diags, broken))
    # "Not a verdict on the proof: a report that we stopped asking"
    # (LSPExtension.sig).
    unchecked = len(by_status.get("timedout", []))
    if unchecked:
        verdict += (" %d proof(s) NOT CHECKED -- the replay budget ran out "
                    "before they finished, so this is not a clean bill of "
                    "health; raise the budget (HOL_LSP_PROOF_TIMEOUT_MS) to "
                    "settle them." % unchecked)
    # `cheated` is the same kind of non-verdict.  Per the state model in
    # server.ML a proof the compile has reached but the pool has not
    # replayed "is taken on trust", and an edit re-announces the proofs
    # it invalidates as `cheated` before they are enqueued again.  So a
    # tally sampled in that window has nothing `checking', settles at
    # once, and carries the verdicts from *before* the edit -- which is
    # how a deleted theorem came back `cheated'.
    untried = len(by_status.get("cheated", []))
    if untried:
        verdict += (" %d proof(s) NOT CHECKED -- taken on trust and never "
                    "replayed, so this is not a clean bill of health. Right "
                    "after an edit this is the pool still catching up and "
                    "the other verdicts may predate the edit too; call "
                    "hol_restart and ask again." % untried)
    return verdict


def _last_token(text, token, start, stop):
    """Byte offset of the last `token` in [start, stop), on word
    boundaries, or None.

    A plain substring search would match the `QED` inside a string
    literal or an identifier such as `myQED`; requiring non-identifier
    characters either side is the whole of what this needs to get
    right, and it is bounded by a range the server's own parser gave
    us rather than being a parser of its own.
    """
    raw = text.encode("utf-8")
    needle = token.encode("ascii")

    def wordish(byte):
        return byte in b"_'" or chr(byte).isalnum()

    at = raw.rfind(needle, start, stop)
    while at >= 0:
        before_ok = at == 0 or not wordish(raw[at - 1])
        after = at + len(needle)
        after_ok = after >= len(raw) or not wordish(raw[after])
        if before_ok and after_ok:
            return at
        at = raw.rfind(needle, start, at)
    return None


# ---------------------------------------------------------------- #
# HOL-side operations
# ---------------------------------------------------------------- #
class Hol:
    """The tool implementations.  Each returns a plain string."""

    def __init__(self, pool, repo):
        self.pool = pool
        self.repo = repo

    # -- plumbing --------------------------------------------------
    def _resolve(self, file):
        path = file if os.path.isabs(file) else os.path.join(self.repo, file)
        path = os.path.abspath(path)
        if not os.path.exists(path):
            raise ValueError("no such file: %s" % path)
        return path

    def _ready(self, file, timeout=180):
        """Session with `file` open, compiled, and current with disk.

        Re-reads the file every call rather than trusting a cache: the
        model edits scripts with its own tools between calls, and a
        stale buffer answers questions about a file nobody has.

        The fourth element is the `$/compileBlocked` params, or None.
        A blocked file compiled *nothing*, so every tool that reads a
        compile result has to say so rather than answer from an empty
        session -- which is how a missing ancestor used to come back as
        "no proofs" or "not inside a proof the server can walk".
        """
        path = self._resolve(file)
        with open(path, "r", encoding="utf-8") as handle:
            text = handle.read()
        session = self.pool.get(path)
        mark = session.open_or_sync(path, text)
        blocked = None
        if mark is not None:
            session.await_compile(path, mark, timeout)
            blocked = session.deps_blocked(path, since=mark)
        else:
            blocked = session.deps_blocked(path)
        return session, path, text, blocked

    def _blocked_report(self, path, blocked, session=None):
        """What to say when the server would not compile the file.

        Names the modules, because the action is to build them, and
        appends any `window/showMessage` -- that is where a heap the
        server could not load gets explained, and without it a session
        silently answering from `bin/hol.state` looks like a bad file.
        """
        mods = blocked.get("modules") or []
        lines = ["file: %s" % os.path.relpath(path, self.repo),
                 "BLOCKED: the server did not compile this file.",
                 "reason: %s" % plain(blocked.get("message", "")).strip()]
        if mods:
            lines.append("unavailable module(s): %s" % ", ".join(mods))
        notes = session.show_messages() if session is not None else []
        for note in notes:
            lines.append("server note: %s" % plain(note).strip())
        lines.append("")
        lines.append("Nothing was elaborated, so there is no proof tally "
                     "and no goal state for any theorem here. Build the "
                     "module(s) above with Holmake, then call hol_restart "
                     "on this file -- a running server is pinned to the "
                     "artifacts it loaded at startup.")
        return "\n".join(lines)

    def _diagnostics(self, session, path):
        uri = path_to_uri(path)
        latest = None
        for msg in session.notifications("textDocument/publishDiagnostics"):
            params = msg.get("params") or {}
            if params.get("uri") == uri:
                latest = params
        return (latest or {}).get("diagnostics", [])

    def _position_of(self, session, path, text, theorem, occurrence=1):
        """Name -> a position the walker will accept.

        Two steps, and the second is the one that matters.

        `textDocument/documentSymbol` gives the authoritative range of
        each declaration, so finding `theorem` is a lookup.  But the
        walker wants a cursor *inside* the `Proof ... QED` body:
        `findEnclosingTheorem` tests `proof_ <= cursor <= qed_`, and a
        declaration's start is before `proof_`, so the symbol's own
        position never walks.  (Nor does the offset `$/proofStates`
        reports, which is the same declaration start.)

        So aim at the `QED` that closes the body.  It satisfies the
        upper bound exactly, and because the cursor is also what
        decides how *far* the walk goes, it means the default -- no
        `step` given -- is the end of the proof, which is the state a
        reader wants when they name a theorem and nothing else.  With
        `step` given, any position in the body would do and this one
        still does.

        A `Definition ... Termination ... End` has no `QED`, and its
        obligation is not written in the file at all.  The server
        derives it, and answers `$/hol/goalState` for a cursor between
        `Termination` and `End`; the block's `End` closes that range
        the way `QED` closes a proof body, so it is the same rule
        applied to the other bracket.  This matters more than it
        looks: most of what a datatype change breaks is in termination
        blocks, so refusing them refused the goals most worth seeing.

        Occurrence matters: proof identity in this server is name plus
        occurrence precisely because a script may declare the same
        name twice, and positions move under edits.
        """
        symbols = session.request("textDocument/documentSymbol", {
            "textDocument": {"uri": path_to_uri(path)}})
        hits = [s for s in (symbols or []) if s.get("name") == theorem]
        if not hits:
            names = sorted({s.get("name", "") for s in (symbols or [])})
            raise ValueError(
                "no declaration named %r in %s. Declared here: %s"
                % (theorem, os.path.basename(path),
                   ", ".join(names[:40]) or "(none)"))
        if occurrence < 1 or occurrence > len(hits):
            raise ValueError(
                "%r has %d occurrence(s) in %s; asked for #%d"
                % (theorem, len(hits), os.path.basename(path), occurrence))
        rng = hits[occurrence - 1]["location"]["range"]
        start = _offset_of(text, rng["start"])
        stop = _offset_of(text, rng["end"])
        closer = _last_token(text, "QED", start, stop)
        if closer is None:
            closer = _last_token(text, "End", start, stop)
        if closer is None:
            raise ValueError(
                "%r in %s has neither a `Proof ... QED' body nor a "
                "`Termination ... End' block, so there is no goal "
                "state to walk." % (theorem, os.path.basename(path)))
        return _position_at(text, closer)

    # -- tools -----------------------------------------------------
    def check_file(self, file, timeout=180, proof_timeout=600):
        session, path, _, blocked = self._ready(file, timeout)
        if blocked is not None:
            return self._blocked_report(path, blocked, session)
        diags = self._diagnostics(session, path)
        proofs, settled = session.await_proofs(path, proof_timeout)

        by_status = {}
        for state in proofs.values():
            by_status.setdefault(state.get("status", "?"), []).append(
                state.get("name"))

        lines = ["file: %s" % os.path.relpath(path, self.repo)]
        # Every status the server can send (`sendProofStates`,
        # server.ML).  `timedout` used to be missing, which dropped it
        # from the tally, from the detail listing and from the verdict
        # -- so a file whose proofs were too slow to check came back as
        # "0 broken proof(s)", the one answer this adapter must never
        # give.  Keep this list exhaustive.
        order = ["failed", "diverged", "suspended", "timedout", "cheated",
                 "checking", "proved", "unseen"]
        if proofs:
            lines.append("proofs: " + ", ".join(
                "%s=%d" % (k, len(by_status[k]))
                for k in order if k in by_status))
        else:
            lines.append("proofs: (none reported)")

        for status in ("failed", "diverged", "suspended", "timedout",
                       "cheated"):
            for name in by_status.get(status, []):
                # Flattened: HOL's exception text is multi-line, and a
                # newline here breaks the one-per-proof listing into
                # something that reads as two separate proofs.
                detail = " ".join(
                    plain(proofs[name].get("detail", "")).split())
                tail = " -- " + detail if detail else ""
                lines.append("  %s: %s%s" % (status, name, tail))

        if diags:
            lines.append("")
            lines.append("diagnostics (%d):" % len(diags))
            for diag in diags:
                start = diag.get("range", {}).get("start", {})
                lines.append("  %s:%s  %s"
                             % (start.get("line", 0) + 1,
                                start.get("character", 0) + 1,
                                plain(diag.get("message", "")).strip()))
        else:
            lines.append("diagnostics: none")

        broken = sum(len(by_status.get(s, []))
                     for s in ("failed", "diverged"))
        # `timedout` is deliberately *not* broken: "Not a verdict on the
        # proof: a report that we stopped asking" (LSPExtension.sig).
        # But it is equally not clean, and a bare "0 broken proof(s)"
        # over a pile of unchecked proofs reads as a pass.  So it gets
        # its own clause in the verdict rather than a bucket.
        verdict = _verdict(len(diags), by_status, settled, proof_timeout)
        return _budget("\n".join(lines), footer=verdict)

    def goal_state(self, file, theorem, step=None, occurrence=1, width=100,
                   timeout=180):
        session, path, text, blocked = self._ready(file, timeout)
        if blocked is not None:
            return self._blocked_report(path, blocked, session)
        pos = self._position_of(session, path, text, theorem, occurrence)
        params = {"textDocument": {"uri": path_to_uri(path)},
                  "position": pos, "width": width}
        if step is not None:
            params["step"] = step
        result = session.request("$/hol/goalState", params)
        at_failure = None
        if step is None:
            at_failure = self._state_at_failure(session, path, result, width)
        return _render_goal_state(result, theorem, step, at_failure)

    def _state_at_failure(self, session, path, result, width):
        """Ask a second time, anchored where the first walk said the
        proof failed.

        The walk a goal-state request runs does not stop at a failure.
        It cannot: a cursor asks "what is the state *here*", and
        getting there means carrying on past the branches that are not
        finished yet, which is the ordinary condition of a proof being
        written.  So it stands `cheat' in for what a failed `>-` branch
        owed and walks on to the cursor -- which, for a request that
        names only a theorem, is the `QED`.

        The consequence is that the step it reports is the END of the
        walk and the goals it reports are the leftovers there, while
        the failure it reports in `failedRange` is somewhere else
        entirely.  On cakeml's `reachable_refs_UPDATE1` that was step
        57 with three goals, against a `metis_tac[]` at line 3848 whose
        real goal was none of the three.  Both halves of the answer
        were correct and they were about different places, which is the
        shape of answer most likely to be acted on wrongly.

        `failedRange` is in the proof body, so it is a cursor like any
        other: asking for it stops the walk just before the step that
        failed, and the state that comes back is the one that step was
        given.  One extra walk, and only when the first reported a
        failure.

        Returns None when there is nothing better to show, in which
        case the caller says what the reported step is and is not.
        """
        if not isinstance(result, dict):
            return None
        start = (result.get("failedRange") or {}).get("start")
        if not start:
            return None
        try:
            again = session.request("$/hol/goalState", {
                "textDocument": {"uri": path_to_uri(path)},
                "position": start, "width": width})
        except (LspError, SessionDead):
            # A diagnosis that cost an answer is a bad trade: the
            # first reply is still a true report of where the walk
            # ended, so fall back to it rather than fail the call.
            return None
        if not isinstance(again, dict):
            return None
        if again.get("status") == "pending":
            return None
        # Nothing to add: the first reply already showed this state.
        if again.get("step") == result.get("step"):
            return None
        if not (again.get("goals")
                or plain(again.get("pretty") or "").strip()):
            return None
        return again

    def try_tactic(self, file, theorem, tactic, step=None, occurrence=1,
                   width=100, budget_ms=0, timeout=180):
        session, path, text, blocked = self._ready(file, timeout)
        if blocked is not None:
            return self._blocked_report(path, blocked, session)
        pos = self._position_of(session, path, text, theorem, occurrence)
        params = {"textDocument": {"uri": path_to_uri(path)},
                  "position": pos, "width": width,
                  "tactic": tactic, "budgetMs": budget_ms}
        if step is not None:
            params["step"] = step
        result = session.request("$/hol/tryTactic", params)
        rendered = _render_goal_state(result, theorem, step)
        return ("candidate: %s\n(probe only -- the file is unchanged)\n\n%s"
                % (tactic, rendered))

    def search(self, file, query, limit=40, timeout=180):
        # A session, not a bare process: patterns are parsed with the
        # file's own grammar, so `f (g x)` means in the search what it
        # would mean in that script.
        session, _, _, blocked = self._ready(file, timeout)
        # Search still answers when the file is blocked -- the session
        # has base HOL loaded -- but only over what did load, so an
        # empty result is not evidence a theorem does not exist.  Say
        # which case this is rather than let absence read as proof.
        caveat = ""
        if blocked is not None:
            mods = ", ".join(blocked.get("modules") or []) or "its ancestors"
            caveat = ("\n\nNOTE: %s could not be loaded, so this searched "
                      "only the theories that did. A theorem defined in "
                      "those modules will not appear here."
                      % mods)
        results = session.request("$/hol/search",
                                  {"query": query, "limit": limit})
        if not results:
            return "no results for: %s%s" % (query, caveat)
        lines = []
        for item in results:
            where = item.get("theory") or ""
            lines.append("%s%s  [%s]"
                         % (where + "$" if where else "",
                            item.get("name", "?"), item.get("class", "")))
            statement = plain(item.get("statement") or "").strip()
            if statement:
                lines.append("    " + statement.replace("\n", "\n    "))
        footer = ("\n\nSUMMARY: %d result(s) for %r.%s"
                  % (len(results), query, caveat))
        return _budget("\n".join(lines), footer=footer)

    def sessions(self):
        rows = self.pool.describe()
        if not rows:
            return "no sessions running"
        return "\n".join(
            "%s  pid=%s  %s  up %ss"
            % (os.path.relpath(r["file"], self.repo), r["pid"],
               "alive" if r["alive"] else "DEAD", r["uptime_s"])
            for r in rows)

    def restart(self, file):
        path = self._resolve(file)
        self.pool.restart(path)
        return ("restarted the session for %s.\n"
                "A server is pinned to the artifacts it loaded at startup, so "
                "this is what picks up a dependency you have since rebuilt."
                % os.path.relpath(path, self.repo))


# The rule HOL draws between a goal's assumptions and its conclusion.
# Reproduced rather than referred to: each goal below is laid out the
# way a goals pane lays out a single goal, so the only thing new to a
# reader is the heading that says which goal it is.
_RULE = "-" * 36

# Said above a multi-goal listing, not in the footer: the footer is
# appended after `_budget`'s cut, but the head of the body survives it,
# and this has to be read *before* the goals it describes.
_ORDER_NOTE = (
    "%d goals, in the order the proof has them. Goal 1 is the one the "
    "next tactic -- and the next `>-` branch -- is applied to. (HOL's "
    "own goals display prints the current goal LAST; this listing does "
    "not, so the two read in opposite directions.)")


def _indent_lines(text, prefix, first=None):
    """`text` with `prefix` on every line, continuations included.

    A term rendered at the client's width breaks across lines, and a
    continuation left at column zero sits flush under the *next*
    goal's heading -- which is the same "which goal is this" ambiguity
    the numbering below exists to remove.
    """
    lines = plain(text).split("\n")
    out = [(prefix if first is None else first) + lines[0]]
    out.extend(prefix + line for line in lines[1:])
    return "\n".join(out)


def _render_goals(goals):
    """The structured goals, numbered, in the order the server sent.

    The server sends the same state twice: a `goals` array and a
    `pretty` rendering.  They do not agree on order.  `pretty` comes
    from HOL's goalstack printer, whose convention is that the
    *current* goal is printed last, under the others -- right for the
    editor panes the server's other clients put it in, where the proof
    is on screen beside it, and wrong here, where a model reading a
    transcript has nothing to anchor it.  Printing `pretty` verbatim
    therefore listed the goals bottom-to-top with nothing saying so,
    and the goal `>-` was about to attack looked like the last one.

    That is not a cosmetic complaint: on cakeml's
    `evaluate_handle_adj_vars_lemma` the four branches of a `>-` chain
    were reordered to match the display, and the reordered proof then
    reported as solved while the real elaboration still failed.

    So print the array, which is in the proof's own order, and number
    every goal against the total.  Numbered rather than merely
    reordered, because a reader given neither numbers nor a convention
    cannot tell a listing that was reordered from one that was not.

    Assumptions are numbered as HOL numbers them: 0 is the *oldest*,
    which is the last element of `asms`, `top_goals` handing them back
    newest-first.  Numbering them the other way up would make `0.`
    here and `0.` in a goals pane two different assumptions, which is
    the first defect again at one level down.
    """
    out = []
    total = len(goals)
    for i, goal in enumerate(goals, 1):
        out.append("goal %d of %d:" % (i, total))
        asms = list(goal.get("asms") or [])
        for n, asm in enumerate(reversed(asms)):
            out.append(_indent_lines(asm, "     ", " %d.  " % n))
        if asms:
            out.append(_RULE)
        out.append(_indent_lines(goal.get("goal", ""), "     "))
        out.append("")
    return "\n".join(out).rstrip("\n")


def _render_goal_state(result, theorem, step, at_failure=None):
    """One goal-state reply, with its diagnosis in the footer.

    `at_failure` is a *second* reply, anchored at the step this one
    blamed (see `Hol._state_at_failure`).  When there is one it is
    what the body shows: it is the state the failing tactic was
    actually given, and therefore the state the reader came for.
    """
    if result is None:
        return ("no goal state for %s%s -- the position is not inside a "
                "proof the server can walk." % (theorem, _step_suffix(step)))
    status = result.get("status", "?")
    if status == "pending":
        return ("the state for %s is not ready yet (a compile is still "
                "running). Retry." % theorem)

    shown = at_failure if at_failure is not None else result
    goals = shown.get("goals") or []
    pretty = plain(shown.get("pretty") or "").strip("\n")
    if len(goals) > 1:
        # Deliberately not `pretty`, which is reversed; see
        # `_render_goals`.  One goal and no goals are left to it: with
        # nothing to order there is no ambiguity to remove, and
        # `pretty` is where the server puts the sentences that are not
        # goals at all ("Initial goal proved.", and the warning that
        # the only reason none remain is `cheat').
        body = [_ORDER_NOTE % len(goals), "", _render_goals(goals)]
    elif pretty.strip():
        body = [pretty]
    elif goals:
        body = [_render_goals(goals)]
    else:
        body = []

    context = [plain(c) for c in (shown.get("context") or [])]
    note = plain(shown.get("note") or "") or None

    walk_step = result.get("step")
    name = result.get("theorem", theorem)
    if at_failure is None:
        footer_bits = ["\n\nSTATUS: %s at step %s of %s; %d goal(s)."
                       % (status, walk_step, name, len(goals))]
    else:
        fail_step = at_failure.get("step")
        footer_bits = [
            "\n\nSTATUS: %s at step %s of %s; %d goal(s) -- but that is "
            "where the walk ENDED, not where the proof failed."
            % (status, walk_step, name, len(result.get("goals") or [])),
            "SHOWING: the state at step %s instead (%d goal(s)), which is "
            "the step that failed. A `>-` branch that fails does not stop "
            "the walk: `cheat' stands in for what the branch owed and the "
            "walk carries on to the end, so the goals it ends with are "
            "downstream of the failure and are not the ones that went "
            "wrong. Ask again with step=%s for the end-of-walk state."
            % (fail_step, len(goals), walk_step)]
    if context:
        footer_bits.append("OPEN: " + "; ".join(context))
    if note:
        footer_bits.append("NOTE: " + note)
    if result.get("error"):
        footer_bits.append("ERROR: " + plain(result["error"]))
    rng = result.get("failedRange")
    if rng:
        start = rng.get("start", {})
        at_step = ("" if at_failure is None
                   else " (step %s)" % at_failure.get("step"))
        footer_bits.append("FAILED AT: line %s col %s%s"
                           % (start.get("line", 0) + 1,
                              start.get("character", 0) + 1, at_step))
        if at_failure is None:
            # The re-anchored walk is what normally answers this, so
            # reaching here means it was not run (the caller named a
            # step) or it declined.  Say the limit rather than leave
            # the step reading as the failure's own.
            footer_bits.append(
                "CAVEAT: the step above is where the walk came to rest, "
                "which need not be where the proof went wrong -- the "
                "walk cheats past a failed branch and carries on. The "
                "line and column are the failure; the goals may not be.")
    return _budget("\n".join(body), footer="\n".join(footer_bits))


def _step_suffix(step):
    return "" if step is None else " at step %s" % step


# ---------------------------------------------------------------- #
# Tool schemas
# ---------------------------------------------------------------- #
_FILE = {"type": "string",
         "description": "Script path, absolute or relative to the HOL tree."}


def tool_schemas():
    return [
        {
            "name": "hol_check_file",
            "description":
                "Compile a HOL script and report its diagnostics and the "
                "status of every proof in it (proved / failed / diverged / "
                "suspended / timedout / cheated). Call this first: it is "
                "what makes a file's state current, and every other tool "
                "here implies it.",
            "inputSchema": {
                "type": "object",
                "properties": {"file": _FILE},
                "required": ["file"],
            },
        },
        {
            "name": "hol_goal_state",
            "description":
                "The goal state inside a named theorem's proof. Omit `step` "
                "for the end of the proof, or give a 0-based step index to "
                "see the state before that tactic ran. Reports which "
                "combinators are still open, and where the proof failed if "
                "it did -- and when it did fail, shows the state at the "
                "failing step rather than at the end of the walk, which are "
                "not the same place. Goals are listed in the proof's own "
                "order: goal 1 is what the next `>-` branch acts on.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": _FILE,
                    "theorem": {"type": "string",
                                "description": "Name as declared."},
                    "step": {"type": "integer",
                             "description": "0-based tactic step index."},
                    "occurrence": {
                        "type": "integer",
                        "description":
                            "Which declaration of this name, 1-based. "
                            "Only needed when a script declares it twice."},
                    "width": {"type": "integer",
                              "description": "Render width, default 100."},
                },
                "required": ["file", "theorem"],
            },
        },
        {
            "name": "hol_try_tactic",
            "description":
                "Apply a candidate tactic at a point in a proof and report "
                "the state it reaches, WITHOUT editing the file. This is the "
                "way to test a tactic: it costs one walk, leaves nothing "
                "behind, and a failure here is not a fault in the script.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": _FILE,
                    "theorem": {"type": "string"},
                    "tactic": {"type": "string",
                               "description": "SML tactic text to apply."},
                    "step": {"type": "integer",
                             "description":
                                 "Apply at this 0-based step instead of at "
                                 "the end of the proof."},
                    "occurrence": {"type": "integer"},
                    "budget_ms": {
                        "type": "integer",
                        "description":
                            "Wall-clock the probe may spend. 0 uses the "
                            "server default. A candidate can loop."},
                    "width": {"type": "integer"},
                },
                "required": ["file", "theorem", "tactic"],
            },
        },
        {
            "name": "hol_search",
            "description":
                "Search HOL's theorem database. The query is a list of "
                "selectors, narrowing: \"NAME\" (double quotes) matches a "
                "theorem-name fragment, 'THY' (single quotes) restricts to "
                "a theory, and anything unquoted is a term pattern. Free "
                "variables in a pattern are wildcards and matching is up to "
                "instantiation, so `f (g x)` finds every nested "
                "application. Example: \"ASSOC\" 'arithmetic'",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": dict(
                        _FILE, description=(
                            "Script whose session to search from -- patterns "
                            "parse with that file's own grammar.")),
                    "query": {"type": "string"},
                    "limit": {"type": "integer",
                              "description": "Default 40."},
                },
                "required": ["file", "query"],
            },
        },
        {
            "name": "hol_sessions",
            "description":
                "List the running HOL servers. One process serves one "
                "script -- a theory, once loaded, can be neither re-read nor "
                "withdrawn -- so each file gets its own and costs a heap.",
            "inputSchema": {"type": "object", "properties": {}},
        },
        {
            "name": "hol_restart",
            "description":
                "Discard and respawn a file's server. A running server is "
                "pinned to the artifacts it loaded at startup, so rebuilding "
                "a dependency with Holmake does NOT reach it; this is what "
                "picks the rebuild up.",
            "inputSchema": {
                "type": "object",
                "properties": {"file": _FILE},
                "required": ["file"],
            },
        },
    ]


def dispatch(hol, name, args):
    if name == "hol_check_file":
        return hol.check_file(args["file"])
    if name == "hol_goal_state":
        return hol.goal_state(
            args["file"], args["theorem"], args.get("step"),
            args.get("occurrence", 1), args.get("width", 100))
    if name == "hol_try_tactic":
        return hol.try_tactic(
            args["file"], args["theorem"], args["tactic"], args.get("step"),
            args.get("occurrence", 1), args.get("width", 100),
            args.get("budget_ms", 0))
    if name == "hol_search":
        return hol.search(args["file"], args["query"], args.get("limit", 40))
    if name == "hol_sessions":
        return hol.sessions()
    if name == "hol_restart":
        return hol.restart(args["file"])
    raise ValueError("unknown tool: %s" % name)


# ---------------------------------------------------------------- #
# MCP transport
# ---------------------------------------------------------------- #
class McpServer:
    """JSON-RPC 2.0 over stdio, one message per line.

    Note this is *not* LSP's `Content-Length` framing -- MCP is
    newline-delimited, and the two halves of this adapter speak the
    two different framings on purpose.
    """

    def __init__(self, hol):
        self.hol = hol
        self.out_lock = threading.Lock()

    def write(self, msg):
        with self.out_lock:
            sys.stdout.write(json.dumps(msg) + "\n")
            sys.stdout.flush()

    def reply(self, rid, result):
        self.write({"jsonrpc": "2.0", "id": rid, "result": result})

    def fail(self, rid, code, message):
        self.write({"jsonrpc": "2.0", "id": rid,
                    "error": {"code": code, "message": message}})

    def serve(self):
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            try:
                msg = json.loads(line)
            except ValueError:
                self.fail(None, -32700, "parse error")
                continue
            try:
                self.handle(msg)
            except Exception as exc:  # never let one call kill the server
                log("handler crashed: %s\n%s" % (exc, traceback.format_exc()))
                if msg.get("id") is not None:
                    self.fail(msg["id"], -32603, "internal error: %s" % exc)

    def handle(self, msg):
        method = msg.get("method")
        rid = msg.get("id")
        params = msg.get("params") or {}

        if method == "initialize":
            self.reply(rid, {
                "protocolVersion": PROTOCOL_VERSION,
                "capabilities": {"tools": {"listChanged": False}},
                "serverInfo": {"name": SERVER_NAME,
                               "version": SERVER_VERSION},
            })
            return
        if method in ("notifications/initialized", "initialized"):
            return  # notification: no reply
        if method == "ping":
            self.reply(rid, {})
            return
        if method == "tools/list":
            self.reply(rid, {"tools": tool_schemas()})
            return
        if method == "tools/call":
            self.call_tool(rid, params)
            return
        if rid is None:
            return  # unknown notification: ignore, per spec
        self.fail(rid, -32601, "unknown method: %s" % method)

    def call_tool(self, rid, params):
        name = params.get("name")
        args = params.get("arguments") or {}
        try:
            text = dispatch(self.hol, name, args)
            is_error = False
        except (ValueError, KeyError) as exc:
            text, is_error = "bad request: %s" % exc, True
        except SessionDead as exc:
            text = ("the HOL server for this file died: %s\n"
                    "Call hol_restart on it." % exc)
            is_error = True
        except LspError as exc:
            text, is_error = "HOL server error: %s" % exc, True
        except Exception as exc:
            log("tool %s crashed: %s\n%s"
                % (name, exc, traceback.format_exc()))
            text, is_error = "%s: %s" % (type(exc).__name__, exc), True
        # A tool failure is a *result* with isError, not a protocol
        # error: the model is meant to see it and try something else.
        self.reply(rid, {"content": [{"type": "text", "text": text}],
                         "isError": is_error})


def main(argv=None):
    here = os.path.dirname(os.path.abspath(__file__))
    default_repo = os.path.normpath(os.path.join(here, "..", "..", ".."))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hol", default=None,
                        help="path to bin/hol (default: <tree>/bin/hol)")
    parser.add_argument("--repo", default=default_repo,
                        help="HOL tree relative paths resolve against")
    opts = parser.parse_args(argv)

    repo = os.path.abspath(opts.repo)
    hol_bin = opts.hol or os.path.join(repo, "bin", "hol")
    if not os.path.exists(hol_bin):
        log("no such hol binary: %s" % hol_bin)
        return 2

    pool = SessionPool(hol_bin)
    server = McpServer(Hol(pool, repo))
    log("serving MCP %s from %s" % (PROTOCOL_VERSION, hol_bin))
    try:
        server.serve()
    except KeyboardInterrupt:
        pass
    finally:
        pool.close_all()
    return 0


if __name__ == "__main__":
    sys.exit(main())
