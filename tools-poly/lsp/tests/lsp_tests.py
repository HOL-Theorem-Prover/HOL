#!/usr/bin/env python3
"""End-to-end LSP scenario tests.

Each test drives bin/hol lsp with a scripted client and asserts expected
notifications/state.  Designed to be self-contained: no editor
dependency, easy CI'ability, fast (target: <5 min total).

Run:  python3 tools-poly/lsp/tests/lsp_tests.py [test_name ...]
Exit code: 0 if all passed, 1 if any failed.
"""
import subprocess, threading, time, json, os, sys, re, tempfile

REPO = os.environ.get("HOL_LSP_TEST_REPO",
    "/repo/.claude/worktrees/lsp-project")
HOL_BIN = f"{REPO}/bin/hol"
# Extra args passed to `bin/hol lsp`.  E.g. `HOL_LSP_ARGS=--bare` to test
# against hol.state0 (relies on the LSP's own auto-loading to pull in
# bossLib etc.).  Split on whitespace, no shell quoting.
LSP_ARGS = os.environ.get("HOL_LSP_ARGS", "").split()

# ------------------------------------------------------------------
# LSP client — minimal, efficient, no O(N^2) buffer slicing.
# ------------------------------------------------------------------
class Client:
    def __init__(self, cwd):
        self.p = subprocess.Popen(
            [HOL_BIN, "lsp", *LSP_ARGS],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            cwd=cwd)
        self.buf = bytearray()
        self.buf_pos = 0
        self.msgs = []
        self.msgs_lock = threading.Lock()
        self.errs = bytearray()
        self._stop = False
        threading.Thread(target=self._reader, daemon=True).start()
        threading.Thread(target=self._ereader, daemon=True).start()

    def _reader(self):
        try:
            self._reader_loop()
        except Exception as e:
            sys.stderr.write(f"[client reader died] {type(e).__name__}: {e}\n")

    def _reader_loop(self):
        while not self._stop:
            try: c = self.p.stdout.read1(65536)
            except: return
            if not c: return
            self.buf.extend(c)
            while True:
                i = self.buf.find(b"\r\n\r\n", self.buf_pos)
                if i < 0: break
                try:
                    header = bytes(self.buf[self.buf_pos:i]).decode("ascii",
                                                                     "replace")
                except Exception:
                    header = ""
                length = None
                for line in header.split("\r\n"):
                    if line.lower().startswith("content-length:"):
                        try:
                            length = int(line.split(":")[1].strip())
                        except Exception:
                            length = None
                if length is None or len(self.buf) < i + 4 + length: break
                body = bytes(self.buf[i+4:i+4+length])
                self.buf_pos = i + 4 + length
                try:
                    m = json.loads(body)
                    with self.msgs_lock:
                        self.msgs.append(m)
                except Exception:
                    pass

    def _ereader(self):
        while not self._stop:
            try: c = self.p.stderr.read1(65536)
            except: return
            if not c: return
            self.errs.extend(c)

    def send(self, m):
        b = json.dumps(m).encode()
        self.p.stdin.write(b"Content-Length: %d\r\n\r\n%s" % (len(b), b))
        self.p.stdin.flush()

    def messages_since(self, from_idx):
        with self.msgs_lock:
            return list(self.msgs[from_idx:]), len(self.msgs)

    def total_msgs(self):
        with self.msgs_lock:
            return len(self.msgs)

    def wait_for_method(self, method, timeout, since=0):
        """Return the first message m with m.method == method arriving at
        index >= since.  Efficient for large message volumes: scans only
        the new tail on each poll, no whole-list copy."""
        deadline = time.time() + timeout
        idx = since
        while time.time() < deadline:
            # Snapshot end-index under lock, then scan msgs[idx:end]
            # without holding the lock.
            with self.msgs_lock:
                end = len(self.msgs)
            while idx < end:
                # Direct index access is safe — Python list append is
                # atomic under the GIL for a single element; the tail
                # up to `end` was written before we sampled end.
                m = self.msgs[idx]
                idx += 1
                if m.get("method") == method:
                    return m
            time.sleep(0.05)
        return None

    def wait_until(self, pred, timeout):
        """Wait until pred(client) is truthy. `pred` takes the client."""
        deadline = time.time() + timeout
        while time.time() < deadline:
            r = pred(self)
            if r: return r
            time.sleep(0.05)
        return None

    def stderr_text(self):
        return bytes(self.errs).decode(errors='replace')

    def close(self):
        try:
            self.send({"jsonrpc":"2.0","id":999,"method":"shutdown","params":None})
            time.sleep(0.1)
            self.send({"jsonrpc":"2.0","method":"exit","params":None})
            self.p.wait(timeout=3)
        except Exception:
            try: self.p.kill()
            except: pass
        self._stop = True


# ------------------------------------------------------------------
# Helpers
# ------------------------------------------------------------------
def _diag_count(client, uri, ver=None):
    """Return list of diagnostics from the LATEST publishDiagnostics for uri."""
    msgs, _ = client.messages_since(0)
    latest = None
    for m in msgs:
        if m.get("method") == "textDocument/publishDiagnostics":
            p = m["params"]
            if p["uri"] == uri and (ver is None or p.get("version") == ver):
                latest = p
    return (latest or {}).get("diagnostics", [])


def _count_out_of_date(diags):
    return sum(1 for d in diags if "out-of-date" in d.get("message", ""))


def _count_lib_first(diags):
    return sum(1 for d in diags if "Lib" in d.get("message", "")
                                    and "first" in d.get("message", ""))


def _count_diag_events(client, uri):
    msgs, _ = client.messages_since(0)
    return sum(1 for m in msgs
               if m.get("method") == "textDocument/publishDiagnostics"
               and m["params"]["uri"] == uri
               and m["params"]["diagnostics"])


def _init(c, root=None):
    c.send({"jsonrpc":"2.0","id":1,"method":"initialize",
            "params":{"capabilities":{},"rootUri":f"file://{root or REPO}",
                      "processId":None}})
    def got_init_reply(cl):
        msgs, _ = cl.messages_since(0)
        return any(m.get("id") == 1 for m in msgs)
    if not c.wait_until(got_init_reply, 5):
        raise RuntimeError("initialize timed out")
    c.send({"jsonrpc":"2.0","method":"initialized","params":{}})


def _did_open(c, uri, text, version=1):
    c.send({"jsonrpc":"2.0","method":"textDocument/didOpen",
            "params":{"textDocument":{"uri":uri,"languageId":"holsml",
                                        "version":version,"text":text}}})


def _did_change_full(c, uri, text, version):
    c.send({"jsonrpc":"2.0","method":"textDocument/didChange",
            "params":{"textDocument":{"uri":uri,"version":version},
                      "contentChanges":[{"text":text}]}})


# ------------------------------------------------------------------
# Assertions
# ------------------------------------------------------------------
class Failed(Exception): pass
def assert_eq(actual, expected, label):
    if actual != expected:
        raise Failed(f"{label}: expected {expected!r}, got {actual!r}")

def assert_le(actual, expected, label):
    if not (actual <= expected):
        raise Failed(f"{label}: expected <= {expected!r}, got {actual!r}")

def assert_ge(actual, expected, label):
    if not (actual >= expected):
        raise Failed(f"{label}: expected >= {expected!r}, got {actual!r}")

def assert_true(cond, label):
    if not cond: raise Failed(f"{label}: expected truthy, got {cond!r}")

def assert_contains(haystack, needle, label):
    if needle not in haystack:
        raise Failed(f"{label}: {needle!r} not in {haystack[:200]!r}")


# ------------------------------------------------------------------
# Scenarios
# ------------------------------------------------------------------
def test_smoke_handshake():
    c = Client("/tmp")
    try:
        _init(c)
        # No file opened; just shutdown cleanly.
    finally:
        c.close()
    assert_eq(c.p.returncode, 0, "clean exit")


def test_small_clean_file():
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/smoke_clean.sml"
        _did_open(c, uri, "Theory smoke_clean\n\nval a = 3\n")
        m = c.wait_for_method("$/compileCompleted", 30)
        assert_true(m is not None, "compileCompleted arrived")
        assert_eq(len(_diag_count(c, uri)), 0, "no diagnostics")
    finally:
        c.close()


def test_small_typerror_at_open():
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/smoke_bad.sml"
        _did_open(c, uri, "Theory smoke_bad\n\nval x = 3 + true\n")
        m = c.wait_for_method("$/compileCompleted", 30)
        assert_true(m is not None, "compileCompleted arrived")
        d = _diag_count(c, uri)
        assert_ge(len(d), 1, "at least one diagnostic")
        assert_true(any("Type error" in x.get("message","") or
                        "Can't unify" in x.get("message","")
                        for x in d),
                    f"got type-error diagnostic (msgs: {[x['message'][:80] for x in d]})")
    finally:
        c.close()


def test_small_recompile_blank_line():
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/smoke_recompile.sml"
        v1 = "Theory smoke_recompile\n\nval a = 3\n"
        _did_open(c, uri, v1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "first compileCompleted")
        idx_before = c.total_msgs()
        _did_change_full(c, uri, "Theory smoke_recompile\n\n\n\nval a = 3\n", 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx_before),
                    "second compileCompleted")
        # Look at LATEST diagnostics for version 2
        msgs, _ = c.messages_since(0)
        latest_v2 = None
        for m in msgs:
            if m.get("method") == "textDocument/publishDiagnostics":
                p = m["params"]
                if p["uri"] == uri and p.get("version") == 2:
                    latest_v2 = p["diagnostics"]
        assert_true(latest_v2 is not None, "have v2 diagnostics")
        assert_eq(len(latest_v2), 0, "no diagnostics after blank-line edit")
        assert_eq(_count_out_of_date(latest_v2), 0, "no out-of-date")
        assert_eq(_count_lib_first(latest_v2), 0, "no Lib.first")
    finally:
        c.close()


def test_small_recompile_type_error_inserted():
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/smoke_typerr.sml"
        v1 = "Theory smoke_typerr\n\nval a = 3\n"
        v2 = "Theory smoke_typerr\n\nval a = 3\nval b = 3 + true\n"
        _did_open(c, uri, v1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "first compileCompleted")
        idx_before = c.total_msgs()
        _did_change_full(c, uri, v2, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx_before),
                    "second compileCompleted")
        msgs, _ = c.messages_since(0)
        latest_v2 = None
        for m in msgs:
            if m.get("method") == "textDocument/publishDiagnostics":
                p = m["params"]
                if p["uri"] == uri and p.get("version") == 2:
                    latest_v2 = p["diagnostics"]
        assert_true(latest_v2 is not None, "have v2 diagnostics")
        # At least one diagnostic (the type error), no Lib.first / out-of-date
        # cascade noise.
        assert_ge(len(latest_v2), 1, "at least one diagnostic")
        assert_eq(_count_out_of_date(latest_v2), 0,
                  f"no out-of-date cascade (got: {[d['message'][:80] for d in latest_v2 if 'out-of-date' in d['message']]})")
        assert_eq(_count_lib_first(latest_v2), 0,
                  f"no Lib.first cascade (got count)")
        # And the diag SET size should be small — one real error, not 100.
        assert_le(len(latest_v2), 5, f"diag set stays small (got {len(latest_v2)})")
    finally:
        c.close()


def test_integer_first_compile():
    src = f"{REPO}/src/integer/integerScript.sml"
    c = Client(os.path.dirname(src))
    try:
        _init(c, REPO)
        uri = f"file://{src}"
        with open(src) as f: text = f.read()
        t0 = time.time()
        _did_open(c, uri, text)
        m = c.wait_for_method("$/compileCompleted", 60)
        elapsed = time.time() - t0
        assert_true(m is not None, f"compileCompleted arrived ({elapsed:.2f}s)")
        assert_le(elapsed, 20.0, f"first compile under 20s ({elapsed:.2f}s)")
        d = _diag_count(c, uri)
        assert_eq(len(d), 0, f"clean file: no diagnostics ({len(d)} got)")
    finally:
        c.close()


def test_integer_recompile_blank_lines():
    src = f"{REPO}/src/integer/integerScript.sml"
    c = Client(os.path.dirname(src))
    try:
        _init(c, REPO)
        uri = f"file://{src}"
        with open(src) as f: text = f.read()
        _did_open(c, uri, text)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "first compileCompleted")
        edited = text.replace("Theory integer\n", "\n\nTheory integer\n", 1)
        idx_before = c.total_msgs()
        t0 = time.time()
        _did_change_full(c, uri, edited, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 60, idx_before),
                    "second compileCompleted")
        elapsed = time.time() - t0
        assert_le(elapsed, 20.0, f"second compile under 20s ({elapsed:.2f}s)")
        msgs, _ = c.messages_since(0)
        latest_v2 = None
        for m in msgs:
            if m.get("method") == "textDocument/publishDiagnostics":
                p = m["params"]
                if p["uri"] == uri and p.get("version") == 2:
                    latest_v2 = p["diagnostics"]
        assert_true(latest_v2 is not None, "have v2 diagnostics")
        assert_eq(len(latest_v2), 0,
                  f"no diagnostics after blank-line ({len(latest_v2)} got)")
    finally:
        c.close()


def test_integer_recompile_with_type_error():
    """Michael's specific scenario: insert `val x = 3 + true` after the header."""
    src = f"{REPO}/src/integer/integerScript.sml"
    c = Client(os.path.dirname(src))
    try:
        _init(c, REPO)
        uri = f"file://{src}"
        with open(src) as f: text = f.read()
        _did_open(c, uri, text)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "first compileCompleted")
        lines = text.split("\n")
        # Find the closing '===' banner and insert after it
        banners = [i for i, l in enumerate(lines)
                   if l.startswith("(*==") and "==*)" in l]
        insert_at = banners[1] + 1
        lines.insert(insert_at, "val x = 3 + true")
        edited = "\n".join(lines)
        idx_before = c.total_msgs()
        _did_change_full(c, uri, edited, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 60, idx_before),
                    "second compileCompleted")
        msgs, _ = c.messages_since(0)
        latest_v2 = None
        for m in msgs:
            if m.get("method") == "textDocument/publishDiagnostics":
                p = m["params"]
                if p["uri"] == uri and p.get("version") == 2:
                    latest_v2 = p["diagnostics"]
        assert_true(latest_v2 is not None, "have v2 diagnostics")
        # We expect ONE real type-error diagnostic and no cascade.
        ood = _count_out_of_date(latest_v2)
        lf = _count_lib_first(latest_v2)
        assert_eq(ood, 0,
                  f"no out-of-date cascade (got {ood}, sample: {[d['message'][:80] for d in latest_v2 if 'out-of-date' in d['message']][:3]})")
        assert_eq(lf, 0, f"no Lib.first cascade (got {lf})")
        # There MUST be at least one diagnostic (the type error)
        assert_ge(len(latest_v2), 1, "at least the type error is reported")
        assert_le(len(latest_v2), 5,
                  f"only a handful of diagnostics (got {len(latest_v2)}: "
                  f"{[d['message'][:60] for d in latest_v2[:5]]})")
    finally:
        c.close()


def test_small_recompile_bare_val():
    """Unterminated `val` decl before another val: reproducer for the
    updateDiags Subscript bug where oldDiags outgrew the current-compile
    diags array across non-monotonic Progress positions."""
    original = "Theory small\nAncestors\n  arithmetic\n\nval a = 3\nval b = 4\n"
    lines = original.split("\n")
    lines.insert(4, "val")
    edited = "\n".join(lines)
    uri = "file:///tmp/small_bare_val.sml"
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        _did_open(c, uri, original)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "first compileCompleted")
        idx = c.total_msgs()
        _did_change_full(c, uri, edited, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx),
                    "second compileCompleted (would fail with cascading Subscript)")
        assert_true(c.wait_for_method("$/compileInterrupted", 1, idx) is None,
                    "no compileInterrupted")
    finally:
        c.close()


def test_integer_didChange_interrupts_stale_compile():
    """didChange mid-compile must interrupt the stale compile and start a
    fresh one.  Otherwise we get two compiles running against the same
    shared HOL state, cascading semantic errors, and diagnostics tagged
    with a stale version."""
    src = f"{REPO}/src/integer/integerScript.sml"
    c = Client(os.path.dirname(src))
    try:
        _init(c, REPO)
        uri = f"file://{src}"
        with open(src) as f: text = f.read()
        _did_open(c, uri, text)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "first compileCompleted")
        # v2: blank lines only, then before it finishes, v3: add a val.
        v2 = text.replace("Theory integer\n", "\n\nTheory integer\n", 1)
        v3 = v2.replace("Theory integer\n", "Theory integer\nval x = 3\n", 1)
        idx = c.total_msgs()
        _did_change_full(c, uri, v2, 2)
        time.sleep(0.5)   # let v2 compile start
        _did_change_full(c, uri, v3, 3)
        # We should see exactly one final compileCompleted, and any
        # diagnostics emitted after the didChange must be tagged v3
        # (or empty version-agnostic).  Zero stale-v2 diagnostics.
        m = c.wait_for_method("$/compileCompleted", 60, idx)
        assert_true(m is not None, "final compileCompleted")
        # After that final compileCompleted, check no v2-tagged diagnostics
        # appeared AFTER the v3 didChange was sent.
        msgs, _ = c.messages_since(idx)
        v3_didChange_idx = next(
            (i for i, m in enumerate(msgs)
             if m.get("method") == "textDocument/didChange"), None)
        stale_diags = [m for m in msgs
                       if m.get("method") == "textDocument/publishDiagnostics"
                       and m["params"].get("version") == 2
                       and m["params"].get("diagnostics")]
        assert_eq(len(stale_diags), 0,
                  f"no v2-tagged diagnostics after v3 (got {len(stale_diags)})")
    finally:
        c.close()


def test_hover_responsive_during_compile():
    """A didChange kicks off a compile; while it's running, hover
    requests must still be answered promptly (recv thread must not
    block on stopCompile).  Regression test for the freeze Michael
    hit typing `Theorem foo:\\n  x` at end of file — old stopCompile
    spin-waited for the (stuck) compile thread to exit and blocked
    every subsequent hover / didChange until Emacs killed the LSP."""
    src = f"{REPO}/src/integer/integerScript.sml"
    c = Client(os.path.dirname(src))
    try:
        _init(c, REPO)
        uri = f"file://{src}"
        with open(src) as f: text = f.read()
        _did_open(c, uri, text)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "first compileCompleted")
        # Kick a fresh compile by inserting text at file start.
        edited = "\n\n" + text
        _did_change_full(c, uri, edited, 2)
        time.sleep(0.3)   # let the new compile actually start
        # Fire a hover while the compile is still running.  Server
        # should respond within a couple of seconds.
        c.send({"jsonrpc":"2.0","id":424242,"method":"textDocument/hover",
                "params":{"textDocument":{"uri":uri},
                          "position":{"line":0,"character":0}}})
        def got(cl):
            with cl.msgs_lock:
                for m in cl.msgs:
                    if m.get("id") == 424242: return m
            return None
        t0 = time.time()
        reply = c.wait_until(got, 5)
        dt = time.time() - t0
        assert_true(reply is not None,
                    "hover reply arrived while compile was running "
                    "(waited {0:.1f}s)".format(dt))
        assert_le(dt, 3.0,
                  "hover responded quickly (took {0:.2f}s)".format(dt))
    finally:
        c.close()


def test_diagnostic_dedup():
    """Type-error inserted → publishDiagnostics event count should be small."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/dedup.sml"
        _did_open(c, uri,
                  "Theory dedup\n\nval a = 3\nval b : string = a\n"
                  "val c = a + 1\nval d = c * 2\nval e = d + a\n")
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Count non-empty diagnostic events for this uri
        n = _count_diag_events(c, uri)
        assert_le(n, 3, f"at most a few non-empty diag events (got {n})")
    finally:
        c.close()


# ------------------------------------------------------------------
# Runner
# ------------------------------------------------------------------
def test_hover_inside_proof_qed():
    """Hover on SML identifiers inside a Theorem-Proof-QED block should
    resolve to their SML type.  Previously the DecExpansion wrapping
    HOLTheoremDecl produced a zero-width synthetic-tuple Built parent
    over the tac's real-span children, blocking builtNavigateTo."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/proof_qed_hover.sml"
        src = ("Theory proof_qed_hover\n"
               "Ancestors arithmetic\n\n"
               "Theorem foo:\n"
               "  T\n"
               "Proof\n"
               "  rw[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 6 = "  rw[]", char 3 lands on 'w' of 'rw'.
        c.send({"jsonrpc":"2.0","id":42,"method":"textDocument/hover",
                "params":{"textDocument":{"uri":uri},
                          "position":{"line":6,"character":3}}})
        def got(cl):
            with cl.msgs_lock:
                for m in cl.msgs:
                    if m.get("id") == 42: return m
            return None
        reply = c.wait_until(got, 5)
        assert_true(reply is not None, "hover reply arrived")
        assert_true(reply.get("result") is not None,
                    "hover result non-null")
        md = reply["result"]["contents"]["value"]
        # rw : thm list -> tactic.  Require a real function type — not
        # just "term frag list" (the quotation arg's type), which was
        # what the previous synthetic-anchor bug returned.
        assert_true("val rw" in md and "->" in md and "tactic" in md,
                    "hover for rw is its SML type ({0!r})".format(md))
        assert_true("frag list" not in md,
                    "hover shouldn't be the quotation's `term frag list` "
                    "({0!r})".format(md))
    finally:
        c.close()


def test_thm_hover_shows_statement():
    """Hover on an SML identifier of type thm should render the
    theorem statement (⊢ ...) alongside the SML type."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/thm_hover_stmt.sml"
        src = ("Theory thm_hover_stmt\n"
               "Ancestors arithmetic\n\n"
               "Theorem plus_zero:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  ALL_TAC\n"
               "QED\n\n"
               "val myThm = plus_zero\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        c.send({"jsonrpc":"2.0","id":42,"method":"textDocument/hover",
                "params":{"textDocument":{"uri":uri},
                          "position":{"line":9,"character":14}}})
        def got(cl):
            with cl.msgs_lock:
                for m in cl.msgs:
                    if m.get("id") == 42: return m
            return None
        reply = c.wait_until(got, 5)
        assert_true(reply is not None, "hover reply arrived")
        md = reply["result"]["contents"]["value"]
        assert_true("thm" in md, f"markdown mentions thm type ({md!r})")
        assert_true("n + 0 = n" in md or "⊢" in md,
                    f"markdown includes theorem statement ({md!r})")
    finally:
        c.close()


def test_cheat_proofs_installed():
    """LSP session installs a set_prover thunk that returns
    mk_oracle_thm for any goal, so tactic bodies never run.  A goal
    that is deliberately false (m + n = 99999999) with a no-op
    tactic (ALL_TAC) must therefore compile without diagnostics."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/cheat_proofs.sml"
        src = ("Theory cheat_proofs\n"
               "Ancestors arithmetic\n\n"
               "Theorem definitely_false[allow_rebind]:\n"
               "  !m n:num. m + n = 99999999\n"
               "Proof\n"
               "  ALL_TAC\n"
               "QED\n")
        _did_open(c, uri, src)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        d = _diag_count(c, uri)
        assert_eq(len(d), 0,
                  f"no diagnostics (got {len(d)}, sample: "
                  f"{[x.get('message','')[:60] for x in d[:3]]})")
    finally:
        c.close()


def test_workdone_progress():
    """Server emits window/workDoneProgress/create + $/progress
    begin/report(s)/end during a compile."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/progress.sml"
        _did_open(c, uri, "Theory progress\n\nval a = 3\n")
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        msgs, _ = c.messages_since(0)
        create = [m for m in msgs
                  if m.get("method") == "window/workDoneProgress/create"]
        progress = [m for m in msgs if m.get("method") == "$/progress"]
        kinds = [m["params"]["value"]["kind"] for m in progress]
        assert_ge(len(create), 1, "at least one workDoneProgress/create")
        assert_true("begin" in kinds, f"got a 'begin' kind (kinds={kinds})")
        assert_true("end" in kinds, f"got an 'end' kind (kinds={kinds})")
    finally:
        c.close()


def test_edit_across_multibyte_char():
    """didChange positions must align with the server's byte-oriented
    buffer even when edits sit past multi-byte UTF-8 characters.
    Regression for the ⇒ Lexical-error bug: server advertises
    positionEncoding=utf-8 so eglot switches from UTF-16 code units to
    bytes; otherwise inserts land mid-codepoint and HOL's lexer
    complains about the first byte of a split character.

    Uses an incremental range-based didChange (not full-text) so the
    (line, character) → byte-offset conversion in applyEdit is
    actually exercised."""
    c = Client("/tmp")
    try:
        _init(c)
        uri = "file:///tmp/multibyte.sml"
        src = ("Theory mbtst\nAncestors hol\n\n"
               "Theorem foo:\n  x < y  ⇒ x < z + y\nProof\n  DECIDE_TAC\nQED\n")
        _did_open(c, uri, src)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "initial compileCompleted")
        d = _diag_count(c, uri)
        assert_eq(len(d), 0, f"clean file, no diagnostics ({len(d)} got)")

        # Insert one char past the ⇒ on line 4.  Under UTF-8 positions,
        # col 13 sits between "  " and "x" (after the ⇒ + space); under
        # UTF-16 it lands two bytes into the ⇒ sequence.  If we're
        # negotiating utf-8 correctly the insert of "y" here is a no-op
        # syntactically (adds "yx <").
        since = c.total_msgs()
        c.send({"jsonrpc":"2.0","method":"textDocument/didChange",
                "params":{"textDocument":{"uri":uri,"version":2},
                          "contentChanges":[{"range":{
                              "start":{"line":4,"character":13},
                              "end":{"line":4,"character":13}},
                              "rangeLength":0,"text":"y"}]}})
        assert_true(c.wait_for_method("$/compileCompleted", 30, since=since),
                    "post-edit compileCompleted")
        d = _diag_count(c, uri, ver=2)
        # We expect at most an "unbound variable y" style error from
        # HOL — NOT a lexical error on \226.
        lex = [x for x in d if "lexical error" in x.get("message","").lower()]
        assert_eq(len(lex), 0, f"no lex errors after multibyte-edge edit ({d})")
    finally:
        c.close()


TESTS = [
    ("smoke_handshake",              test_smoke_handshake),
    ("edit_across_multibyte",        test_edit_across_multibyte_char),
    ("small_clean_file",             test_small_clean_file),
    ("small_typerror_at_open",       test_small_typerror_at_open),
    ("small_recompile_blank_line",   test_small_recompile_blank_line),
    ("small_recompile_type_error",   test_small_recompile_type_error_inserted),
    ("small_recompile_bare_val",     test_small_recompile_bare_val),
    ("integer_first_compile",        test_integer_first_compile),
    ("integer_recompile_blank",      test_integer_recompile_blank_lines),
    ("integer_recompile_type_error", test_integer_recompile_with_type_error),
    ("integer_didChange_interrupts",
                                     test_integer_didChange_interrupts_stale_compile),
    ("hover_responsive_during_compile",
                                     test_hover_responsive_during_compile),
    ("diagnostic_dedup",             test_diagnostic_dedup),
    ("workdone_progress",            test_workdone_progress),
    ("cheat_proofs_installed",       test_cheat_proofs_installed),
    ("thm_hover_shows_statement",    test_thm_hover_shows_statement),
    ("hover_inside_proof_qed",       test_hover_inside_proof_qed),
]


def main():
    wanted = set(sys.argv[1:])
    passed = failed = 0
    for name, fn in TESTS:
        if wanted and name not in wanted: continue
        t0 = time.time()
        try:
            fn()
            dt = time.time() - t0
            print(f"  PASS  {name}  ({dt:.1f}s)")
            passed += 1
        except Failed as e:
            dt = time.time() - t0
            print(f"  FAIL  {name}  ({dt:.1f}s): {e}")
            failed += 1
        except Exception as e:
            dt = time.time() - t0
            print(f"  ERROR {name}  ({dt:.1f}s): {type(e).__name__}: {e}")
            failed += 1
    print(f"\n{passed} passed, {failed} failed")
    sys.exit(0 if failed == 0 else 1)


if __name__ == "__main__":
    main()
