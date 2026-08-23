#!/usr/bin/env python3
"""End-to-end LSP scenario tests.

Each test drives bin/hol lsp with a scripted client and asserts expected
notifications/state.  Designed to be self-contained: no editor
dependency, easy CI'ability, fast (target: <5 min total).

Run:  python3 tools-poly/lsp/tests/lsp_tests.py [test_name ...]
Exit code: 0 if all passed, 1 if any failed.
"""
import subprocess, threading, time, json, os, sys, re, tempfile, shutil

REPO = os.environ.get("HOL_LSP_TEST_REPO",
    "/repo/.claude/worktrees/lsp-project")
HOL_BIN = f"{REPO}/bin/hol"
DEFAULT_HEAP = f"{REPO}/bin/hol.state"
HOL_STATE0 = f"{REPO}/bin/hol.state0"
# Extra args passed to `bin/hol lsp`.  Split on whitespace, no shell
# quoting.  Note: `HOL_LSP_ARGS=--bare` is NOT supported for this
# suite.  Under hol.state0 the LSP auto-`use`s bossLib.uo on every
# didChange (loadedMods gets reverted between compiles), and repeated
# `.uo` execution creates fresh opaque type constructors that
# conflict with those already installed in globalNameSpace — three
# of the recompile tests then fail with hundreds of spurious
# diagnostics.  Real editor sessions never hit this: task #9's
# HOLHEAP auto-detect always resolves to a heap that already
# contains bossLib.
LSP_ARGS = os.environ.get("HOL_LSP_ARGS", "").split()

# ------------------------------------------------------------------
# LSP client — minimal, efficient, no O(N^2) buffer slicing.
# ------------------------------------------------------------------
class Client:
    def __init__(self, cwd, args=None):
        self.p = subprocess.Popen(
            [HOL_BIN, "lsp", *(args if args is not None else LSP_ARGS)],
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


def _init(c, root=None, timeout=5):
    c.send({"jsonrpc":"2.0","id":1,"method":"initialize",
            "params":{"capabilities":{},"rootUri":f"file://{root or REPO}",
                      "processId":None}})
    def got_init_reply(cl):
        msgs, _ = cl.messages_since(0)
        return any(m.get("id") == 1 for m in msgs)
    if not c.wait_until(got_init_reply, timeout):
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


def _line_col_at(text, byte_offset):
    """Byte offset → (line, character) using LSP positionEncoding=utf-8
    (see 1cfd8db81)."""
    prefix = text[:byte_offset]
    if "\n" not in prefix:
        return (0, byte_offset)
    line = prefix.count("\n")
    col = byte_offset - prefix.rfind("\n") - 1
    return (line, col)


def _did_change_incr(c, uri, old_text, byte_from, byte_to, insert, version):
    """Send an incremental `didChange` with a range covering
    `[byte_from, byte_to)` in `old_text`, replaced by `insert`."""
    frm = _line_col_at(old_text, byte_from)
    to  = _line_col_at(old_text, byte_to)
    c.send({"jsonrpc":"2.0","method":"textDocument/didChange",
            "params":{"textDocument":{"uri":uri,"version":version},
                      "contentChanges":[{
                          "range":{
                            "start":{"line":frm[0], "character":frm[1]},
                            "end":  {"line":to[0],  "character":to[1]}},
                          "text":insert}]}})


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
def test_hover_type_only_no_identifier_is_null():
    """Hover on a compound expression like `Conv (foo bar)` at a position
    between identifiers should not fall up to the enclosing expression's
    SML type ("Conv.conv", "Thm.thm -> Thm.thm", …).  Only per-identifier
    hovers (with a name) are useful."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/hover_typeonly.sml"
        # Line 3: "val f = rw[SUB_0]"  — cursor at char 8 lands just
        # after "= " on `r` of `rw` (an identifier, has a name → real
        # hover) but at char 10 sits on `[` (whitespace/bracket, no
        # identifier at this position; previously returned "thm list").
        src = ("Theory hover_typeonly\n"
               "Ancestors arithmetic\n"
               "val f = rw[SUB_0]\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Char 10 = '[' bracket — no identifier at this position.
        c.send({"jsonrpc":"2.0","id":52,"method":"textDocument/hover",
                "params":{"textDocument":{"uri":uri},
                          "position":{"line":2,"character":10}}})
        def got(cl):
            with cl.msgs_lock:
                for m in cl.msgs:
                    if m.get("id") == 52: return m
            return None
        reply = c.wait_until(got, 5)
        assert_true(reply is not None, "hover reply arrived")
        assert_eq(reply.get("result"), None,
                  "hover on non-identifier position returns null")
    finally:
        c.close()


def test_hover_on_proof_body_whitespace_is_null():
    """Hover on whitespace inside a Proof-QED body should return null.
    Previously the SML-side hover fell up to the enclosing tactic
    expression and returned its type (`goal -> goal list * validation`),
    which is never informative."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/proof_ws_hover.sml"
        src = ("Theory proof_ws_hover\n"
               "Ancestors arithmetic\n\n"
               "Theorem foo:\n"
               "  T\n"
               "Proof\n"
               "  ARITH_TAC\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 5 = "Proof" — char 5 is just past the keyword, on
        # whitespace.  Previously would give the tactic-type hover.
        c.send({"jsonrpc":"2.0","id":51,"method":"textDocument/hover",
                "params":{"textDocument":{"uri":uri},
                          "position":{"line":5,"character":5}}})
        def got(cl):
            with cl.msgs_lock:
                for m in cl.msgs:
                    if m.get("id") == 51: return m
            return None
        reply = c.wait_until(got, 5)
        assert_true(reply is not None, "hover reply arrived")
        assert_eq(reply.get("result"), None,
                  "hover on proof-body whitespace returns null")
    finally:
        c.close()


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


def test_hover_inside_term_quotation():
    """Hover inside an explicit ``‘‘...’’`` HOL term quotation resolves
    identifiers via the HOL parser (Preterm walker with type + theory
    info), not just as raw SML `term frag list`.  Exercises
    hover_quote_init.ML's Preterm-based callback registered into
    LSPExtension.hoverQuotation.

    Companion test test_hover_inside_theorem_body covers the same
    machinery on Theorem-QED bodies (which route through the
    HOLSourceExpand PQuote-annotation path)."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/quote_hover.sml"
        # ``‘‘`` and ``’’`` are 3-byte UTF-8 sequences each.  The line
        # `val body = ‘‘!n:num. SUC n = n + 1’’` has these BYTE columns:
        #   0..10   = "val body = " (11 bytes)
        #   11..13  = first ``‘`` (3 bytes)
        #   14..16  = second ``‘``
        #   17      = '!'
        #   18      = 'n' (binder)
        #   19..24  = ':num. '
        #   25..27  = 'SUC'
        #   28      = ' '
        #   29      = 'n' (bound)
        src = ("Theory quote_hover\n"
               "Ancestors arithmetic\n\n"
               "val body = ‘‘"
               "!n:num. SUC n = n + 1’’\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")

        def do_hover(id_, line, char):
            c.send({"jsonrpc":"2.0","id":id_,
                    "method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":line,"character":char}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            reply = c.wait_until(got, 5)
            assert_true(reply is not None,
                        f"hover reply {id_} arrived")
            return reply

        # Hover on middle char of SUC (byte col 26): expect const info.
        reply = do_hover(101, 3, 26)
        result = reply.get("result")
        assert_true(result is not None,
                    f"hover on SUC returned a result ({reply})")
        md = result["contents"]["value"]
        assert_true("SUC" in md,
                    f"hover on SUC mentions the name ({md!r})")
        assert_true("num" in md,
                    f"hover on SUC mentions num type ({md!r})")

        # Hover on bound `n` at byte col 29: expect bound-var info.
        reply = do_hover(102, 3, 29)
        result = reply.get("result")
        assert_true(result is not None,
                    f"hover on bound n returned a result ({reply})")
        md = result["contents"]["value"]
        assert_true("bound" in md,
                    f"hover on bound n says 'bound' ({md!r})")
    finally:
        c.close()


def test_hover_inside_theorem_body():
    """Hover inside the term body of a Theorem-QED declaration works
    just as hover inside an explicit ``‘‘...’’`` quotation.  Requires
    HOLSourceExpand's expandQuote to give the synthesized quote List a
    body-precise span AND to wrap it in ExpExpansion(HOLQuote-synth,
    ...) so the LSP annotator adds PQuote."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/thmqed_body_hover.sml"
        # 0: Theory quote_hover
        # 1: Ancestors arithmetic
        # 2:
        # 3: Theorem foo:
        # 4:   !n:num. SUC n = n + 1
        #      0123456789012345678901
        # 4 cols: 2='!' 3='n' (binder) 10..12='SUC' 14='n' (bound) ...
        src = ("Theory thm_body_hover\n"
               "Ancestors arithmetic\n\n"
               "Theorem foo:\n"
               "  !n:num. SUC n = n + 1\n"
               "Proof\n"
               "  ALL_TAC\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")

        def do_hover(id_, line, char):
            c.send({"jsonrpc":"2.0","id":id_,
                    "method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":line,"character":char}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            reply = c.wait_until(got, 5)
            assert_true(reply is not None,
                        f"hover reply {id_} arrived")
            return reply

        reply = do_hover(201, 4, 11)
        result = reply.get("result")
        assert_true(result is not None,
                    f"hover on SUC (theorem body) returned result "
                    f"({reply})")
        md = result["contents"]["value"]
        assert_true("SUC" in md,
                    f"hover on SUC mentions the name ({md!r})")
        assert_true("num" in md,
                    f"hover on SUC mentions num ({md!r})")

        reply = do_hover(202, 4, 14)
        result = reply.get("result")
        assert_true(result is not None,
                    f"hover on bound n (theorem body) returned "
                    f"result ({reply})")
        md = result["contents"]["value"]
        assert_true("bound" in md,
                    f"hover on bound n says 'bound' ({md!r})")
    finally:
        c.close()


def test_hover_at_body_boundary_and_operators():
    """Cursor at three tricky positions in a Theorem body:
    (a) the very first byte of the body — must not be claimed by
        the preceding synthetic-`bar` string arg (seam bug);
    (b) the byte of an infix operator whose HOL parser gave it a
        synthetic Locn borrowed from an operand (∧ in `p ∧ q ⇒ r`);
    (c) the bytes of an operator whose Locn doesn't span its source
        position at all (⇒ in the same expression) — must fall back
        via the enclosing Comb's Locn."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/hover_boundary.sml"
        # Line 3 (0-origin): "Theorem bar: p ∧ q ⇒ r"
        # UTF-8 byte columns:
        #   13='p'  14=' '  15..17='∧'  18=' '  19='q'  20=' '
        #   21..23='⇒'  24=' '  25='r'
        src = ("Theory hover_boundary\n"
               "Ancestors hol\n\n"
               "Theorem bar: p ∧ q ⇒ r\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")

        def hover(id_, ch):
            c.send({"jsonrpc":"2.0","id":id_,"method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":3,"character":ch}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            reply = c.wait_until(got, 5)
            assert_true(reply is not None, f"hover reply {id_} arrived")
            return reply.get("result")

        # (a) Body-boundary: cursor at byte 13 = 'p'.  Must NOT return
        # "string" (which is what the SML tree walk-up would give from
        # the synthetic nameAttrs `mkString(pos, "bar")` whose exclusive
        # end coincides with the body's inclusive start).
        r = hover(301, 13)
        assert_true(r is not None, "hover on 'p' returned result")
        md = r["contents"]["value"]
        assert_true("p " in md and "bool" in md and "string" not in md,
                    f"hover on 'p' identifies the variable ({md!r})")

        # (b) Operator ∧ at byte 16 (middle of the 3-byte UTF-8 sequence).
        # Must find the ∧/`/\` Const via the Comb.combLocn fallback.
        r = hover(302, 16)
        assert_true(r is not None, "hover on ∧ returned result")
        md = r["contents"]["value"]
        assert_true("/\\" in md or "∧" in md,
                    f"hover on ∧ identifies the conjunction ({md!r})")

        # (c) Operator ⇒ at byte 22 (middle byte).  The parser gives
        # `==>` Const a Locn that doesn't include this byte, so the
        # walker must fall back through the outer Comb's Locn.
        r = hover(303, 22)
        assert_true(r is not None, "hover on ⇒ returned result")
        md = r["contents"]["value"]
        assert_true("==>" in md,
                    f"hover on ⇒ identifies the implication ({md!r})")
    finally:
        c.close()


def test_hover_across_utf8_binder_and_var():
    """Hover across a body that mixes ``∀``, a bound variable, and an
    infix operator whose UTF-8 byte width matters for cursor
    resolution.  Regression for two bugs surfaced by the eglot log:

    (a) `stripDelims` (in hover_quote_init.ML) only inspected the
    first UTF-8 byte to detect quote delimiters, and ``E2`` is the
    leading byte of ``∀`` (as well as ``‘`` / ``’``).  A leading
    ``∀`` in the body was eaten, the parser saw a truncated term,
    and every hover returned nil.

    (b) `term_tokens.stdfinish` split a lexeme's Locn by codepoint
    count applied to a byte-based `LocA` column.  For lexeme ``∀p``
    it gave ``∀`` a 1-byte Locn and ``p`` a 3-byte Locn — hovers on
    the ``∀`` symbol's own bytes (or on the binder ``p``) missed
    the intended leaf and returned the enclosing operator instead."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/utf8_binder.sml"
        # Line 3 = "Theorem bar: ∀p. p ∧ q ⇒ r"
        # UTF-8 byte columns:
        #   0..11 "Theorem bar:"  12 space  13..15 ∀  16 p (binder)
        #   17 .  18 space  19 p (occurrence)  20 space  21..23 ∧
        #   24 space  25 q  26 space  27..29 ⇒  30 space  31 r
        src = ("Theory utf8_binder\n"
               "Ancestors hol\n\n"
               "Theorem bar: ∀p. p ∧ q ⇒ r\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "compileCompleted")

        def hover(id_, ch):
            c.send({"jsonrpc":"2.0","id":id_,
                    "method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":3,"character":ch}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            reply = c.wait_until(got, 5)
            assert_true(reply is not None, f"hover {id_} arrived")
            r = reply.get("result")
            assert_true(r is not None, f"hover on col {ch} non-null ({reply})")
            return r["contents"]["value"]

        # ∀ (byte 13, first byte of the 3-byte codepoint)
        md = hover(401, 13)
        assert_true("!" in md and "bool" in md,
                    f"hover on ∀ identifies universal ({md!r})")

        # Binder p (byte 16, immediately after ∀'s 3 bytes)
        md = hover(402, 16)
        assert_true("p " in md and "bound" in md,
                    f"hover on binder p is 'bound' ({md!r})")

        # Occurrence p (byte 19) — should also be bound after the ∀
        md = hover(403, 19)
        assert_true("p " in md and "bound" in md,
                    f"hover on p occurrence is 'bound' ({md!r})")

        # ⇒ (byte 27, first byte of the 3-byte codepoint)
        md = hover(404, 27)
        assert_true("==>" in md,
                    f"hover on ⇒ identifies implication ({md!r})")

        # Format sanity: no double colons.
        assert_true(": :" not in md,
                    f"no double colon in output ({md!r})")
    finally:
        c.close()


def test_hover_inside_definition_body():
    """Hover inside a Definition body works the same way as inside a
    Theorem body.  Regression for the synthetic termination-option
    arg bug: expandDec for HOLDefinition wrapped the quotation in
    `App(_, mkIdent(definition_, "NONE"))`, giving the outer App
    span `(definition_, definition_+4)` and hiding the body's
    PQuote node behind a sibling magicBind binding that findChild
    picked first.  Fix: anchor termOpt at `stop` so App's expStop
    covers the body."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/defn_hover.sml"
        # Line 3 = "Definition foo:"
        # Line 4 = "  f x y = case x of"
        # Line 6 = "          | t::ts => LENGTH ts + 6"
        src = ("Theory t\n"
               "Ancestors list arithmetic\n\n"
               "Definition foo:\n"
               "  f x y = case x of\n"
               "            [] => 3\n"
               "          | t::ts => LENGTH ts + 6\n"
               "End\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "compileCompleted")

        def hover(id_, line, ch):
            c.send({"jsonrpc":"2.0","id":id_,
                    "method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":line,"character":ch}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            reply = c.wait_until(got, 5)
            assert_true(reply is not None, f"hover {id_} arrived")
            r = reply.get("result")
            assert_true(r is not None, f"hover {id_} non-null result")
            return r["contents"]["value"]

        # x is a bound argument of f (Definition body line 4).
        md = hover(500, 4, 4)
        assert_true("x " in md and "list" in md,
                    f"hover on x resolves as list-typed ({md!r})")
        assert_true("string" not in md,
                    f"hover on x isn't the SML `string` walk-up ({md!r})")

        # LENGTH is a constant (list theory).  Line 6 char 21 = `L`.
        md = hover(501, 6, 21)
        assert_true("LENGTH" in md and "num" in md,
                    f"hover on LENGTH identifies the constant ({md!r})")
    finally:
        c.close()


def test_stale_sml_binding_dropped():
    """Deleting a `val foo = …` line and recompiling must remove foo
    from what later hovers and later files see.  Before the
    LSPNameSpace file-layer, Poly/ML's `globalNameSpace` retained
    the binding across compiles because there's no `#deleteVal` —
    hovering at the deleted position still returned the retained
    Values.value, and a fresh file referencing `foo` still compiled."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/stale.sml"
        _did_open(c, uri, "Theory stale\n\nval myfoo = 42\n", 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "first compileCompleted")

        def hover(id_, line, ch):
            c.send({"jsonrpc":"2.0","id":id_,
                    "method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":line,"character":ch}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            return c.wait_until(got, 5)

        # Hover on `myfoo` — should identify the int binding.
        r = hover(700, 2, 6)
        v = (r.get("result") or {}).get("contents", {}).get("value") \
            if r and r.get("result") else None
        assert_true(v is not None and "myfoo" in v and "int" in v,
                    f"first hover on myfoo shows int ({v!r})")

        # Delete the val decl and recompile.
        idx = c.total_msgs()
        _did_change_full(c, uri, "Theory stale\n\n\n", 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx),
                    "second compileCompleted")

        # Open a fresh file that references myfoo — should NOT resolve.
        idx = c.total_msgs()
        uri2 = "file:///tmp/staleref.sml"
        _did_open(c, uri2,
                  "Theory staleref\n\nval z = myfoo + 1\n", 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx),
                    "refstale compileCompleted")
        msgs, _ = c.messages_since(0)
        latest = None
        for m in msgs:
            if m.get("method") == "textDocument/publishDiagnostics":
                p = m["params"]
                if p["uri"] == uri2:
                    latest = p
        diags = (latest or {}).get("diagnostics", [])
        assert_true(any("myfoo" in d.get("message", "")
                        and "not been declared" in d.get("message", "")
                        for d in diags),
                    f"stale myfoo is undeclared in a new file ({diags})")
    finally:
        c.close()


def test_hover_inside_inductive_body():
    """Hover inside an Inductive body's rules.  Two structural
    fixes are needed to make this work:

    - HOLSourceExpand for HOLInductiveDecl builds its own List
      inline (not via expandQuote), with `mkList (inductive_, …)`
      giving left=stop=inductive_ (zero-width) and no
      ExpExpansion(HOLQuote, …) wrapper.  Fix: give the List a
      body-precise span from the qdecl positions and wrap in
      ExpExpansion so the annotator adds PQuote.

    - The extracted body contains DefinitionLabels (`[nil:]`,
      `[cons:]`) that HOL's Parse.Term can't parse.  hover_quote_init's
      callback now splits the body on `[…:]` regions and parses only
      the region containing the cursor.
    """
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/ind_hover.sml"
        # Line 3 = "Inductive foo:"
        # Line 4 = "[nil:]  foo []"
        #           01234567890123
        # Line 5 = "[cons:] !x xs. foo xs ==> foo (x :: xs)"
        #           0         1         2         3
        #           0123456789012345678901234567890123456789
        src = ("Theory t\nAncestors list arithmetic\n\n"
               "Inductive foo:\n"
               "[nil:]  foo []\n"
               "[cons:] !x xs. foo xs ==> foo (x :: xs)\n"
               "End\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "compileCompleted")

        def hover(id_, line, ch):
            c.send({"jsonrpc":"2.0","id":id_,
                    "method":"textDocument/hover",
                    "params":{"textDocument":{"uri":uri},
                              "position":{"line":line,"character":ch}}})
            def got(cl):
                with cl.msgs_lock:
                    for m in cl.msgs:
                        if m.get("id") == id_: return m
                return None
            reply = c.wait_until(got, 5)
            assert_true(reply is not None, f"hover {id_} arrived")
            r = reply.get("result")
            assert_true(r is not None, f"hover {id_} non-null result ({reply})")
            return r["contents"]["value"]

        # foo (rule nil) — the relation being defined.
        md = hover(600, 4, 8)
        assert_true("foo " in md and "list" in md,
                    f"hover on foo (rule nil) identifies it ({md!r})")
        # bound x in cons rule (line 5 char 9).
        md = hover(601, 5, 9)
        assert_true("x " in md and "bound" in md,
                    f"hover on x is bound ({md!r})")
        # LENGTH-like constant: `foo` in cons rule body (line 5 char 15).
        md = hover(602, 5, 15)
        assert_true("foo " in md,
                    f"hover on body-foo identifies ({md!r})")
    finally:
        c.close()


def _wait_for_exit(p, timeout=10):
    deadline = time.time() + timeout
    while time.time() < deadline:
        if p.poll() is not None: return True
        time.sleep(0.1)
    return False


def test_heap_autodetect_from_holmakefile():
    """A HOLHEAP path in the cwd's Holmakefile is picked up by the LSP
    server's heap auto-detect (hol.ML get_heap_name).  Verified by
    pointing HOLHEAP at a non-existent file: the server dies during
    base-state load with a stderr message containing that path.
    Without the auto-detect widening for LSP mode (task #9), the
    server would silently load the default hol.state instead."""
    d = tempfile.mkdtemp(prefix="lsp_heap_")
    bogus = f"{d}/no_such_heap_deadbeef"
    try:
        with open(f"{d}/Holmakefile", "w") as f:
            f.write(f"HOLHEAP = {bogus}\n")
        c = Client(d, args=[])
        try:
            assert_true(_wait_for_exit(c.p, 15),
                        f"server exited on bogus heap "
                        f"(stderr tail: {c.stderr_text()[-400:]!r})")
            assert_contains(c.stderr_text(), bogus,
                            "stderr mentions the bogus HOLHEAP path")
            assert_contains(c.stderr_text(), "Couldn't load HOL base-state",
                            "stderr mentions the base-state load failure")
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def test_heap_autodetect_no_holmakefile():
    """With no Holmakefile in cwd, the server falls back to the default
    hol.state and boots normally.  Verified via the initialize
    handshake."""
    d = tempfile.mkdtemp(prefix="lsp_heap_")
    try:
        c = Client(d, args=[])
        try:
            _init(c, timeout=30)
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def test_heap_autodetect_holmakefile_without_holheap():
    """A Holmakefile without a HOLHEAP line also falls back to the
    default hol.state.  Verified via the initialize handshake."""
    d = tempfile.mkdtemp(prefix="lsp_heap_")
    try:
        with open(f"{d}/Holmakefile", "w") as f:
            f.write("INCLUDES = /tmp/foo\n")
        c = Client(d, args=[])
        try:
            _init(c, timeout=30)
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def _resume_events(client, since=0, uri=None):
    msgs, _ = client.messages_since(since)
    out = []
    for m in msgs:
        if m.get("method") != "$/compileResumedAt": continue
        if uri is None or m["params"]["uri"] == uri:
            out.append(m["params"])
    return out


def test_snapshot_resume_late_edit():
    """After compiling a multi-dec script, an incremental `didChange`
    near the end reuses a snapshot from an earlier dec: the resumed
    compile emits `$/compileResumedAt` with pos > 0 and produces the
    same v2 diagnostic set as v1 had."""
    d = tempfile.mkdtemp(prefix="lsp_resume_")
    try:
        body = "\n".join(f"val x{i} = {i}" for i in range(20))
        src = f"Theory resumescr\n\n{body}\n"
        c = Client(d, args=["--dbg"])
        try:
            _init(c, d, timeout=30)
            uri = f"file://{d}/resumescrScript.sml"
            _did_open(c, uri, src)
            assert_true(c.wait_for_method("$/compileCompleted", 60),
                        "first compileCompleted")
            v1_diags = _diag_count(c, uri)
            assert_eq(len(_resume_events(c, uri=uri)), 0,
                      "no resume event on first compile")

            # Insert two blank lines just before `val x19`.
            at = src.index("val x19")
            idx_before = c.total_msgs()
            _did_change_incr(c, uri, src, at, at, "\n\n", 2)
            assert_true(c.wait_for_method("$/compileCompleted", 60, idx_before),
                        "second compileCompleted")
            resumes = _resume_events(c, since=idx_before, uri=uri)
            assert_eq(len(resumes), 1,
                      f"exactly one resume event on late edit ({resumes!r})")
            assert_true(resumes[0]["pos"] > 0,
                        f"resume pos > 0 ({resumes[0]})")
            v2_diags = _diag_count(c, uri, ver=2)
            assert_eq(len(v1_diags), len(v2_diags),
                      f"diag count parity v1={len(v1_diags)} v2={len(v2_diags)}")
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def test_snapshot_resume_early_edit_falls_back():
    """An incremental `didChange` at byte 0 forces a full boot-restore
    — all snapshots have endByte > 0, so none qualifies for resume."""
    d = tempfile.mkdtemp(prefix="lsp_resume_")
    try:
        body = "\n".join(f"val x{i} = {i}" for i in range(20))
        src = f"Theory resumescr2\n\n{body}\n"
        c = Client(d, args=["--dbg"])
        try:
            _init(c, d, timeout=30)
            uri = f"file://{d}/resumescr2Script.sml"
            _did_open(c, uri, src)
            assert_true(c.wait_for_method("$/compileCompleted", 60),
                        "first compileCompleted")

            # Prepend a comment via an incremental change at byte 0.
            idx_before = c.total_msgs()
            _did_change_incr(c, uri, src, 0, 0, "(* leading *)\n", 2)
            assert_true(c.wait_for_method("$/compileCompleted", 60, idx_before),
                        "second compileCompleted")
            resumes = _resume_events(c, since=idx_before, uri=uri)
            assert_eq(len(resumes), 0,
                      f"no resume event on early edit ({resumes!r})")
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def test_snapshot_resume_full_text_replace_resets():
    """A `didChange` with `range = null` (full-text replace) drops all
    snapshots — no `$/compileResumedAt` fires on the next compile."""
    d = tempfile.mkdtemp(prefix="lsp_resume_")
    try:
        body = "\n".join(f"val x{i} = {i}" for i in range(20))
        src = f"Theory resumescr3\n\n{body}\n"
        c = Client(d, args=["--dbg"])
        try:
            _init(c, d, timeout=30)
            uri = f"file://{d}/resumescr3Script.sml"
            _did_open(c, uri, src)
            assert_true(c.wait_for_method("$/compileCompleted", 60),
                        "first compileCompleted")

            # Full-text replace: same body but +1 blank line at start.
            edited = "\n" + src
            idx_before = c.total_msgs()
            # `_did_change_full` uses `range = null`.
            _did_change_full(c, uri, edited, 2)
            assert_true(c.wait_for_method("$/compileCompleted", 60, idx_before),
                        "second compileCompleted")
            resumes = _resume_events(c, since=idx_before, uri=uri)
            assert_eq(len(resumes), 0,
                      f"no resume on full-text replace ({resumes!r})")
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def test_snapshot_resume_survives_grammar_delta():
    """A script that mutates the parser grammar via `overload_on` in
    an early dec, then uses the overload in a later dec: a resume
    from a snapshot AFTER the overload must preserve the overload.
    Tests that `Parse.invalidate_caches` in `restoreCompileSnap`
    rebuilds the parser closures correctly."""
    d = tempfile.mkdtemp(prefix="lsp_resume_")
    try:
        src = (
            "Theory resumescr4\n\n"
            "val _ = Parse.overload_on (\"+\", boolSyntax.disjunction)\n"
            + "\n".join(f"val x{i} = {i}" for i in range(15))
            + "\nval combined = ``T + F``\n"
        )
        c = Client(d, args=["--dbg"])
        try:
            _init(c, d, timeout=30)
            uri = f"file://{d}/resumescr4Script.sml"
            _did_open(c, uri, src)
            assert_true(c.wait_for_method("$/compileCompleted", 60),
                        "first compileCompleted")
            v1_diags = _diag_count(c, uri)

            # Insert a blank line just before `val combined` via an
            # incremental change; snapshot after `val x14` should be
            # picked, and its restore must preserve the overload.
            at = src.index("val combined")
            idx_before = c.total_msgs()
            _did_change_incr(c, uri, src, at, at, "\n\n", 2)
            assert_true(c.wait_for_method("$/compileCompleted", 60, idx_before),
                        "second compileCompleted")
            v2_diags = _diag_count(c, uri, ver=2)
            assert_eq(len(v1_diags), len(v2_diags),
                      f"diag count parity v1={len(v1_diags)} v2={len(v2_diags)}")
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def test_snapshot_resume_second_edit_after_completion():
    """Two consecutive `didChange` edits: verify the second compile
    still resumes from a snapshot taken during the first-triggered
    compile."""
    d = tempfile.mkdtemp(prefix="lsp_resume_")
    try:
        body = "\n".join(f"val x{i} = {i}" for i in range(20))
        src = f"Theory resumescr5\n\n{body}\n"
        c = Client(d, args=["--dbg"])
        try:
            _init(c, d, timeout=30)
            uri = f"file://{d}/resumescr5Script.sml"
            _did_open(c, uri, src)
            assert_true(c.wait_for_method("$/compileCompleted", 60),
                        "first compileCompleted")

            at1 = src.index("val x19")
            idx1 = c.total_msgs()
            _did_change_incr(c, uri, src, at1, at1, "\n\n", 2)
            assert_true(c.wait_for_method("$/compileCompleted", 60, idx1),
                        "second compileCompleted")
            assert_eq(len(_resume_events(c, since=idx1, uri=uri)), 1,
                      "second compile resumed")

            # The text now has "\n\n" before "val x19".
            src_v2 = src[:at1] + "\n\n" + src[at1:]
            at2 = src_v2.index("val x18")
            idx2 = c.total_msgs()
            _did_change_incr(c, uri, src_v2, at2, at2, "\n\n", 3)
            assert_true(c.wait_for_method("$/compileCompleted", 60, idx2),
                        "third compileCompleted")
            assert_eq(len(_resume_events(c, since=idx2, uri=uri)), 1,
                      "third compile also resumed")
        finally:
            c.close()
    finally:
        shutil.rmtree(d, ignore_errors=True)


def _send_goalstate(c, req_id, uri, line, char):
    c.send({"jsonrpc":"2.0","id":req_id,
            "method":"$/hol/goalState",
            "params":{"textDocument":{"uri":uri},
                      "position":{"line":line,"character":char}}})
    def got(cl):
        with cl.msgs_lock:
            for m in cl.msgs:
                if m.get("id") == req_id: return m
        return None
    return c.wait_until(got, 5)


def test_goalState_inside_proof():
    """Slice B: cursor inside a `Proof … QED` block returns the enclosing
    theorem's name and parsed statement as the initial goal (step 0, no
    assumptions)."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_inside.sml"
        src = ("Theory goalstate_inside\n"
               "Ancestors arithmetic\n\n"
               "Theorem plus_zero:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  rw[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 6 = "  rw[]" — inside the Proof body.
        reply = _send_goalstate(c, 101, uri, 6, 3)
        assert_true(reply is not None, "reply arrived")
        result = reply.get("result")
        assert_true(result is not None,
                    f"result populated ({reply!r})")
        assert_eq(result.get("theorem"), "plus_zero", "theorem name")
        assert_eq(result.get("step"), 0, "step index 0")
        goals = result.get("goals")
        assert_true(isinstance(goals, list) and len(goals) == 1,
                    f"one goal ({goals!r})")
        assert_eq(goals[0].get("asms"), [], "no assumptions initially")
        goal_text = goals[0].get("goal", "")
        assert_true("n + 0 = n" in goal_text or "n + 0" in goal_text,
                    f"goal renders the theorem statement ({goal_text!r})")
    finally:
        c.close()


def test_goalState_outside_proof():
    """Slice B: cursor outside any `Proof … QED` block returns null."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_outside.sml"
        src = ("Theory goalstate_outside\n"
               "Ancestors arithmetic\n\n"
               "Theorem foo:\n"
               "  T\n"
               "Proof\n"
               "  rw[]\n"
               "QED\n"
               "\n"
               "val x = 3\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 3 = "Theorem foo:" — before Proof.
        r1 = _send_goalstate(c, 201, uri, 3, 4)
        assert_eq(r1.get("result"), None,
                  "cursor before Proof → null")
        # Line 9 = "val x = 3" — after QED.
        r2 = _send_goalstate(c, 202, uri, 9, 4)
        assert_eq(r2.get("result"), None,
                  "cursor after QED → null")
    finally:
        c.close()


def test_goalState_step_advances_within_proof():
    """Slice D: cursor at successive positions inside a Proof body sees
    the goal-state advance step-by-step.  Start of Proof body → initial
    goal; after the first tactic runs → whatever it produced."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_step.sml"
        # Theorem: `!n:num. n + 0 = n`.  Applying `gen_tac` drops the
        # binder, leaving  `n + 0 = n`.
        src = ("Theory goalstate_step\n"
               "Ancestors arithmetic\n\n"
               "Theorem step_test:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  gen_tac >> rw[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 6 is "  gen_tac >> rw[]" (0-based).  Cursor at char 2
        # (start of gen_tac) → step 0 (initial goal, binder still there).
        r0 = _send_goalstate(c, 401, uri, 6, 2)
        result0 = r0.get("result")
        assert_true(result0 is not None,
                    f"pre-gen_tac has a goal ({r0!r})")
        goal0 = result0["goals"][0]["goal"]
        assert_true("!" in goal0 or "∀" in goal0,
                    f"initial goal still has the quantifier ({goal0!r})")
        # Cursor at char 15 (past `>>`, on `rw[]`) → step 1, after
        # gen_tac has run.  The universal binder is gone.
        r1 = _send_goalstate(c, 402, uri, 6, 15)
        result1 = r1.get("result")
        assert_true(result1 is not None,
                    f"pre-rw has a goal ({r1!r})")
        step1 = result1.get("step")
        assert_true(step1 >= 1, f"advanced past step 0 ({step1})")
        goal1 = result1["goals"][0]["goal"]
        assert_true("!" not in goal1 and "∀" not in goal1,
                    f"quantifier stripped after gen_tac ({goal1!r})")
    finally:
        c.close()


def test_goalState_incomplete_proof_body():
    """Slice G.1: a Theorem missing its QED (user still typing the
    proof) still yields a goalState response for cursors inside the
    in-progress Proof body — driving the live-editing UX."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/incomplete_proof.sml"
        # No QED, no trailing content after the tactic body.
        src = ("Theory incomplete_proof\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  gen_tac >> rw[]\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted (even with parse errors)")
        # Line 6 = "  gen_tac >> rw[]"; cursor at char 2 = start of tactic.
        r = _send_goalstate(c, 901, uri, 6, 2)
        result = r.get("result")
        assert_true(result is not None,
                    f"in-progress proof yields a state ({r!r})")
        assert_eq(result.get("theorem"), "t", "theorem name")
        # step 0 = pre-first-tactic; initial goal still shows the ∀.
        goal0 = result["goals"][0]["goal"]
        assert_true("!" in goal0 or "∀" in goal0,
                    f"pre-tactic goal still has quantifier ({goal0!r})")
    finally:
        c.close()


def test_goalState_cache_invalidates_on_tactic_edit():
    """Slice E: after editing the tactic body, the goal-state cache
    should invalidate — subsequent queries return the walk against the
    edited tactic, not against the pre-edit cached snapshots."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_invalidate.sml"
        # Initial proof: gen_tac >> rw[] — after gen_tac the quantifier
        # is stripped.
        v1 = ("Theory goalstate_invalidate\n"
              "Ancestors arithmetic\n\n"
              "Theorem t:\n"
              "  !n:num. n + 0 = n\n"
              "Proof\n"
              "  gen_tac >> rw[]\n"
              "QED\n")
        _did_open(c, uri, v1, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "v1 compileCompleted")
        # Query cursor past `>>` on rw[] — state = post gen_tac.
        r1 = _send_goalstate(c, 701, uri, 6, 15)
        goal1 = r1["result"]["goals"][0]["goal"]
        assert_true("!" not in goal1 and "∀" not in goal1,
                    f"v1 step 1 is post-gen_tac ({goal1!r})")
        # Replace `gen_tac >> rw[]` with just `rw[]`.  Now step 0 is
        # rw[]; cursor at the same position sits inside/past rw[].
        v2 = v1.replace("  gen_tac >> rw[]\n", "  rw[]\n")
        idx_before = c.total_msgs()
        _did_change_full(c, uri, v2, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx_before),
                    "v2 compileCompleted")
        # Cursor on rw[] in the edited version; its pre-state has the
        # full ∀-goal (no gen_tac ran to strip the binder).
        r2 = _send_goalstate(c, 702, uri, 6, 2)
        goal2 = r2["result"]["goals"][0]["goal"]
        assert_true("!" in goal2 or "∀" in goal2,
                    f"v2 pre-rw shows the original quantified goal, "
                    f"not the stale post-gen_tac state ({goal2!r})")
    finally:
        c.close()


def test_goalState_cache_invalidates_on_upstream_change():
    """Slice E: editing an UPSTREAM definition (not the theorem's own
    tactic body) still invalidates the cache — the compile-driven
    `resetForCompile` hook clears the cache, so the next query walks
    against the new HOL Context.  Without that clearing, the theorem's
    unchanged tacText would let the stale post-unfold state stand."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/upstream_change.sml"
        v1 = ("Theory upstream_change\n"
              "Ancestors arithmetic\n\n"
              "Definition foo_def:\n"
              "  foo (n:num) = n + 1\n"
              "End\n\n"
              "Theorem t:\n"
              "  foo 0 = 1\n"
              "Proof\n"
              "  rw[foo_def]\n"
              "QED\n")
        _did_open(c, uri, v1, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "v1 compileCompleted")
        # Line 10 = `  rw[foo_def]`; cursor at char 13 (past the
        # closing bracket) → state AFTER rw runs.  v1: rw unfolds to
        # `0 + 1 = 1`, closes the goal.
        r1 = _send_goalstate(c, 811, uri, 10, 13)
        pretty1 = r1["result"]["pretty"]
        # Change ONLY foo_def's body — not the theorem's tacText.
        v2 = v1.replace("foo (n:num) = n + 1", "foo (n:num) = n + 999")
        idx_before = c.total_msgs()
        _did_change_full(c, uri, v2, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx_before),
                    "v2 compileCompleted")
        r2 = _send_goalstate(c, 812, uri, 10, 13)
        pretty2 = r2["result"]["pretty"]
        # v1's rw closes the goal (`0 + 1 = 1`); v2's leaves it open
        # (`0 + 999 = 1`).  A stale cache would show v1's closed state
        # for the v2 query.
        assert_true(pretty1 != pretty2,
                    f"pretty differs after upstream change\n"
                    f"v1: {pretty1!r}\nv2: {pretty2!r}")
    finally:
        c.close()


def test_goalState_cache_preserved_when_edit_is_downstream():
    """Slice E: editing content AFTER a theorem should not invalidate
    that theorem's cache.  The partial-invalidate logic keyed on
    `minEditOffset` keeps entries whose theoremStart is before the
    edit.  We verify by comparing the goalState response before and
    after a downstream-only edit — both should succeed and produce
    the same goal-state text."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/downstream_edit.sml"
        v1 = ("Theory downstream_edit\n"
              "Ancestors arithmetic\n\n"
              "Theorem t:\n"
              "  !n:num. n + 0 = n\n"
              "Proof\n"
              "  gen_tac >> rw[]\n"
              "QED\n\n"
              "val downstream = 1\n")
        _did_open(c, uri, v1, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "v1 compileCompleted")
        r1 = _send_goalstate(c, 821, uri, 6, 15)  # after gen_tac
        pretty1 = r1["result"]["pretty"]
        # Change only content AFTER t — the theorem's dec is untouched.
        v2 = v1.replace("val downstream = 1\n", "val downstream = 42\n")
        idx_before = c.total_msgs()
        _did_change_full(c, uri, v2, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx_before),
                    "v2 compileCompleted")
        r2 = _send_goalstate(c, 822, uri, 6, 15)
        pretty2 = r2["result"]["pretty"]
        assert_eq(pretty1, pretty2,
                  "downstream edit leaves the theorem's goal state "
                  "unchanged")
    finally:
        c.close()


def test_goalState_case_split_produces_two_subgoals():
    """Slice D: after `Cases_on \\`p\\``, the goalstate should have two
    subgoals — one with `p` as an assumption, one with `¬p`.  The tactic
    source contains raw HOL backticks; TacticWalker.compileTactic must
    pass those through the quotation filter before feeding to
    PolyML.compiler, else the compile fails and the walker halts."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_cases_on.sml"
        src = ("Theory goalstate_cases_on\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n < 5 ==> n + 0 = n\n"
               "Proof\n"
               "  REPEAT GEN_TAC THEN STRIP_TAC THEN\n"
               "  Cases_on `n = 0` THEN\n"
               "  simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 7 char 22 = the `N` of `THEN` immediately after
        # `Cases_on \`n = 0\``.
        r = _send_goalstate(c, 601, uri, 7, 22)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        goals = result.get("goals", [])
        assert_eq(len(goals), 2, f"two subgoals after Cases_on ({goals!r})")
        asms_flat = [a for g in goals for a in g.get("asms", [])]
        assert_true(any("n = 0" in a for a in asms_flat),
                    f"one branch has n = 0 ({asms_flat!r})")
        assert_true(any("n ≠ 0" in a or "n <> 0" in a
                        or "~(n = 0)" in a for a in asms_flat),
                    f"other branch has ¬(n = 0) ({asms_flat!r})")
    finally:
        c.close()


def test_goalState_walks_double_backslash_in_then1_block():
    """`\\\\` (Tactical alias for `THEN`) inside a `>-` block must
    split the walker's step stream so a cursor between the inner
    tactics advances past what came before, not halts at the pre-
    block state."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_bslash.sml"
        # Line 7 is `  >- (ALL_TAC \\\\ ACCEPT_TAC TRUTH)`.  In the
        # buffer that becomes `  >- (ALL_TAC \\ ACCEPT_TAC TRUTH)`.
        src = ("Theory goalstate_bslash\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  T /\\ !n:num. n = n\n"
               "Proof\n"
               "  CONJ_TAC\n"
               "  >- (ALL_TAC \\\\ ACCEPT_TAC TRUTH)\n"
               "  >> gen_tac >> REFL_TAC\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at line 7 char 13 = right after `ALL_TAC `, before
        # the `\\\\`.  Post-TacticParse the walker treats `\\\\` as
        # a THEN-chain separator and descends into the `>-` block:
        # CONJ_TAC ran, then focus flipped to the first subgoal
        # `T` for the >- branch, then ALL_TAC (semantic no-op).
        # What we're testing: the walker got INTO the >- block and
        # focused a single subgoal — proves the `\\\\` chain
        # split.  (Without the fix the whole >- block was opaque
        # and the walker halted at the pre-CONJ_TAC state showing
        # both conjuncts.)
        r = _send_goalstate(c, 501, uri, 7, 13)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        goals = result["goals"]
        assert_true(len(goals) == 1 and goals[0]["goal"] == "T",
                    f"walker split the `\\\\` chain and focused `T`, "
                    f"got {result!r}")
    finally:
        c.close()


def test_goalState_walks_thenl_branches():
    """Regression: cursor inside a specific branch of a `THENL [b1,
    b2, b3]` (or `>|` alias) list must resolve to the state that
    focuses that branch's subgoal.  Before this the walker treated
    the whole `[b1, …, bn]` as one opaque ExpandList and any cursor
    inside halted at the post-left state, hiding the sub-branch
    state entirely."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_thenl.sml"
        #  0 Theory ...
        #  1 Ancestors ...
        #  2
        #  3 Theorem t:
        #  4   T /\ (!n:num. n = n) /\ (0 < 1)
        #  5 Proof
        #  6   REPEAT CONJ_TAC THENL [
        #  7     ACCEPT_TAC TRUTH,
        #  8     gen_tac >> REFL_TAC,
        #  9     SIMP_TAC arith_ss []
        # 10   ]
        # 11 QED
        src = ("Theory goalstate_thenl\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  T /\\ (!n:num. n = n) /\\ (0 < 1)\n"
               "Proof\n"
               "  REPEAT CONJ_TAC THENL [\n"
               "    ACCEPT_TAC TRUTH,\n"
               "    gen_tac >> REFL_TAC,\n"
               "    SIMP_TAC arith_ss []\n"
               "  ]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at line 8 char 15 = start of `REFL_TAC`.  With the
        # fix the walker enters the THENL list, completes branch 1
        # (ACCEPT_TAC TRUTH), advances to branch 2's subgoal
        # (`!n:num. n = n`), applies `gen_tac`, and halts before
        # REFL_TAC.  The current goal is `n = n` (quantifier gone).
        r = _send_goalstate(c, 701, uri, 8, 15)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        goals = result.get("goals", [])
        assert_eq(len(goals), 1,
                  f"THENL focuses the current branch's subgoal "
                  f"({goals!r})")
        goal = goals[0].get("goal", "")
        assert_true("n = n" in goal,
                    f"branch 2's subgoal after gen_tac is n = n "
                    f"({goal!r})")
        assert_true("!" not in goal and "∀" not in goal,
                    f"quantifier stripped by gen_tac ({goal!r})")
    finally:
        c.close()


def test_goalState_thenl_context_line():
    """When the walker's state is inside a `THENL` branch (Stashed
    with a TacsToLT wrapper), `pp_goalstate` must surface which
    branch the cursor is in via a `[branch k of n of THENL]`
    context line -- otherwise the focused subgoal appears without
    any indication that the previous branches are done."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_thenl_ctx.sml"
        src = ("Theory goalstate_thenl_ctx\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  T /\\ (!n:num. n = n) /\\ (0 < 1)\n"
               "Proof\n"
               "  REPEAT CONJ_TAC THENL [\n"
               "    ACCEPT_TAC TRUTH,\n"
               "    gen_tac >> REFL_TAC,\n"
               "    SIMP_TAC arith_ss []\n"
               "  ]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 8 char 4 = start of branch 2's `gen_tac`.  Walker has
        # just applied NextTacsToLT and focused on branch 2.
        r = _send_goalstate(c, 811, uri, 8, 4)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        pretty = result.get("pretty", "")
        assert_true("[branch 2 of 3 of THENL]" in pretty,
                    f"expected [branch 2 of 3 of THENL] context, "
                    f"got: {pretty!r}")
        # Line 9 char 4 = start of branch 3's `SIMP_TAC`.
        r = _send_goalstate(c, 812, uri, 9, 4)
        pretty = r.get("result", {}).get("pretty", "")
        assert_true("[branch 3 of 3 of THENL]" in pretty,
                    f"expected [branch 3 of 3 of THENL] context, "
                    f"got: {pretty!r}")
    finally:
        c.close()


def test_diagnostics_deduplicated_across_publish():
    """A partial tactic body often triggers multiple parser recovery
    passes that each emit the same "expected 'QED'" / "expected an
    expression" pair.  Deduplicate before publishing so the client
    sees each (range, message) once."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/dedup.sml"
        # `simp[` with no closing bracket produces multiple duplicated
        # "expected an expression" / "expected 'QED'" reports pre-dedup.
        src = ("Theory dedup\nAncestors bool\n\nTheorem foo:\n  T\n"
               "Proof\n  simp[")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        diags = _diag_count(c, uri)
        keys = [(d["range"]["start"]["line"],
                 d["range"]["start"]["character"],
                 d["range"]["end"]["line"],
                 d["range"]["end"]["character"],
                 d["message"]) for d in diags]
        assert_eq(len(keys), len(set(keys)),
                  f"diagnostics deduplicated by (range, message): {keys!r}")
    finally:
        c.close()


def test_unclosed_quotation_narrows_to_opening_delimiter():
    """An unclosed HOL quotation at EOF reports a point diagnostic
    at the opening delimiter, not a range spanning to EOF."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/unclosed.sml"
        src = ("Theory unclosed\n"
               "Ancestors bool\n\n"
               "Definition foo:\n"
               "  foo x = x /\\ x\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        diags = _diag_count(c, uri)
        unclosed = [d for d in diags
                    if "unclosed quotation" in d.get("message", "")]
        assert_eq(len(unclosed), 1, f"one unclosed-quotation diag ({diags!r})")
        rng = unclosed[0]["range"]
        assert_true(rng["end"]["line"] == rng["start"]["line"] and
                    rng["end"]["character"] - rng["start"]["character"] <= 2,
                    f"unclosed-quotation range is narrow: {rng!r}")
    finally:
        c.close()


def _diag_spans_at_most(d, n_lines):
    return d["range"]["end"]["line"] - d["range"]["start"]["line"] <= n_lines


def test_incomplete_definition_mid_file_stays_narrow():
    """Inserting a fresh `Definition` block mid-file, still typing the
    RHS with no `End` yet, must NOT paint the entire in-progress
    fragment red — the diagnostic must be narrow, and the following
    valid Theorem must still parse and compile normally."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/incomplete_def_midfile.sml"
        # `Definition foo:` never reaches `End`; the following
        # `Theorem after:` must still be recognised as a fresh decl
        # rather than swallowed by the unclosed quotation.
        src = ("Theory incomplete_def_midfile\n"
               "Ancestors bool\n\n"
               "Definition foo:\n"
               "  foo x = x /\\ x\n"
               "  /\\ x\n"
               "\n"
               "Theorem after:\n"
               "  T\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        diags = _diag_count(c, uri)
        wide = [d for d in diags if not _diag_spans_at_most(d, 1)]
        assert_eq(wide, [],
                  f"no diagnostic spans multiple lines: "
                  f"{[(d['range'], d.get('message','')[:60]) for d in wide]!r}")
        for d in diags:
            # Any leak of "Theorem after" text into a diagnostic
            # would signal the quotation swallowed the next decl.
            assert_true("Theorem after" not in d.get("message", ""),
                        f"'Theorem after' didn't leak into a diag: "
                        f"{d.get('message','')[:80]!r}")
    finally:
        c.close()


def test_incomplete_theorem_statement_mid_file_stays_narrow():
    """A Theorem being written mid-file, statement quotation still
    open, must not paint the whole in-progress block red -- and the
    following valid decl must still compile."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/incomplete_thm_stmt_midfile.sml"
        src = ("Theory incomplete_thm_stmt_midfile\n"
               "Ancestors bool\n\n"
               "Theorem in_progress[simp]:\n"
               "  !x. x /\\ T = x\n"
               "\n"
               "Theorem after:\n"
               "  T\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        diags = _diag_count(c, uri)
        wide = [d for d in diags if not _diag_spans_at_most(d, 1)]
        assert_eq(wide, [],
                  f"no diagnostic spans multiple lines: "
                  f"{[(d['range'], d.get('message','')[:60]) for d in wide]!r}")
    finally:
        c.close()


def test_incomplete_proof_body_mid_file_stays_narrow():
    """A Proof body being typed mid-file (no QED yet), followed by
    a valid Theorem below, must not get a wide type-error squiggle
    over the whole `Proof … <next>` fragment: e.g. a bare
    `Induct_on` still waiting for its `` `t` `` argument used to
    fire a wrapping-type error across the entire Proof block."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/incomplete_proof_midfile.sml"
        src = ("Theory incomplete_proof_midfile\n"
               "Ancestors arithmetic\n\n"
               "Theorem sm:\n"
               "  !n. n + 0 = n\n"
               "Proof\n"
               "  Induct_on\n"
               "\n"
               "Theorem after:\n"
               "  T\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        diags = _diag_count(c, uri)
        wide = [d for d in diags if not _diag_spans_at_most(d, 1)]
        assert_eq(wide, [],
                  f"no diagnostic spans multiple lines: "
                  f"{[(d['range'], d.get('message','')[:60]) for d in wide]!r}")
        # The wrapping type error from `Q.store_thm (..., wrapTac Induct_on)`
        # would mention `Type error` / `Can't unify` -- prove those are gone.
        type_errs = [d for d in diags
                     if "Type error" in d.get("message", "")
                     or "Can't unify" in d.get("message", "")]
        assert_eq(type_errs, [],
                  f"no wide Q.store_thm wrapping type error: "
                  f"{[d.get('message','')[:80] for d in type_errs]!r}")
    finally:
        c.close()


def test_goalState_available_past_compile_pos():
    """A `$/hol/goalState' issued between a didChange and the fresh
    compile finishing must still return a valid result -- otherwise
    the auto-follow-cursor pane goes stale for the 300 ms debounce."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goal_past_compile.sml"
        base = ("Theory goal_past_compile\n"
                "Ancestors bool\n\n"
                "Theorem thm:\n"
                "  T\n"
                "Proof\n"
                "  ACCEPT_TAC TRUTH\n"
                "QED\n")
        _did_open(c, uri, base, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        idx = c.total_msgs()
        new_text = base.replace("ACCEPT_TAC TRUTH",
                                "ACCEPT_TAC TRUTH >> ALL_TAC")
        _did_change_full(c, uri, new_text, 2)
        # Query goalState IMMEDIATELY (mid-debounce, before compile
        # has had a chance to run).
        r = _send_goalstate(c, 501, uri, 6, 30)
        result = r.get("result")
        assert_true(result is not None,
                    f"goalState available past compile pos ({r!r})")
        # Assumes step != None; the walker walked the current buffer.
        assert_true(result.get("step") is not None,
                    f"got a step count ({result!r})")
    finally:
        c.close()


def test_stale_diags_dont_survive_char_by_char_typing():
    """A HOL Theory declaration expands to multiple SML decs at the
    same source-byte position (`Theory.new_theory <name>` plus
    `Parse.set_grammar_ancestry ...`).  When the user types the
    declaration character-by-character, intermediate states like
    `Theory ` (no name yet) fail on the first expanded dec but
    the second, being an inert grammar-setup call, doesn't add
    new errors -- so the resume-snapshot machinery used to
    capture a snapshot whose frozen `diags' embedded the earlier
    dec's error.  Every subsequent didChange resumed from that
    snapshot and inherited the error, even once the user finished
    typing a valid name.

    Regression: type `Theory foo` one character at a time and
    assert the final state carries no stale diagnostics."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/stale_theory.sml"
        _did_open(c, uri, "", 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c0")
        text = ""
        for ch in "Theory foo":
            idx = c.total_msgs()
            _did_change_incr(c, uri, text, len(text), len(text), ch,
                             len(text) + 2)
            text = text + ch
            assert_true(c.wait_for_method("$/compileCompleted", 30, idx),
                        f"after typing {ch!r}")
        with c.msgs_lock:
            pubs = [m for m in c.msgs
                    if m.get("method") == "textDocument/publishDiagnostics"
                    and m["params"].get("uri") == uri]
        final = pubs[-1]["params"]["diagnostics"] if pubs else []
        stale = [d for d in final
                 if "proposed theory name" in d.get("message", "")
                 or "expected identifier" in d.get("message", "")]
        assert_eq(stale, [],
                  f"no stale theory-name errors after 'Theory foo': "
                  f"{[d.get('message','')[:60] for d in final]!r}")
    finally:
        c.close()


def test_runaway_errors_still_publish_diagnostics():
    """When a single dec produces the runOfErrorsLimit's worth of
    errors and the compile is force-interrupted, the accumulated
    diagnostics used to be stranded in `trees.diags' -- Progress
    fired only at dec boundaries, and no boundary was reached
    before the abort.  The client kept whatever diagnostics were
    current before the edit and saw nothing new despite the file
    being obviously broken.

    Regression: paste in a syntactically-catastrophic tail (an
    unbalanced HOL-quote closer that turns the rest of the file
    into orphan SML) and assert several diagnostics land."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/runaway_errors.sml"

        def latest():
            with c.msgs_lock:
                pubs = [m for m in c.msgs
                        if m.get("method") == "textDocument/publishDiagnostics"
                        and m["params"].get("uri") == uri]
            return pubs[-1]["params"]["diagnostics"] if pubs else None

        base = ("Theory runaway_errors\n"
                "Ancestors bool\n\n"
                "val s1 = “(p:bool)”\n")
        _did_open(c, uri, base, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted baseline")
        assert_eq(len(latest() or []), 0, "baseline: no diags")

        # Inject a stray U+201D right after the opening U+201C, then
        # follow with several lines of orphan SML.
        idx = c.total_msgs()
        broken = ("Theory runaway_errors\n"
                  "Ancestors bool\n\n"
                  "val s1 = “”(p:bool)”\n"
                  "val s2 = 1 + 2 + this + is + all + broken + now\n"
                  "val s3 = another + broken + line + here\n"
                  "val s4 = yet + more + garbage + expressions\n")
        _did_change_full(c, uri, broken, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx),
                    "compileCompleted after break")
        diags = latest() or []
        assert_true(len(diags) >= 3,
                    f"broken tail produces multiple diagnostics, "
                    f"got {len(diags)}: {[d.get('message','')[:40] for d in diags]!r}")
    finally:
        c.close()


def test_stale_diagnostic_from_partial_parse_clears_on_completion():
    """A dec that fails to parse partway through user typing (e.g. a
    `Theorem foo` with no body yet, or an unfinished `Anc...` line)
    used to leave its diagnostic sticky: the resume snapshot at its
    endByte carried the frozen error forward, and later compiles
    seeded `trees.diags' with it -- no matter how the user completed
    the dec.  Fix: don't snapshot decs that added diagnostics during
    their own compile; a fresh recompile falls back to the previous
    good snapshot (or the file start) and re-parses from scratch."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/stale_partial.sml"

        def latest_diags():
            with c.msgs_lock:
                pubs = [m for m in c.msgs
                        if m.get("method") == "textDocument/publishDiagnostics"
                        and m["params"].get("uri") == uri]
            return pubs[-1]["params"]["diagnostics"] if pubs else None

        # --- Case A: partial `Anc` then complete to `Ancestors hol`. ---
        _did_open(c, uri, "Theory qux\n", 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30), "c1")
        idx = c.total_msgs()
        _did_change_full(c, uri, "Theory qux\nAnc\n", 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx), "c2")
        d2 = latest_diags() or []
        assert_true(any("Anc" in d.get("message", "") for d in d2),
                    f"partial Anc emits a diagnostic ({d2!r})")
        idx = c.total_msgs()
        _did_change_full(c, uri, "Theory qux\nAncestors hol\n", 3)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx), "c3")
        d3 = latest_diags() or []
        assert_true(not any("Anc" in d.get("message", "") for d in d3),
                    f"Anc diagnostic clears once Ancestors hol is typed "
                    f"({d3!r})")

        # --- Case B: partial `Theorem foo` then Proof/QED. ---
        idx = c.total_msgs()
        _did_change_full(c, uri,
                          "Theory qux\nAncestors bool\nTheorem foo\n", 4)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx), "c4")
        d4 = latest_diags() or []
        assert_true(any("missing body" in d.get("message", "") for d in d4),
                    f"partial Theorem emits missing-body diagnostic ({d4!r})")
        idx = c.total_msgs()
        _did_change_full(
            c, uri,
            "Theory qux\nAncestors bool\n"
            "Theorem foo:\n  T\nProof\n  ACCEPT_TAC TRUTH\nQED\n", 5)
        assert_true(c.wait_for_method("$/compileCompleted", 30, idx), "c5")
        d5 = latest_diags() or []
        assert_true(not any("missing body" in d.get("message", "")
                            for d in d5),
                    f"missing-body diagnostic clears once Theorem completes "
                    f"({d5!r})")
    finally:
        c.close()


def test_goalState_failed_tactic_publishes_diagnostic():
    """After a walker query that halts at a failed tactic, the server
    must publish a `textDocument/publishDiagnostics` covering the
    failed leaf's file range — so the client renders a runtime
    squiggle in addition to the ⚠ message in the goals pane.  On a
    subsequent didChange that fixes the tactic + a re-query, the
    diagnostic is cleared."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_squiggle.sml"
        src_broken = ("Theory goalstate_squiggle\n"
                      "Ancestors bool\n\n"
                      "Theorem bar: !p:bool. p /\\ q ==> r\n"
                      "Proof\n"
                      "  ACCEPT_TAC TRUTH\n"
                      "QED\n")
        _did_open(c, uri, src_broken, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted 1")
        idx_before_query = c.total_msgs()
        r = _send_goalstate(c, 3001, uri, 5, 18)
        assert_true(r.get("result") is not None, f"got response ({r!r})")
        # A publishDiagnostics arrives after the walker updates
        # walkerDiags; wait briefly.
        assert_true(c.wait_for_method("textDocument/publishDiagnostics",
                                       5, idx_before_query),
                    "walker publish after query")
        msgs, _ = c.messages_since(0)
        latest = None
        for m in msgs[idx_before_query:]:
            if m.get("method") == "textDocument/publishDiagnostics" \
               and m["params"]["uri"] == uri:
                latest = m["params"]["diagnostics"]
        assert_true(latest is not None, "have walker diagnostics")
        # Expect one runtime squiggle naming the failed tactic.
        matched = [d for d in latest
                   if "ACCEPT_TAC TRUTH" in d.get("message", "")]
        assert_eq(len(matched), 1,
                  f"one walker diagnostic for the failed tactic, "
                  f"got: {latest!r}")
        # Fix the proof (goal has no free vars now).  didChange +
        # compileCompleted invalidates walkerDiags; re-query and
        # confirm the diag is gone.
        src_fixed = ("Theory goalstate_squiggle\n"
                     "Ancestors bool\n\n"
                     "Theorem bar: T\n"
                     "Proof\n"
                     "  ACCEPT_TAC TRUTH\n"
                     "QED\n")
        idx_before_change = c.total_msgs()
        _did_change_full(c, uri, src_fixed, 2)
        assert_true(c.wait_for_method("$/compileCompleted", 30,
                                       idx_before_change),
                    "compileCompleted 2")
        idx_before_requery = c.total_msgs()
        r = _send_goalstate(c, 3002, uri, 5, 18)
        assert_true(r.get("result") is not None,
                    f"got response 2 ({r!r})")
        msgs, _ = c.messages_since(0)
        latest2 = None
        for m in msgs:
            if m.get("method") == "textDocument/publishDiagnostics" \
               and m["params"]["uri"] == uri \
               and m["params"].get("version") == 2:
                latest2 = m["params"]["diagnostics"]
        matched2 = [d for d in (latest2 or [])
                    if "ACCEPT_TAC TRUTH" in d.get("message", "")]
        assert_eq(len(matched2), 0,
                  f"walker diagnostic cleared after fix, got: {latest2!r}")
    finally:
        c.close()


def test_goalState_failed_tactic_signals_error():
    """When the walker halts because a tactic didn't apply -- the
    tactic compiled but its `goalFrag.expand` raised, or the tactic
    source didn't compile at all -- the response must set `error`
    naming the failed leaf.  Otherwise the pre-step state is shown
    with no indication anything went wrong, implying the tactic
    ran and did nothing.

    `bar`'s goal has free `q` and `r`, so `ACCEPT_TAC TRUTH` can't
    unify `TRUTH : |- T` against `∀p. p ∧ q ⇒ r` and the walker
    halts at that leaf."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_fail.sml"
        src = ("Theory goalstate_fail\n"
               "Ancestors bool\n\n"
               "Theorem bar: !p:bool. p /\\ q ==> r\n"
               "Proof\n"
               "  ACCEPT_TAC TRUTH\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 5 char 18 = just past `TRUTH`.  Walker has attempted
        # `ACCEPT_TAC TRUTH`, it failed, walker halted with pre-
        # step state + error.
        r = _send_goalstate(c, 1101, uri, 5, 18)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        err = result.get("error")
        assert_true(err is not None and "failed" in err.lower(),
                    f"error field names the failed leaf: {err!r}")
        assert_true("ACCEPT_TAC TRUTH" in (err or ""),
                    f"error names the specific tactic: {err!r}")
        pretty = result.get("pretty", "")
        assert_true("p" in pretty and "q" in pretty and "r" in pretty,
                    f"pre-fail state still visible: {pretty!r}")
    finally:
        c.close()


def test_goalState_focused_subgoal_solved_between_close_and_outer():
    """When the cursor sits between a solved subgoal's last tactic
    and the paren-close that ends its `>-` block, the walker's state
    has `top_goals = []` but the outer combinator hasn't yet closed.
    Before: pp_goalstate reported "No subgoals but proof incomplete"
    — misleading, since the current focus has been solved and only
    the mechanical close remains.  After: pp_goalstate simulates the
    close and shows the state that will be current once the outer
    combinator finalises."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_then1_paren.sml"
        src = ("Theory goalstate_then1_paren\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. (n = n) /\\ (0 < 1)\n"
               "Proof\n"
               "  gen_tac THEN CONJ_TAC THEN1\n"
               "   (REFL_TAC) THEN\n"
               "  SIMP_TAC arith_ss []\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 7 char 12 = at the `)` closing the THEN1 branch.
        # First subgoal solved; the >- combinator still open.
        r = _send_goalstate(c, 901, uri, 7, 12)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        pretty = result.get("pretty", "")
        assert_true("No subgoals but proof incomplete" not in pretty,
                    f"NOT the stale close-pending message: {pretty!r}")
        assert_true("Focused subgoal(s) solved" in pretty,
                    f"clearer solved message: {pretty!r}")
        assert_true("0 < 1" in pretty,
                    f"remaining subgoal visible: {pretty!r}")
    finally:
        c.close()


def test_goalState_thenl_end_shows_proved():
    """When the cursor sits after the last branch of a `THENL` list
    (all branches applied, close_paren pending), `pp_goalstate` must
    show "Initial goal proved." rather than "No subgoals but proof
    incomplete."  Regression for goalFrag.close_paren's TacsToLT
    case, which used to discard the final branch's result and leave
    the outer validation with n-1 theorems for n branches."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_thenl_end.sml"
        src = ("Theory goalstate_thenl_end\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  T /\\ (!n:num. n = n) /\\ (0 < 1)\n"
               "Proof\n"
               "  REPEAT CONJ_TAC THENL [\n"
               "    ACCEPT_TAC TRUTH,\n"
               "    gen_tac >> REFL_TAC,\n"
               "    SIMP_TAC arith_ss []\n"
               "  ]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 9 char 24 = right after `SIMP_TAC arith_ss []`, before
        # the newline.  All three branches have applied; close_paren
        # is the only remaining step.  Expect a proved-goal message.
        r = _send_goalstate(c, 801, uri, 9, 24)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        pretty = result.get("pretty", "")
        assert_true("Initial goal proved" in pretty,
                    f"cursor after last branch shows proved-message, "
                    f"got: {pretty!r}")
        assert_true("No subgoals but proof incomplete" not in pretty,
                    f"NOT the stale close_paren-failed message: "
                    f"{pretty!r}")
    finally:
        c.close()


def test_goalState_walks_squiggle_selector():
    """Regression: `>~` (Q.>~, a goal-selector by pattern) must
    split the walker's step stream so cursor between the LHS
    tactic and the `>~ pats` selector sees the post-LHS state.
    Without this split, the whole `left >~ pats` compiled as one
    atomic Expand and any cursor inside halted the walker at the
    pre-`left` state.

    The right operand of `>~` is a term-quote list, not a tactic,
    so the walker synthesises `ALL_TAC >~ pats` at apply time."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_squiggle.sml"
        #  0 Theory ...
        #  1 Ancestors ...
        #  2
        #  3 Theorem t:
        #  4   !n:num. n = 0 \/ 0 < n
        #  5 Proof
        #  6   gen_tac >> Cases_on `n`
        #  7   >~ [`SUC m`] >- rw[]
        #  8   >~ [`0`] >- rw[]
        #  9 QED
        src = ("Theory goalstate_squiggle\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n = 0 \\/ 0 < n\n"
               "Proof\n"
               "  gen_tac >> Cases_on `n`\n"
               "  >~ [`SUC m`] >- rw[]\n"
               "  >~ [`0`] >- rw[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at line 6 char 25 = just past `Cases_on ` \`n\``, before
        # the newline.  With the fix the walker treats `>~` as a
        # splitter and the step count is >= 2 (gen_tac + Cases_on).
        r = _send_goalstate(c, 601, uri, 6, 25)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        step = result.get("step")
        assert_true(step >= 2,
                    f"walker advanced past Cases_on, before >~; "
                    f"got step {step} ({result!r})")
    finally:
        c.close()


def test_goalState_walks_into_by_block():
    """`‘g’ by (tac1 >> tac2)` compiles to `ThenLT(Subgoal, [LThen1
    tac1 >> tac2])`; the walker steps into the RHS so a cursor
    between tac1 and tac2 advances past the subgoal + tac1."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_by_block.sml"
        #  0 Theory goalstate_by_block
        #  1 Ancestors arithmetic
        #  2
        #  3 Theorem t:
        #  4   !n:num. n + 0 = n
        #  5 Proof
        #  6   gen_tac >> `n = n` by (ALL_TAC >> ACCEPT_TAC (REFL n))
        #  7   >> simp[]
        #  8 QED
        src = ("Theory goalstate_by_block\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  gen_tac >> `n = n` by (ALL_TAC >> ACCEPT_TAC (REFL n))\n"
               "  >> simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at line 6 char 34: right after `ALL_TAC `, inside the
        # `by (…)` block.  Post-fix the walker has descended into the
        # `by` RHS.  ALL_TAC is a semantic no-op under TacticParse
        # (`Then []`) so it doesn't advance the step count; what
        # matters is the goal-state — cursor should sit on the
        # freshly-introduced subgoal `n = n`, not on the outer goal.
        r = _send_goalstate(c, 701, uri, 6, 34)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        goals = result["goals"]
        assert_true(len(goals) == 1 and goals[0]["goal"] == "n = n",
                    f"walker focused subgoal `n = n` ({result!r})")
    finally:
        c.close()


def test_goalState_walks_into_suffices_by_block():
    """`‘g’ suffices_by tac` compiles to
    `ThenLT(Group(ThenLT(Subgoal,[LReverse])), [LThen1 tac])` — the
    walker steps into the tac RHS."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_suffices_by.sml"
        #  0 Theory goalstate_suffices_by
        #  1 Ancestors arithmetic
        #  2
        #  3 Theorem t:
        #  4   !n:num. n + 0 = n
        #  5 Proof
        #  6   gen_tac >> `n = n + 0` suffices_by (ALL_TAC >> simp[])
        #  7 QED
        src = ("Theory goalstate_suffices_by\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  gen_tac >> `n = n + 0` suffices_by (ALL_TAC >> simp[])\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at line 6 char 43: right after `ALL_TAC `, inside the
        # `suffices_by (…)` block.  Focus should be on the sufficient
        # goal (`n = n + 0`) with the original `n + 0 = n` sitting
        # below as the assumption-holder subgoal.
        r = _send_goalstate(c, 702, uri, 6, 43)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        goals = result["goals"]
        assert_true(len(goals) >= 1 and goals[0]["goal"] == "n = n + 0",
                    f"walker focused sufficient goal ({result!r})")
    finally:
        c.close()


def test_goalState_walks_into_select_goal_block():
    """`>~ [pat]` (LSelectGoal) narrows focus to a matching subgoal;
    the walker steps into the tactic sequence that follows.  Before
    the fix, the walker synthesised `ALL_TAC >~ [pat]` at apply
    time, which would fail when the current focus didn't hold a
    matching goal (see fibonacciScript.sml's `>~
    [‘fibloop _ _ i i = fib i’]` where the false-positive `Selector
    ALL_TAC >~ ...` error came from)."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_select_block.sml"
        src = ("Theory goalstate_select_block\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n = 0 \\/ 0 < n\n"
               "Proof\n"
               "  gen_tac >> Cases_on `n`\n"
               "  >~ [`SUC m`] >- (ALL_TAC >> rw[])\n"
               "  >~ [`0`] >- rw[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at line 7 char 29: right after `ALL_TAC `, inside
        # the `>~ [`SUC m`] >- (…)` block.  Step should be past
        # gen_tac + Cases_on + SUC-selector + ALL_TAC.
        r = _send_goalstate(c, 703, uri, 7, 29)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        step = result.get("step")
        assert_true(step >= 3,
                    f"walker stepped into select-goal block, "
                    f"got step {step} ({result!r})")
    finally:
        c.close()


def test_goalState_walks_map_every():
    """`MAP_EVERY f [a, b]` is a single `MapEvery` atom annotated with
    the span of `f` alone — the head token `MAP_EVERY` and the argument
    list sit outside every recorded span, so `topSpan` is NONE and the
    walker used to return `Failed` here ("Structural leaf failed"),
    freezing the goal for the whole rest of the proof.  It now falls
    back on `TacticParse.printTacAsSML` to rebuild the surface call.

    Pinned against the real `integerScript.sml` (INT_LE_MUL, line 961)
    because that is where the bug was found."""
    src = f"{REPO}/src/integer/integerScript.sml"
    c = Client(os.path.dirname(src))
    try:
        _init(c, REPO)
        uri = f"file://{src}"
        with open(src, encoding="utf8") as f: text = f.read()
        _did_open(c, uri, text)
        assert_true(c.wait_for_method("$/compileCompleted", 60),
                    "compileCompleted")
        lines = text.split("\n")
        # 0-based 960 is `MAP_EVERY ASM_CASES_TAC [Term `0i = x`, …]`
        assert_true("MAP_EVERY ASM_CASES_TAC" in lines[960],
                    f"line 960 still holds the MAP_EVERY ({lines[960]!r})")
        # Cursor on `MAP_EVERY` itself: halted before the atom, so this
        # is the state the MAP_EVERY is about to act on.
        before = _send_goalstate(c, 710, uri, 960, 10).get("result")
        assert_true(before is not None, "goal state before MAP_EVERY")
        assert_eq(before.get("error"), None, "no error before MAP_EVERY")
        # Cursor inside the argument list (char 45; `ASM_CASES_TAC` ends
        # at 32).  The atom is annotated with the mapped function's span
        # alone, so without the atomEndByte fix this counts as past the
        # atom and fires it early.
        inarg = _send_goalstate(c, 711, uri, 960, 45).get("result")
        assert_true(inarg is not None, "goal state inside the arg list")
        assert_eq(inarg.get("error"), None, "no error inside the arg list")
        assert_eq(inarg.get("goals"), before.get("goals"),
                  "cursor in MAP_EVERY's arg list still shows the "
                  "pre-MAP_EVERY goal")
        # Cursor on the following line: MAP_EVERY has fired.
        after = _send_goalstate(c, 712, uri, 961, 10).get("result")
        assert_true(after is not None, "goal state after MAP_EVERY")
        assert_eq(after.get("error"), None,
                  f"MAP_EVERY applied cleanly ({after!r})")
        assert_true(after.get("goals") != before.get("goals"),
                    f"goal advanced past MAP_EVERY ({after!r})")
        # Two ASM_CASES_TAC splits over a single goal.
        assert_eq(len(after.get("goals")), 4,
                  f"two case splits give four subgoals ({after!r})")
        # And the walker reaches the end of the proof without failing
        # anywhere — line 961's `TRY(FIRST_ASSUM(SUBST1_TAC o SYM))`
        # fails on some of the four subgoals, so this also covers TRY
        # absorbing a failure.
        for ln in range(961, 966):
            r = _send_goalstate(c, 713 + ln, uri, ln, 10).get("result")
            assert_true(r is not None, f"goal state on line {ln}")
            assert_eq(r.get("error"), None,
                      f"no walker failure on line {ln} ({r!r})")
    finally:
        c.close()


def test_goalState_walks_map_first():
    """`MAP_FIRST` reaches the walker as a `MapFirst` atom with the
    same NONE-topSpan shape as `MAP_EVERY`."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_map_first.sml"
        #  6   MAP_FIRST (fn t => t) [gen_tac] >>
        #  7   simp[]
        src = ("Theory goalstate_map_first\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !n:num. n + 0 = n\n"
               "Proof\n"
               "  MAP_FIRST (fn t => t) [gen_tac] >>\n"
               "  simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        r = _send_goalstate(c, 714, uri, 7, 2)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        assert_eq(result.get("error"), None,
                  f"MAP_FIRST applied cleanly ({result!r})")
        goals = result["goals"]
        assert_true(len(goals) == 1 and goals[0]["goal"] == "n + 0 = n",
                    f"gen_tac ran under MAP_FIRST ({result!r})")
    finally:
        c.close()


def test_goalState_walks_squiggle_minus_rename():
    """`>>~- ([pat], tac)` elaborates to `LSelectThen (Rename …, …)`.
    The `Rename` atom carries only the pattern's span; the walker
    synthesises `Q.RENAME_TAC` for it — qualified, because plain
    `RENAME_TAC` lives in `Q` and the edited file need not have
    opened it."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_squig_minus.sml"
        #  6   gen_tac >> conj_tac >>~- ([`0 + a = a`], simp[]) >>
        #  7   simp[]
        src = ("Theory goalstate_squig_minus\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !a:num. a + 0 = a /\\ 0 + a = a\n"
               "Proof\n"
               "  gen_tac >> conj_tac >>~- ([`0 + a = a`], simp[]) >>\n"
               "  simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        r = _send_goalstate(c, 715, uri, 7, 2)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        assert_eq(result.get("error"), None,
                  f"the >>~- block applied cleanly ({result!r})")
    finally:
        c.close()


def test_goalState_try_absorbs_failure():
    """`TRY tac` is `tac ORELSE ALL_TAC`, so `linearize` has to give it
    ORELSE's second, empty branch.  With only `FOpenFirst … FClose` and
    no `FNextFirst`, a failing inner tactic left goalFrag's
    `Try (Failed e, _)` node in place and every closer re-raised it —
    the walker reported "Combinator close failed" and froze the goals
    for the rest of the proof, which is precisely the case TRY is
    written for."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_try_absorbs.sml"
        #  6   gen_tac THEN DISCH_TAC THEN
        #  7   TRY(CONJ_TAC) THEN
        #  8   simp[]
        src = ("Theory goalstate_try_absorbs\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !a:num. 0 < a ==> a + 0 = a\n"
               "Proof\n"
               "  gen_tac THEN DISCH_TAC THEN\n"
               "  TRY(CONJ_TAC) THEN\n"
               "  simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        before = _send_goalstate(c, 716, uri, 7, 2).get("result")
        assert_true(before is not None, "goal state on the TRY")
        after = _send_goalstate(c, 717, uri, 8, 2).get("result")
        assert_true(after is not None, "goal state after the TRY")
        assert_eq(after.get("error"), None,
                  f"CONJ_TAC's failure absorbed by TRY ({after!r})")
        assert_eq(after.get("goals"), before.get("goals"),
                  f"a failing TRY leaves the goals alone ({after!r})")
    finally:
        c.close()


def test_goalState_try_multi_step_branch():
    """`TRY (t1 >> t2)` is the one `FMBracket` producer whose section
    holds a THEN-chain directly rather than a single `Group`, so it is
    what pins `mbracket` reversing each section: with the frags the
    wrong way round CONJ_TAC would run first, fail, and be absorbed,
    leaving one goal instead of two."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_try_multi.sml"
        #  6   gen_tac THEN
        #  7   TRY (DISCH_TAC >> CONJ_TAC) THEN
        #  8   simp[]
        src = ("Theory goalstate_try_multi\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !p:bool. p ==> p /\\ p\n"
               "Proof\n"
               "  gen_tac THEN\n"
               "  TRY (DISCH_TAC >> CONJ_TAC) THEN\n"
               "  simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor between the two branch steps: DISCH_TAC has run.
        mid = _send_goalstate(c, 718, uri, 7, 20).get("result")
        assert_true(mid is not None, "goal state inside the TRY")
        assert_eq(mid.get("error"), None, "no error inside the TRY")
        goals = mid["goals"]
        assert_true(len(goals) == 1 and goals[0]["asms"] == ["p"],
                    f"DISCH_TAC ran first, not CONJ_TAC ({mid!r})")
        after = _send_goalstate(c, 719, uri, 8, 2).get("result")
        assert_true(after is not None, "goal state after the TRY")
        assert_eq(after.get("error"), None, "no error after the TRY")
        assert_eq(len(after["goals"]), 2,
                  f"both branch steps ran, in order ({after!r})")
    finally:
        c.close()


def test_goalState_try_lt_absorbs_failure():
    """`TRY_LT` (`LTry`) had the same missing branch as `TRY`."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_try_lt.sml"
        #  6   gen_tac THEN_LT TRY_LT (ALLGOALS DISCH_TAC) THEN
        #  7   simp[]
        src = ("Theory goalstate_try_lt\n"
               "Ancestors arithmetic\n\n"
               "Theorem t:\n"
               "  !a:num. a + 0 = a\n"
               "Proof\n"
               "  gen_tac THEN_LT TRY_LT (ALLGOALS DISCH_TAC) THEN\n"
               "  simp[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        r = _send_goalstate(c, 720, uri, 7, 2)
        result = r.get("result")
        assert_true(result is not None, f"got a result ({r!r})")
        assert_eq(result.get("error"), None,
                  f"DISCH_TAC's failure absorbed by TRY_LT ({result!r})")
        goals = result["goals"]
        assert_true(len(goals) == 1 and goals[0]["goal"] == "a + 0 = a",
                    f"goals left alone by the failing TRY_LT ({result!r})")
    finally:
        c.close()


def test_lsp_walks_file_includes_from_arbitrary_cwd():
    """When the LSP server is launched with cwd != the opened file's
    directory (as eglot typically does — cwd is the project root),
    the file's Holmakefile INCLUDES chain must still be walked so
    `Meta.loadPath` picks up sibling directories that hold the
    file's `Ancestors` dependencies."""
    root = tempfile.mkdtemp(prefix="lsp_incl_test_")
    lib = os.path.join(root, "lib")
    user = os.path.join(root, "user")
    os.makedirs(lib); os.makedirs(user)
    try:
        # A minimal theory in lib/ — built via Holmake below.
        with open(os.path.join(lib, "myLibScript.sml"), "w") as f:
            f.write("Theory myLib\n"
                    "Definition my_id_def:\n"
                    "  my_id (x:num) = x\n"
                    "End\n")
        r = subprocess.run(
            [f"{REPO}/bin/Holmake", "myLibTheory"],
            cwd=lib, capture_output=True, text=True)
        assert_true(r.returncode == 0,
                    f"Holmake in {lib} succeeded ({r.stderr!r})")
        # user/Holmakefile points at the sibling.
        with open(os.path.join(user, "Holmakefile"), "w") as f:
            f.write("INCLUDES = ../lib\n")
        # user/uses_libScript.sml references myLib via Ancestors.
        user_src = ("Theory uses_lib\n"
                    "Ancestors myLib\n\n"
                    "Theorem noop:\n"
                    "  my_id (n:num) = n\n"
                    "Proof\n"
                    "  simp[my_id_def]\n"
                    "QED\n")
        user_file = os.path.join(user, "uses_libScript.sml")
        with open(user_file, "w") as f:
            f.write(user_src)
        # LSP server cwd is /tmp — NOT user — so boot-time INCLUDES
        # walk doesn't find `../lib`.  Whether the compile succeeds
        # is entirely a question of whether the LSP re-walks INCLUDES
        # per-file on didOpen.
        c = Client("/tmp")
        try:
            _init(c, "/tmp")
            uri = f"file://{user_file}"
            _did_open(c, uri, user_src, 1)
            assert_true(c.wait_for_method("$/compileCompleted", 30),
                        "compileCompleted")
            missing = []
            with c.msgs_lock:
                for m in c.msgs:
                    if m.get("method") == "textDocument/publishDiagnostics":
                        for d in m["params"].get("diagnostics", []):
                            msg = d.get("message", "")
                            if "myLib" in msg or "my_id" in msg:
                                missing.append(msg)
            assert_eq(missing, [],
                      f"LSP should resolve ../lib INCLUDES for the "
                      f"opened file, but produced diagnostics: "
                      f"{missing!r}")
        finally:
            c.close()
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_lsp_holproject_preload_project_dirs():
    """When `bin/hol` is launched inside a `holproject.toml
    holmake = true` project, every discovered project_dir must end
    up in `Meta.loadPath` — so a file whose own directory has no
    `INCLUDES = ../…` chain can still `open` theories in sibling
    project_dirs.

    This is served by `hol.ML`'s boot-time HMProject preload (from
    cwd), so the test launches with `Client(root)` matching eglot's
    convention of starting the server with cwd = workspace root.

    Isolated from the per-didOpen fallback: `user/` has no
    Holmakefile, so `augmentLoadPathForUri` finds no INCLUDES to
    walk.  Only the boot-time project scan can add `lib/` to
    loadPath."""
    root = tempfile.mkdtemp(prefix="lsp_hp_test_")
    try:
        with open(os.path.join(root, "holproject.toml"), "w") as f:
            f.write("holmake = true\n")
        lib = os.path.join(root, "lib")
        user = os.path.join(root, "user")
        os.makedirs(lib); os.makedirs(user)
        with open(os.path.join(lib, "myLibScript.sml"), "w") as f:
            f.write("Theory myLib\n"
                    "Definition my_id_def:\n"
                    "  my_id (x:num) = x\n"
                    "End\n")
        r = subprocess.run(
            [f"{REPO}/bin/Holmake", "myLibTheory"],
            cwd=lib, capture_output=True, text=True)
        assert_true(r.returncode == 0,
                    f"Holmake in {lib} succeeded ({r.stderr!r})")
        user_src = ("Theory uses_lib\n"
                    "Ancestors myLib\n\n"
                    "Theorem noop:\n"
                    "  my_id (n:num) = n\n"
                    "Proof\n"
                    "  simp[my_id_def]\n"
                    "QED\n")
        user_file = os.path.join(user, "uses_libScript.sml")
        with open(user_file, "w") as f:
            f.write(user_src)
        # cwd = fixture root triggers hol.ML's boot-time HMProject
        # preload; mirrors eglot's cwd = project root convention.
        c = Client(root)
        try:
            _init(c, root)
            _did_open(c, f"file://{user_file}", user_src, 1)
            assert_true(c.wait_for_method("$/compileCompleted", 30),
                        "compileCompleted")
            missing = []
            with c.msgs_lock:
                for m in c.msgs:
                    if m.get("method") == "textDocument/publishDiagnostics":
                        for d in m["params"].get("diagnostics", []):
                            msg = d.get("message", "")
                            if "myLib" in msg or "my_id" in msg:
                                missing.append(msg)
            assert_eq(missing, [],
                      f"holproject.toml preload should add every "
                      f"project_dir to loadPath, got: {missing!r}")
        finally:
            c.close()
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_goalState_walker_uses_theorem_position_context():
    """Walker must apply the per-dec Context snapshot for the theorem
    the cursor is inside, not the whole-file post-compile Context.
    Otherwise `srw_ss()` entries registered LATER in the file leak
    back into the walker's `simp[]` and change its normal form.

    This file registers `test_pred_def` into srw_ss via a trailing
    `BasicProvers.export_rewrites`.  At compile time (top-to-bottom)
    the earlier theorem's `simp[]` doesn't have `test_pred` unfolded,
    so the goal `test_pred 3 /\\ 2 + 2 = 4` reduces to `test_pred 3`
    and the following `THEN1 REWRITE_TAC[test_pred_def]` discharges
    it.  Under the buggy walker that runs against the whole-file
    context, `simp[]` unfolds `test_pred` too, closes the goal
    entirely, and the ensuing `THEN1` fails with no-subgoals.

    Cursor is placed right after the `simp[]` line so the walker
    halts before the `THEN1` marker.  Correct behaviour: exactly
    one remaining subgoal `test_pred 3`.  Buggy behaviour: zero
    subgoals (whole goal solved by simp)."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_context_snapshot.sml"
        src = ("Theory goalstate_context_snapshot\n"
               "Ancestors arithmetic\n\n"
               "Definition test_pred_def:\n"
               "  test_pred (x:num) = (x = 3)\n"
               "End\n\n"
               "Theorem test_earlier:\n"
               "  test_pred 3 /\\ 2 + 2 = 4\n"
               "Proof\n"
               "  simp[]\n"
               "  THEN1 REWRITE_TAC[test_pred_def]\n"
               "QED\n\n"
               "val _ = BasicProvers.export_rewrites [\"test_pred_def\"]\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Cursor at end of `  simp[]` (LSP line 10, char 8 = past `]`).
        # Walker applies `simp[]` and stops before the OpenThen1
        # marker at `THEN1`.
        r = _send_goalstate(c, 501, uri, 10, 8)
        result = r.get("result")
        assert_true(result is not None,
                    f"goalState succeeded ({r!r})")
        err = result.get("error")
        assert_true(err is None,
                    f"walker did not time out or error ({err!r})")
        goals = result.get("goals", [])
        assert_eq(len(goals), 1,
                  f"exactly one remaining subgoal — the walker's simp "
                  f"did not close the goal via a later-registered "
                  f"srw_ss entry ({goals!r})")
        goal_text = goals[0].get("goal", "")
        assert_true("test_pred 3" in goal_text,
                    f"remaining subgoal is `test_pred 3` "
                    f"({goal_text!r})")
    finally:
        c.close()


def test_goalState_between_two_theorems():
    """Slice B: cursor between two `Theorem…QED` blocks returns null and
    picks the right block when inside the second one."""
    c = Client("/tmp")
    try:
        _init(c, "/tmp")
        uri = "file:///tmp/goalstate_two.sml"
        src = ("Theory goalstate_two\n"
               "Ancestors arithmetic\n\n"
               "Theorem first:\n"
               "  T\n"
               "Proof\n"
               "  rw[]\n"
               "QED\n"
               "\n"
               "Theorem second:\n"
               "  T /\\ T\n"
               "Proof\n"
               "  rw[]\n"
               "QED\n")
        _did_open(c, uri, src, 1)
        assert_true(c.wait_for_method("$/compileCompleted", 30),
                    "compileCompleted")
        # Line 8 = blank between the two theorems → null.
        r_gap = _send_goalstate(c, 301, uri, 8, 0)
        assert_eq(r_gap.get("result"), None,
                  "cursor between two theorems → null")
        # Line 12 = "  rw[]" inside the second theorem's Proof.
        r_second = _send_goalstate(c, 302, uri, 12, 3)
        result = r_second.get("result")
        assert_true(result is not None,
                    f"cursor inside second theorem populates result "
                    f"({r_second!r})")
        assert_eq(result.get("theorem"), "second", "picks second theorem")
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
    ("hover_on_proof_body_whitespace_is_null",
                                     test_hover_on_proof_body_whitespace_is_null),
    ("hover_type_only_no_identifier_is_null",
                                     test_hover_type_only_no_identifier_is_null),
    ("hover_inside_term_quotation",  test_hover_inside_term_quotation),
    ("hover_inside_theorem_body",    test_hover_inside_theorem_body),
    ("hover_at_body_boundary_and_operators",
                                     test_hover_at_body_boundary_and_operators),
    ("hover_across_utf8_binder_and_var",
                                     test_hover_across_utf8_binder_and_var),
    ("hover_inside_definition_body", test_hover_inside_definition_body),
    ("hover_inside_inductive_body",  test_hover_inside_inductive_body),
    ("stale_sml_binding_dropped",    test_stale_sml_binding_dropped),
    ("heap_autodetect_from_holmakefile",
                                     test_heap_autodetect_from_holmakefile),
    ("heap_autodetect_no_holmakefile",
                                     test_heap_autodetect_no_holmakefile),
    ("heap_autodetect_holmakefile_without_holheap",
                                     test_heap_autodetect_holmakefile_without_holheap),
    ("snapshot_resume_late_edit",    test_snapshot_resume_late_edit),
    ("snapshot_resume_early_edit_falls_back",
                                     test_snapshot_resume_early_edit_falls_back),
    ("snapshot_resume_full_text_replace_resets",
                                     test_snapshot_resume_full_text_replace_resets),
    ("snapshot_resume_survives_grammar_delta",
                                     test_snapshot_resume_survives_grammar_delta),
    ("snapshot_resume_second_edit_after_completion",
                                     test_snapshot_resume_second_edit_after_completion),
    ("goalState_inside_proof",       test_goalState_inside_proof),
    ("goalState_outside_proof",      test_goalState_outside_proof),
    ("goalState_between_two_theorems",
                                     test_goalState_between_two_theorems),
    ("goalState_step_advances_within_proof",
                                     test_goalState_step_advances_within_proof),
    ("goalState_case_split_produces_two_subgoals",
                                     test_goalState_case_split_produces_two_subgoals),
    ("goalState_walker_uses_theorem_position_context",
                                     test_goalState_walker_uses_theorem_position_context),
    ("goalState_walks_double_backslash_in_then1_block",
                                     test_goalState_walks_double_backslash_in_then1_block),
    ("goalState_walks_thenl_branches",
                                     test_goalState_walks_thenl_branches),
    ("goalState_thenl_context_line",
                                     test_goalState_thenl_context_line),
    ("goalState_failed_tactic_signals_error",
                                     test_goalState_failed_tactic_signals_error),
    ("goalState_failed_tactic_publishes_diagnostic",
                                     test_goalState_failed_tactic_publishes_diagnostic),
    ("stale_diags_dont_survive_char_by_char_typing",
                                     test_stale_diags_dont_survive_char_by_char_typing),
    ("diagnostics_deduplicated_across_publish",
                                     test_diagnostics_deduplicated_across_publish),
    ("unclosed_quotation_narrows_to_opening_delimiter",
                                     test_unclosed_quotation_narrows_to_opening_delimiter),
    ("incomplete_definition_mid_file_stays_narrow",
                                     test_incomplete_definition_mid_file_stays_narrow),
    ("incomplete_theorem_statement_mid_file_stays_narrow",
                                     test_incomplete_theorem_statement_mid_file_stays_narrow),
    ("incomplete_proof_body_mid_file_stays_narrow",
                                     test_incomplete_proof_body_mid_file_stays_narrow),
    ("goalState_available_past_compile_pos",
                                     test_goalState_available_past_compile_pos),
    ("runaway_errors_still_publish_diagnostics",
                                     test_runaway_errors_still_publish_diagnostics),
    ("stale_diagnostic_from_partial_parse_clears_on_completion",
                                     test_stale_diagnostic_from_partial_parse_clears_on_completion),
    ("goalState_focused_subgoal_solved_between_close_and_outer",
                                     test_goalState_focused_subgoal_solved_between_close_and_outer),
    ("goalState_thenl_end_shows_proved",
                                     test_goalState_thenl_end_shows_proved),
    ("goalState_walks_squiggle_selector",
                                     test_goalState_walks_squiggle_selector),
    ("goalState_walks_into_by_block",
                                     test_goalState_walks_into_by_block),
    ("goalState_walks_into_suffices_by_block",
                                     test_goalState_walks_into_suffices_by_block),
    ("goalState_walks_into_select_goal_block",
                                     test_goalState_walks_into_select_goal_block),
    ("goalState_walks_map_every",    test_goalState_walks_map_every),
    ("goalState_walks_map_first",    test_goalState_walks_map_first),
    ("goalState_walks_squiggle_minus_rename",
                                     test_goalState_walks_squiggle_minus_rename),
    ("goalState_try_absorbs_failure",
                                     test_goalState_try_absorbs_failure),
    ("goalState_try_multi_step_branch",
                                     test_goalState_try_multi_step_branch),
    ("goalState_try_lt_absorbs_failure",
                                     test_goalState_try_lt_absorbs_failure),
    ("lsp_walks_file_includes_from_arbitrary_cwd",
                                     test_lsp_walks_file_includes_from_arbitrary_cwd),
    ("lsp_holproject_preload_project_dirs",
                                     test_lsp_holproject_preload_project_dirs),
    ("goalState_incomplete_proof_body",
                                     test_goalState_incomplete_proof_body),
    ("goalState_cache_invalidates_on_tactic_edit",
                                     test_goalState_cache_invalidates_on_tactic_edit),
    ("goalState_cache_invalidates_on_upstream_change",
                                     test_goalState_cache_invalidates_on_upstream_change),
    ("goalState_cache_preserved_when_edit_is_downstream",
                                     test_goalState_cache_preserved_when_edit_is_downstream),
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
