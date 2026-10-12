"""An LSP client, and a pool of them, for driving `bin/hol lsp`.

This is the half of the MCP adapter that talks HOL.  It knows LSP --
`Content-Length` framing, request/response correlation, the document
lifecycle -- and nothing about MCP.  `hol_mcp.py` is the other half and
knows nothing about LSP.

Two facts shape everything here.

One process serves one script.  `Theory.load_complete` seals a theory
in `KernelSig`, which lives outside `Context`, so an ancestor a server
loaded for one file can be neither re-read nor withdrawn; the server
refuses files it is not bound to.  So the adapter keeps a *pool* keyed
by file and pays a HOL heap apiece.

Everything is asynchronous and debounced.  A compile starts ~300ms
after the last edit and finishes whenever it finishes, so a tool call
that wants an answer about the file has to open the document and wait
for `$/compileCompleted` rather than assume anything is ready.

Stdlib only, deliberately: this directory is not a Holmake directory
and must stay installable by copying.
"""
import json
import os
import subprocess
import threading
import time


class LspError(Exception):
    """The server answered a request with an error, or did not answer."""


class SessionDead(Exception):
    """The server process is gone."""


def path_to_uri(path):
    return "file://" + os.path.abspath(path)


class Session:
    """One `bin/hol lsp` process, bound to one script.

    Spawned lazily by `SessionPool`.  The reader thread is the only
    thing that touches the receive buffer; everything else reads the
    decoded message list under a lock.
    """

    def __init__(self, hol_bin, cwd, args=(), env=None):
        self.hol_bin = hol_bin
        self.cwd = cwd
        self.started = time.time()
        self.proc = subprocess.Popen(
            [hol_bin, "lsp", *args],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, cwd=cwd,
            env=None if env is None else {**os.environ, **env})
        self._buf = bytearray()
        self._pos = 0
        self._msgs = []
        self._lock = threading.Lock()
        self._cond = threading.Condition(self._lock)
        self._errs = bytearray()
        self._stop = False
        self._next_id = 1
        self._id_lock = threading.Lock()
        # Documents this session has opened, path -> (version, text).
        self.docs = {}
        threading.Thread(target=self._read_stdout, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()

    # -- framing ---------------------------------------------------
    def _read_stdout(self):
        try:
            while not self._stop:
                chunk = self.proc.stdout.read1(65536)
                if not chunk:
                    break
                self._buf.extend(chunk)
                self._drain()
        except Exception:
            pass
        finally:
            # Wake anyone waiting on a reply that will now never come.
            with self._cond:
                self._cond.notify_all()

    def _drain(self):
        while True:
            i = self._buf.find(b"\r\n\r\n", self._pos)
            if i < 0:
                return
            header = bytes(self._buf[self._pos:i]).decode("ascii", "replace")
            length = None
            for line in header.split("\r\n"):
                if line.lower().startswith("content-length:"):
                    try:
                        length = int(line.split(":", 1)[1].strip())
                    except ValueError:
                        length = None
            if length is None or len(self._buf) < i + 4 + length:
                return
            body = bytes(self._buf[i + 4:i + 4 + length])
            self._pos = i + 4 + length
            try:
                msg = json.loads(body)
            except ValueError:
                continue
            with self._cond:
                self._msgs.append(msg)
                self._cond.notify_all()

    def _read_stderr(self):
        try:
            while not self._stop:
                chunk = self.proc.stderr.read1(65536)
                if not chunk:
                    return
                self._errs.extend(chunk)
        except Exception:
            pass

    def stderr_text(self):
        return bytes(self._errs).decode(errors="replace")

    def alive(self):
        return self.proc.poll() is None

    # -- sending ---------------------------------------------------
    def _send(self, msg):
        if not self.alive():
            raise SessionDead(
                "hol lsp exited (rc=%s); stderr tail: %r"
                % (self.proc.returncode, self.stderr_text()[-600:]))
        blob = json.dumps(msg).encode()
        try:
            self.proc.stdin.write(
                b"Content-Length: %d\r\n\r\n%s" % (len(blob), blob))
            self.proc.stdin.flush()
        except Exception as exc:
            raise SessionDead("write to hol lsp failed: %s" % exc)

    def notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params, timeout=120):
        with self._id_lock:
            rid = self._next_id
            self._next_id += 1
        mark = self.mark()
        self._send({"jsonrpc": "2.0", "id": rid,
                    "method": method, "params": params})
        reply = self.wait_for(
            lambda m: m.get("id") == rid and "method" not in m,
            timeout, since=mark)
        if reply is None:
            if not self.alive():
                raise SessionDead(
                    "hol lsp exited while answering %s; stderr tail: %r"
                    % (method, self.stderr_text()[-600:]))
            raise LspError("%s timed out after %ss" % (method, timeout))
        if "error" in reply:
            err = reply["error"]
            raise LspError("%s: %s" % (method, err.get("message", err)))
        return reply.get("result")

    # -- receiving -------------------------------------------------
    def mark(self):
        """Index of the next message to arrive.

        Pass it as `since` so a wait cannot be satisfied by something
        that arrived before the request was even sent -- the mistake
        that makes an async test pass against a server doing nothing.
        """
        with self._lock:
            return len(self._msgs)

    def wait_for(self, pred, timeout, since=0):
        deadline = time.time() + timeout
        idx = since
        with self._cond:
            while True:
                while idx < len(self._msgs):
                    msg = self._msgs[idx]
                    idx += 1
                    if pred(msg):
                        return msg
                remaining = deadline - time.time()
                if remaining <= 0:
                    return None
                self._cond.wait(min(remaining, 0.25))

    def wait_for_method(self, method, timeout, since=0):
        return self.wait_for(lambda m: m.get("method") == method,
                             timeout, since=since)

    def notifications(self, method, since=0):
        with self._lock:
            return [m for m in self._msgs[since:]
                    if m.get("method") == method]

    # -- document lifecycle ---------------------------------------
    def open_or_sync(self, path, text):
        """Make the server's copy of `path` equal `text`.

        Returns the mark to pass as `since` when waiting for the
        compile this triggers, or None when nothing was sent because
        the text was already current.
        """
        known = self.docs.get(path)
        uri = path_to_uri(path)
        if known is None:
            self.docs[path] = (1, text)
            mark = self.mark()
            self.notify("textDocument/didOpen", {
                "textDocument": {"uri": uri, "languageId": "holsml",
                                 "version": 1, "text": text}})
            return mark
        version, old = known
        if old == text:
            return None
        version += 1
        self.docs[path] = (version, text)
        mark = self.mark()
        self.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": text}]})
        return mark

    def await_compile(self, path, since, timeout=180):
        """Wait for the pass triggered at `since` to finish.

        `$/compileCompleted` is the success edge; `$/compileInterrupted`
        is the give-up edge and must be waited on too, or an abandoned
        pass spends the whole timeout.
        """
        uri = path_to_uri(path)

        def done(msg):
            if msg.get("method") not in ("$/compileCompleted",
                                         "$/compileInterrupted"):
                return False
            return (msg.get("params") or {}).get("uri") == uri

        return self.wait_for(done, timeout, since=since)

    def proof_states(self, path):
        """Fold the `$/proofStates` transition stream into a state.

        The server sends transitions and never a full state -- sampling
        one would race a settling worker -- so accumulating is the
        client's job.  Last write per name wins, names being how the
        pool identifies a proof.
        """
        uri = path_to_uri(path)
        states = {}
        with self._lock:
            msgs = list(self._msgs)
        for msg in msgs:
            if msg.get("method") != "$/proofStates":
                continue
            params = msg.get("params") or {}
            if params.get("uri") != uri:
                continue
            for state in params.get("states", []):
                states[state.get("name")] = state
        return states

    def await_proofs(self, path, timeout=600):
        """Wait for every known proof to stop being `checking`.

        `$/compileCompleted` is *not* this.  It says elaboration
        finished; the proofs it enqueued are then checked on a pool, so
        a tally read at that moment says `checking` and a verdict built
        from it says nothing is broken.  A confident clean answer about
        a file with a false theorem in it is the worst thing this
        adapter could return, so it waits.

        Safe to start only after `await_compile`: a proof is announced
        as `checking` when it is enqueued, and enqueueing happens
        during elaboration, so by then the set is complete.

        Returns the settled tally, and whether it actually settled.
        """
        deadline = time.time() + timeout
        while True:
            states = self.proof_states(path)
            pending = [s for s in states.values()
                       if s.get("status") == "checking"]
            if not pending:
                return states, True
            if time.time() >= deadline or not self.alive():
                return states, False
            with self._cond:
                self._cond.wait(0.1)

    def close(self, grace=20):
        try:
            self._send({"jsonrpc": "2.0", "id": 0x7FFFFFFF,
                        "method": "shutdown", "params": None})
            self.wait_for(lambda m: m.get("id") == 0x7FFFFFFF, grace)
            self._send({"jsonrpc": "2.0", "method": "exit", "params": None})
            deadline = time.time() + grace
            while time.time() < deadline and self.alive():
                time.sleep(0.05)
        except Exception:
            pass
        finally:
            try:
                if self.alive():
                    self.proc.kill()
                    self.proc.wait(timeout=5)
            except Exception:
                pass
            self._stop = True


class SessionPool:
    """One session per script, created on demand.

    Keyed by the file's absolute path because that is the granularity
    the server itself enforces -- it refuses documents it is not bound
    to, so two scripts cannot share one process however much we would
    like them to.
    """

    def __init__(self, hol_bin, args=(), env=None, init_timeout=120):
        self.hol_bin = hol_bin
        self.args = tuple(args)
        self.env = env
        self.init_timeout = init_timeout
        self._sessions = {}
        self._lock = threading.Lock()

    def describe(self):
        with self._lock:
            return [{"file": path,
                     "pid": s.proc.pid,
                     "alive": s.alive(),
                     "uptime_s": round(time.time() - s.started, 1)}
                    for path, s in sorted(self._sessions.items())]

    def get(self, path):
        path = os.path.abspath(path)
        with self._lock:
            session = self._sessions.get(path)
            if session is not None and session.alive():
                return session
            if session is not None:
                session.close()
                del self._sessions[path]
            session = self._spawn(path)
            self._sessions[path] = session
            return session

    def _spawn(self, path):
        cwd = os.path.dirname(path) or "."
        session = Session(self.hol_bin, cwd, self.args, self.env)
        # utf-8 position encoding: every offset the adapter computes is
        # a byte offset, and a HOL script with `.."` quotations is
        # full of multibyte characters, so negotiating utf-16 here
        # would mis-place every range by the width of the quotes.
        session.request("initialize", {
            "processId": None,
            "rootUri": path_to_uri(cwd),
            "capabilities": {"general": {"positionEncodings": ["utf-8"]}},
        }, timeout=self.init_timeout)
        session.notify("initialized", {})
        # Proof checking is off unless asked for -- the CLI flag
        # `--lsp-check-proofs' only sets the initial value.  For an
        # editor that is a reasonable default; for this adapter it is
        # the whole point, "did my proofs survive" being the question
        # a model asks most.  Sent before any `didOpen', so the
        # recompile switching it on would force has no pass to force.
        try:
            session.request("$/setConfig", {"checkProofs": True},
                            timeout=30)
        except LspError:
            pass  # an older server without the switch still works
        return session

    def restart(self, path):
        path = os.path.abspath(path)
        with self._lock:
            session = self._sessions.pop(path, None)
        if session is not None:
            session.close()
        return self.get(path)

    def close_all(self):
        with self._lock:
            sessions = list(self._sessions.values())
            self._sessions.clear()
        for session in sessions:
            session.close()
