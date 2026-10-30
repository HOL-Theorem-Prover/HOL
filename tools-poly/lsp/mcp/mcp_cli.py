#!/usr/bin/env python3
"""A command-line client for `hol_mcp.py`.

    mcp_cli.py --serve [--socket S] [--hol H] [--repo R]   # daemon
    mcp_cli.py [--socket S] <tool> ['<json arguments>']     # call
    mcp_cli.py [--socket S] --list                          # tools/list
    mcp_cli.py [--socket S] --stop                          # stop daemon

`hol_mcp.py` speaks MCP and nothing else, so the only things that can
drive it are MCP clients -- which means a model whose host registered
it, and nothing a human, a shell or a test can reach.  This is that
missing half: it speaks the same newline-delimited JSON-RPC 2.0 to the
adapter and ordinary argv/stdout to whoever ran it.

Why a daemon rather than a process per call.  The adapter pools one
`bin/hol lsp` per script and each one pays a HOL heap -- seconds of
startup and hundreds of megabytes.  A one-shot client throws that pool
away after every question, so the second question about a file costs
as much as the first.  `--serve` keeps one adapter alive behind a unix
socket and the pool with it; without `--socket` the call still works,
one-shot, which is what a smoke test wants.

Stdlib only, like the rest of this directory: it must stay installable
by copying.
"""
import argparse
import json
import os
import socket
import subprocess
import sys
import threading

HERE = os.path.dirname(os.path.abspath(__file__))
ADAPTER = os.path.join(HERE, "hol_mcp.py")
DEFAULT_SOCKET = os.environ.get(
    "HOL_MCP_SOCKET", os.path.join("/tmp", "hol-mcp-%d.sock" % os.getuid()))

# A tool call can legitimately run for many minutes -- `hol_check_file`
# alone allows 180s of elaboration plus 600s of proof checking -- so the
# client must not impose a deadline shorter than the adapter's own.
CALL_TIMEOUT = 1800


def log(msg):
    sys.stderr.write("[mcp-cli] %s\n" % msg)
    sys.stderr.flush()


class Adapter:
    """One `hol_mcp.py` child, spoken to in newline-delimited JSON-RPC.

    The adapter's `serve()` loop is single-threaded and answers in
    order, so one lock around write-then-read is the whole concurrency
    story.  Holding it for the duration of a call is deliberate: the
    adapter could not have overlapped them anyway, and a queue here is
    easier to reason about than one inside it.
    """

    def __init__(self, hol=None, repo=None):
        argv = [sys.executable, ADAPTER]
        if hol:
            argv += ["--hol", hol]
        if repo:
            argv += ["--repo", repo]
        self.proc = subprocess.Popen(
            argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=None, text=True, bufsize=1)
        self._lock = threading.Lock()
        self._id = 0
        self._rpc("initialize", {
            "protocolVersion": "2025-06-18",
            "capabilities": {},
            "clientInfo": {"name": "mcp_cli", "version": "1"}})
        self._notify("notifications/initialized", {})

    def _notify(self, method, params):
        self.proc.stdin.write(
            json.dumps({"jsonrpc": "2.0", "method": method,
                        "params": params}) + "\n")
        self.proc.stdin.flush()

    def _rpc(self, method, params=None):
        with self._lock:
            self._id += 1
            msg = {"jsonrpc": "2.0", "id": self._id, "method": method}
            if params is not None:
                msg["params"] = params
            self.proc.stdin.write(json.dumps(msg) + "\n")
            self.proc.stdin.flush()
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    raise RuntimeError(
                        "hol_mcp.py exited (rc=%s)" % self.proc.poll())
                line = line.strip()
                if not line:
                    continue
                reply = json.loads(line)
                # The adapter answers in order and sends nothing
                # unsolicited, but correlating anyway costs one
                # comparison and turns a protocol change from a silent
                # wrong answer into a loud one.
                if reply.get("id") == self._id:
                    return reply

    def call(self, tool, arguments):
        reply = self._rpc("tools/call",
                          {"name": tool, "arguments": arguments})
        if "error" in reply:
            return "RPC ERROR: %s" % json.dumps(reply["error"]), True
        result = reply.get("result") or {}
        chunks = [c.get("text", "") for c in result.get("content", [])
                  if c.get("type") == "text"]
        return "\n".join(chunks), bool(result.get("isError"))

    def tools(self):
        reply = self._rpc("tools/list")
        return (reply.get("result") or {}).get("tools", [])

    def close(self):
        try:
            self.proc.stdin.close()
        except Exception:
            pass
        try:
            self.proc.wait(timeout=10)
        except Exception:
            self.proc.kill()


# ------------------------------------------------------------------ #
# Daemon
# ------------------------------------------------------------------ #
def serve(sock_path, hol, repo):
    if os.path.exists(sock_path):
        # A stale socket from a killed daemon is a file, not a
        # listener; connecting is the only way to tell the two apart.
        probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            probe.connect(sock_path)
            probe.close()
            log("a daemon is already listening on %s" % sock_path)
            return 1
        except OSError:
            os.unlink(sock_path)
        finally:
            probe.close()

    adapter = Adapter(hol, repo)
    server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    server.bind(sock_path)
    server.listen(16)
    log("listening on %s (adapter pid %d)" % (sock_path, adapter.proc.pid))
    stopping = False
    try:
        while not stopping:
            conn, _ = server.accept()
            try:
                conn.settimeout(CALL_TIMEOUT)
                data = b""
                while not data.endswith(b"\n"):
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    data += chunk
                if not data.strip():
                    continue
                req = json.loads(data.decode("utf-8"))
                if req.get("op") == "stop":
                    stopping = True
                    reply = {"text": "stopping", "isError": False}
                elif req.get("op") == "list":
                    reply = {"text": json.dumps(adapter.tools(), indent=2),
                             "isError": False}
                else:
                    text, err = adapter.call(req["tool"],
                                             req.get("arguments") or {})
                    reply = {"text": text, "isError": err}
            except Exception as exc:
                reply = {"text": "%s: %s" % (type(exc).__name__, exc),
                         "isError": True}
            try:
                conn.sendall((json.dumps(reply) + "\n").encode("utf-8"))
            except Exception:
                pass
            finally:
                conn.close()
    finally:
        adapter.close()
        try:
            os.unlink(sock_path)
        except OSError:
            pass
    return 0


def send(sock_path, payload):
    conn = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    conn.settimeout(CALL_TIMEOUT)
    conn.connect(sock_path)
    conn.sendall((json.dumps(payload) + "\n").encode("utf-8"))
    data = b""
    while not data.endswith(b"\n"):
        chunk = conn.recv(65536)
        if not chunk:
            break
        data += chunk
    conn.close()
    return json.loads(data.decode("utf-8"))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--serve", action="store_true",
                        help="run the daemon in the foreground")
    parser.add_argument("--socket", default=DEFAULT_SOCKET)
    parser.add_argument("--hol", default=None)
    parser.add_argument("--repo", default=None)
    parser.add_argument("--list", action="store_true",
                        help="print the tool schemas")
    parser.add_argument("--stop", action="store_true",
                        help="ask a running daemon to exit")
    parser.add_argument("tool", nargs="?")
    parser.add_argument("arguments", nargs="?", default="{}",
                        help="JSON object of tool arguments")
    opts = parser.parse_args(argv)

    if opts.serve:
        return serve(opts.socket, opts.hol, opts.repo)

    live = os.path.exists(opts.socket)
    if opts.stop:
        if not live:
            log("no daemon at %s" % opts.socket)
            return 0
        print(send(opts.socket, {"op": "stop"})["text"])
        return 0

    if opts.list:
        payload = {"op": "list"}
    else:
        if not opts.tool:
            parser.error("give a tool name, or --list/--stop/--serve")
        try:
            args = json.loads(opts.arguments)
        except ValueError as exc:
            parser.error("arguments must be a JSON object: %s" % exc)
        payload = {"tool": opts.tool, "arguments": args}

    if live:
        reply = send(opts.socket, payload)
    else:
        # One-shot: correct, just slow, and the only mode a test with
        # no daemon of its own can use.
        adapter = Adapter(opts.hol, opts.repo)
        try:
            if payload.get("op") == "list":
                reply = {"text": json.dumps(adapter.tools(), indent=2),
                         "isError": False}
            else:
                text, err = adapter.call(payload["tool"],
                                         payload["arguments"])
                reply = {"text": text, "isError": err}
        finally:
            adapter.close()

    print(reply["text"])
    return 1 if reply.get("isError") else 0


if __name__ == "__main__":
    sys.exit(main())
