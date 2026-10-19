# An MCP server over the HOL4 LSP server

`hol_mcp.py` exposes HOL4 to a model through the [Model Context
Protocol](https://modelcontextprotocol.io).  It is an *adapter*: it
speaks MCP to the model and LSP to one `bin/hol lsp` per script, and
contains no HOL logic of its own.

Python 3.8+, standard library only, no build step.

## Running it

    tools-poly/lsp/mcp/hol_mcp.py [--hol <bin/hol>] [--repo <HOL tree>]

Both default to the tree this file lives in, so from a built checkout
the bare command works.  MCP is spoken on stdin/stdout; everything
human goes to stderr.

In a client's configuration:

```json
{
  "mcpServers": {
    "hol4": {
      "command": "/path/to/HOL/tools-poly/lsp/mcp/hol_mcp.py"
    }
  }
}
```

Launched by path, not by registry name, and it reaches `bin/hol`
relative to itself — so the adapter and the server it drives always
come from the same tree.  That is the point: the two speak a private
protocol with no version negotiation in it, and a packaged adapter
talking to somebody else's HOL would be free to skew.

## Tools

| Tool | What it answers |
|---|---|
| `hol_check_file` | Does this script compile, and did every proof in it go through? |
| `hol_goal_state` | What is the goal inside *theorem* — at the end, at step *n*, or where it fails? |
| `hol_try_tactic` | What would *tactic* do here — without editing the file? |
| `hol_search` | Which theorems match this name, theory or term pattern? |
| `hol_sessions` | Which servers are running? |
| `hol_restart` | Pick up a dependency rebuilt since the server started. |

Every tool naming a `file` re-reads it from disk and makes the
server's copy current before answering, so a model that edits a script
with its own tools does not then get answers about the version the
server last saw.

## What the adapter owns

The LSP server was built for a human with a cursor in a buffer.  A
model has neither, and three gaps follow.

**Addressing.** Every server hook takes a URI and a position.  A model
has a *name*.  `textDocument/documentSymbol` is the authoritative
declaration index, so name → declaration is a lookup — but the walker
wants a cursor *inside* the `Proof … QED` body (`findEnclosingTheorem`
tests `proof_ <= cursor <= qed_`), and a declaration's start is before
`proof_`.  So is the offset `$/proofStates` reports, which is the same
declaration start.  The adapter therefore aims at the `QED` token that
closes the body, found inside the range the server's own parser gave
it.  That satisfies the upper bound exactly, and because the cursor
also decides how *far* the walk goes, it makes the default — no `step`
given — the end of the proof, which is the state a reader wants when
they name a theorem and nothing else.

A by-name request on the server would be tidier, and is the obvious
next server-side addition.  Until then this is adapter-side and costs
nothing.

**Waiting.** Compiles are debounced and asynchronous, and the proof
tally arrives as a transition stream with deliberately no full-state
message — sampling one would race a settling worker.  So a tool call
opens the document, waits for `$/compileCompleted`, and accumulates
the stream.

`$/compileCompleted` is *not* the end of proof checking: it says
elaboration finished, and the proofs it enqueued are checked
afterwards on a pool.  A tally read at that moment says `checking`,
and a verdict built from it says nothing is broken — a confident clean
answer about a file with a false theorem in it, which is the worst
thing this adapter could return.  `check_file` waits for every proof
to stop being `checking`, and when it runs out of patience says
`INCOMPLETE` rather than reporting a total.

Proof checking is also off unless asked for (`--lsp-check-proofs` only
sets the initial value), so the adapter turns it on at session
startup, before any `didOpen`.

**Budget.** A goal with ninety assumptions does not fit in a reply
worth sending.  `_budget` keeps head *and* tail, and every caller puts
its diagnosis in a footer appended after the cut — because the
attribution for a failure is the shortest and most valuable thing in
the reply, and a truncation that eats it does so in exactly the case
that needed it.

ANSI stripping lives here too: the server renders through a
pretty-printer whose default backend emits VT100 colour, which is
right for its other two clients and is literal noise to a model.

**Convention.**  The server's other clients are editor panes, and two
of its conventions assume one.  Goals are listed in HOL's goalstack
order, which puts the *current* goal last — unambiguous beside a
cursor, and bottom-to-top in a transcript, which is how four `>-`
branches of a cakeml lemma came to be reordered to match a display.
And a goal-state walk does not stop at a failure: a cursor asks what
the state *here* is, so the walk stands `cheat` in for what a failed
`>-` branch owed and carries on, and the step it reports is where it
ended rather than where the proof went wrong.

So the adapter prints the structured `goals` array, numbered `goal i
of n`, rather than the pre-rendered `pretty` string; and when a reply
blames a position, it asks again anchored there and shows the state
that step was actually given, saying in the footer which step is
which.  The server is unchanged — both conventions are right for the
clients they were built for.

## One process per script

`Theory.load_complete` seals a theory in `KernelSig`, which lives
outside `Context`, so an ancestor a server loaded for one file can be
neither re-read nor withdrawn; the server refuses files it is not
bound to.  The pool is keyed by absolute path and pays a HOL heap
apiece.  `hol_sessions` shows what that is costing.

A running server is also pinned to the artifacts it loaded at startup,
so rebuilding a dependency with `Holmake` does not reach it.
`hol_restart` is what picks the rebuild up.

## Not here yet

Build orchestration (`Holmake` as a tool, with the per-artifact
coordination several agents sharing a tree need), per-step cost
attribution, and the advisory layer that turns facts into what-to-do-
next.  All three are planned; none is in this slice.

## Tests

The LSP side is covered by `../tests/lsp_tests.py`, which this adapter
reuses the client design of.  The adapter's own end-to-end coverage is
not yet in the suite.
