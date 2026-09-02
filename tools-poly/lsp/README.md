# HOL LSP server — developer quick-start

The `hol lsp` subcommand starts a Language Server Protocol server over
stdio that speaks LSP 3 to any conforming client.  This file is a
practical guide to trying it out; the protocol details live in
[`Manual/Developers/lsp-server.md`](../../Manual/Developers/lsp-server.md).

## What it does today

- Runs on top of `bin/hol.state` (post-boss).
- On `didOpen` / `didChange`, incrementally compiles the file via
  `PolyML.compiler`.  Compilation is execution: every SML top-level
  declaration is type-checked, run, and its HOL side-effects (theory
  segment, DB, TypeBase, simpsets, grammars) applied to live state.
- **Fast-oracle prover swap.**  `holide.ML` replaces `Tactical.set_prover`
  with `fn (t, _) => mk_oracle_thm "fast_proof" t`.  `prove(term, tac)`
  never actually calls `tac`; the theorem is minted with a
  `fast_proof` oracle tag.  Compilation is therefore near-batch-build
  speed even for files heavy in tactic proofs, at the cost of not
  detecting tactic errors.
- Server capabilities advertised: `textDocumentSync`, `hoverProvider`,
  `definitionProvider`, `referencesProvider`.  Plus LSP extensions:
  `$/setConfig` (elabOn mode, holdep behaviour, hover width),
  `$/eval` (streamed
  arbitrary SML), `$/hol/goalState` (goal-state at cursor — see
  below), `$/cancelRequest`, `$/compileProgress` /
  `$/compileCompleted` / `$/compileInterrupted` /
  `$/compileBlocked`, `$/hol/retryCompile`.
- Server capabilities also cover `documentSymbolProvider`,
  `workspaceSymbolProvider` and `completionProvider`, so an editor's
  outline, symbol search and completion work with no client-side code
  — see "Symbols, completion and their scope".
- **Unloadable ancestors stop the file.**  A script that names an
  ancestor or library the server cannot load — not built yet, or
  raising on load — gets no compile at all: there is nothing to
  elaborate it against, so every name it takes from that dependency
  would draw its own diagnostic, at the price of the file's whole
  elaboration.  The server publishes the load failures against the
  header entries that asked for them, sends `$/compileBlocked`, and
  answers `null` to `$/hol/goalState` until the file's declared
  dependency list changes.  Editing that list — `Ancestors` / `Libs`,
  or a leading top-level `open` — is what makes it try again; so does
  `$/hol/retryCompile`, for when the ancestor has been built outside
  the editor and the header is already right — `M-h M-C` in the
  shipped eglot client, "HOL: Compile the active script again" in
  hol4-vscode.

Sanity check the server works before wiring up an editor.  The
protocol requires strict CRLF line endings on the header block, so
you cannot just paste into an interactive terminal (Enter sends `\n`,
not `\r\n`, and the server will silently sit in its header-read
loop).  Send a full initialize / shutdown / exit handshake through
`printf` instead:

    printf 'Content-Length: 116\r\n\r\n{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{},"rootUri":"file:///tmp","processId":null}}Content-Length: 52\r\n\r\n{"jsonrpc":"2.0","method":"initialized","params":{}}Content-Length: 58\r\n\r\n{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}Content-Length: 47\r\n\r\n{"jsonrpc":"2.0","method":"exit","params":null}' | bin/hol lsp

That sends the full initialize / initialized / shutdown / exit
handshake in one go.  You should see the `initialize` response
advertising `textDocumentSync`, `hoverProvider`,
`definitionProvider`, `referencesProvider`; a
`window/logMessage "started"` notification; the `shutdown` response
(`{"id":2,"result":null}`); and a clean exit 0.

## Hover

Hover on an SML identifier gives its type and, when the identifier
names something the file namespace can resolve, its **value** --
rendered by HOL's own pretty printers, so a theorem shows its
statement:

```
val loc: Thm.thm = |- 1 + 1 = 2
val n: int = 42
val pair: int * Thm.thm = (42, |- 1 + 1 = 2)
```

Three things make that work, and each of them limits it:

- `lsp/pretty_printers_init.ML` installs Poly/ML pretty printers for
  `thm`, `term` and `hol_type` in the LSP session.  Without them
  `PolyML.NameSpace.Values.print` renders a theorem as `?`, which is
  why theorems used to be looked up in DB *by name* -- a path that
  cannot reach a `[local]` theorem, nor a value that merely contains
  one.  DB is still the fallback for a name that is not in scope at
  all.
- The compile thread's file-namespace layer is thread-local, and a
  hover is answered on its own thread, so the hover installs the
  captured layer (`nsLayer`) first.  Without that step the only values
  it can see are the ones the LSP boot session left in
  `globalNameSpace`, and that session `open`s nothing on purpose.
- A value is printed only for an identifier whose declaration is
  external (Poly/ML gives it id 0) or is one of the buffer's top-level
  declarations, matched by comparing `PTdeclaredAt` against the
  outline's `selSpan`s.  A function parameter or a `let`-bound name is
  in no namespace, and a same-named top-level binding is a different
  thing entirely, so those get their type only.

Dotted names (`numSyntax.plus_tm`) are walked a component at a time
through `PolyML.NameSpace.Structures.contents`, because Poly/ML's
value tables are flat.

Contents go out as markdown in a fenced code block.  Unfenced, a
client treats single newlines as spaces and reflows the statement in a
proportional font, which throws away every break the pretty printer
just chose.

### Width

Hover text is laid out at 100 columns until a client says otherwise:

```json
{"jsonrpc":"2.0","id":1,"method":"$/setConfig",
 "params":{"hoverWidth":72}}
```

It has to come from the client -- only the client knows how wide its
hover box is, and a statement broken to some other width breaks in the
wrong places.  Widths outside 20-500 are ignored and logged.  In VS
Code this is the `hol4-mode.lsp.hoverWidth` setting, defaulting to 72,
because the extension API does not expose a hover box's width; under
eglot, hovers land in the frame-wide echo area, so
`hol-lsp-hover-width` is nil (leave it at 100) unless you set a number
or the symbol `frame`.

## Proof checking (`--lsp-check-proofs`)

Elaboration does not run tactics: `holide.ML` swaps in a prover that
mints an oracle-tagged theorem, which is what makes compilation fast.
Started with `--lsp-check-proofs`, the server instead *queues* each
proof and a worker pool (`lsp/deferred_proofs.ML`, on HOL's `Future`)
replays them, one cancellable group per proof.  Off by default, so an
LSP session costs elaboration only unless asked otherwise.

Three of the pool's verdicts are diagnostics, keyed by theorem name
and squiggled on the theorem's own name:

| verdict | severity | means |
|---|---|---|
| `Failed` | error | the replay did not go through.  A real build would have raised out of `store_thm_at`, so nothing below it is trustworthy. |
| `Suspended` | warning | the proof is *correct*; our model of the file was wrong.  A real build stashes such a theorem instead of saving it, so the declarations below were elaborated as though it had been saved.  Names the subgoals. |
| `Diverged` | warning | the proof went through but produced extra hypotheses, so what elaboration stood in for was not what the proof gives. |

The other states are not diagnostics: `Proved` and `Cheated` are not
complaints, and `Checking` is not one yet.

These entries are **not** cleared by a fresh compile, unlike the
walker's.  The pool owns their lifetime and announces every change,
the `Cheated` of a dropped proof included, so clearing them on a
compile that reuses its entries would lose a squiggle with nothing
left to restore it.  A proof that gets fixed therefore clears in two
steps: the edit drops the entry (`cheated`), and the re-elaborated
proof settles as `proved`.

Every change is also announced on `$/proofStates` as a transition --
`checking`, then a verdict, `cheated` when an entry is dropped -- for
a client that wants to render progress per declaration.  There is
deliberately no full-state message: the state would have to be
sampled and only then sent, so a worker settling in between would have
its newer verdict overwritten by the older sample.

## Goal-state at cursor (`$/hol/goalState`)

Custom LSP request that returns the goal-state for a cursor position
inside a `Proof … QED` block.  The server walks the tactic body via
`goalFrag` up to the step under the cursor, snapshotting states in a
per-theorem cache so subsequent queries at nearby cursors reuse work.

### Request

```json
{
  "jsonrpc": "2.0", "id": <n>,
  "method": "$/hol/goalState",
  "params": {
    "textDocument": {"uri": "file:///path/to/Script.sml"},
    "position": {"line": <0-based>, "character": <0-based, in the
                 negotiated encoding>},
    "width": <optional: column width to render `pretty` at; default 75>
  }
}
```

### Response

`result` is `null` when the cursor isn't inside a `Proof … QED` (or
when the theorem statement can't be parsed).  Otherwise:

```json
{
  "theorem": "<theorem name>",
  "step": <int>,
  "goals": [{"asms": ["<assumption>", ...], "goal": "<goal>"}, ...],
  "pretty": "<full REPL-style render>",
  "context": ["<combinator tag>", ...],
  "status": "ok" | "pending",
  "error": <string or null>
}
```

- `step` — 0-based tactic-step index at the cursor, counting only
  `Expand` / `ExpandList` steps (structural markers like `>-` /
  `THEN1` don't advance it).
- `goals` — structured per-subgoal render for clients that want to
  format goals themselves.
- `width` — the column width to break lines at, which only the client
  knows: it is the width of the pane the answer is going into.  Both
  `pretty` and the strings in `goals` respect it.  Omit it for the
  75 columns HOL's own goalstack printing uses.  The shipped clients
  measure: eglot from `window-body-width` of the *HOL Goals* window,
  hol4-vscode from a hidden monospace ruler in the webview, re-asking
  when the pane is resized.

- `pretty` — the whole state rendered by HOL's `goalFrag.pp_goalstate`
  via the VT100 backend, so bound / free variables carry ANSI colour
  escapes (`\x1B[…m`).  Clients that don't render ANSI can strip the
  escapes with `\x1B\[[0-9;]*m` or fall back to `goals`.
- `context` — the combinator tags naming what is still open around
  the focus, outermost first: `"branch 2 of 3 of THENL"`,
  `"inside 2 nested >-"`.  `pretty` already prints these above the
  goals, so a client rendering it verbatim can ignore the field; it
  is sent separately so a client can pin them somewhere that doesn't
  scroll, which matters because the goals are listed with the current
  one last.  Matching the exact strings is also how a client can
  strip the line back out of `pretty` — a goal may itself begin with
  a `[`.
- `status` — `"pending"` when the answer is provisional because the
  file's own compile hasn't finished.  The walker compiles each
  tactic against the file's namespace, so until the file's `open`s
  have run the tactic names aren't there and nothing can be applied;
  goal-state requests are answered during a compile on purpose (see
  `goalStateAtPos`), so a client should show what it gets but not
  treat it as settled.  A tactic whose source doesn't compile never
  produces an `error` either way: the file's compile reports the real
  message against that very text, and the walker would only duplicate
  and misdescribe it.
- `error` — non-null when the walker gave up (e.g. wall-clock budget
  exceeded); `goals` / `pretty` are empty and clients should render
  the message in place of the state.  A mid-walk partial state is
  complete for its own step but wrong for the cursor's step, so the
  server refuses to send it and returns `error` instead.  A stderr
  line `goal-state walker exceeded Nms budget; interrupting` is
  also emitted for visibility.

### Client cookbook

- **eglot (shipped in this repo)** — `hol-lsp-show-goal-state` bound
  to `M-h M-g`.  The *HOL Goals* window is scrolled to the buffer's
  end, the current goal being last and the subgoal count printed
  after them, with `theorem`, `step`, `context` and `error` in the
  window's `header-line-format` so they stay visible.  An empty
  `goals` with no `error` means the focused subgoal(s) are proved —
  what `pretty` announces on its first line, which scrolling to the
  end would carry out of sight — so the header shows that too.
  The pane goes beside the script window when that window is at
  least `hol-lsp-goals-side-min-width` columns (default 160, so both
  halves clear HOL's 75-column render), and below it otherwise.
  Set `hol-lsp-goals-follow-cursor` non-nil to make
  `*HOL Goals*` auto-refresh on cursor movement (debounced via
  `hol-lsp-goals-follow-delay`).  `hol-lsp--render-goals` runs
  `ansi-color-apply-on-region` on the inserted `pretty` text so the
  bound / free variable colouring survives.
- **VS Code** —
  [hol4-vscode](https://github.com/HOL-Theorem-Prover/hol4-vscode)
  ships a client and a HOL Goals pane on `main`; see
  [`vscode-setup.md`](vscode-setup.md) for a step-by-step install.
  To drive `$/hol/goalState` yourself,
  `client.sendRequest("$/hol/goalState", params)`
  returns the response object.  For the simplest path, strip the ANSI
  escapes (regex `\x1B\[[0-9;]*m`) and display `pretty` as plain text
  in a `WebviewPanel`, or ignore `pretty` entirely and render the
  `goals` array structurally.  Keeping the colours requires an
  ANSI-to-HTML converter (e.g. `ansi_up` on npm) plus a small CSS
  palette in the webview.

The server picks its position encoding (LSP 3.17) from the client's
`general.positionEncodings` at `initialize`: `utf-8` when that is on
offer, because the server's own offsets are bytes and nothing then has
to be converted, and `utf-16` otherwise — including for a client that
offers nothing, which is what the spec says its silence means.  Either
way `position.character` counts in the encoding the `initialize` reply
names, in both directions and for every request, so a client need only
speak the units it already has.

Note for a client built on `vscode-languageclient`: it advertises only
`utf-16` and throws on any other answer, so it gets `utf-16` and must
not translate positions itself.

## Emacs

The repo ships `holscript-mode` (`tools/editor-modes/emacs/`), which
does the syntax highlighting and structural editing but is not itself
an LSP client.  Pair it with either **eglot** (built into Emacs ≥ 29)
or **lsp-mode** (from MELPA).

### With eglot

Eglot documentation: `M-x info` → `(eglot)`.  Minimal `init.el`:

```elisp
;; hol-mode.el / holscript-mode.el on the load-path.
(add-to-list 'load-path
             "/absolute/path/to/HOL/tools/editor-modes/emacs")
(require 'hol-mode)

;; Registers the server for both holscript-mode and its tree-sitter
;; variant holscript-ts-mode, gives each buffer its own LSP project,
;; and auto-starts eglot from each mode hook.
(hol-lsp-enable)

;; Optional: *HOL Goals* follows point.
(setq hol-lsp-goals-follow-cursor t)
```

That is the whole configuration — in particular there is no need to
add an `eglot-server-programs` entry, call `eglot-ensure`, or send
`$/setConfig` by hand:

- `hol-lsp-enable` registers `hol-lsp--server-program`, which resolves
  `bin/hol` per file through `.hol/make-deps/lastmaker`.  A literal
  `("/path/to/HOL/bin/hol" "lsp")` entry pins every buffer to one
  tree, which is wrong as soon as you have more than one worktree.
  It also covers both modes: `holscript-ts-mode` derives from
  `prog-mode`, not from `holscript-mode`, so a single-mode entry
  misses one of the two.
- Auto-start is `hol-lsp-enable`'s job as well; it adds
  `hol-lsp--setup-buffer` (which ends in `eglot-ensure`) to both mode
  hooks.  Note `eglot-managed-mode-hook` is *not* an auto-start hook —
  it runs only once eglot is already managing the buffer.
- `elabOn` already defaults to `Change`, so setting it to `1`
  changes nothing; see Troubleshooting for the case where you want
  `2`.

#### One server per buffer

`hol-lsp-enable` gives every script buffer its own LSP project, so
every buffer gets its own server process.  This is not a tuning
choice; a server cannot be re-aimed at a second file.  A file's
ancestors have to be present in the theory graph, only loading puts
them there, and loading a theory seals it (`Theory.load_complete`) —
so an ancestor already loaded for the first file can neither be
re-read for the second nor withdrawn.  Serve two files from one
process and the second one's goals and hovers are quietly wrong.
The server says so via `window/showMessage` if a client opens a
second file anyway.

Two consequences worth knowing:

- **Each server holds a HOL heap.**  Ten open script buffers means
  ten `bin/hol lsp` processes.  `hol-lsp-autoshutdown` (default `t`)
  therefore shuts a buffer's server down when the buffer is killed,
  set buffer-locally over `eglot-autoshutdown` so other languages
  keep your own policy.
- **`M-x eglot` is not equivalent.**  It connects one server for the
  current project and adopts every same-mode buffer under it, which
  is exactly the arrangement that breaks.  Let `hol-lsp-enable`'s
  hook start the server.

#### What one file's server can see of another

Two files edited at once, in two servers, are completely isolated:
neither server can read the other's buffer, and no unsaved edit in one
can change any answer given for the other.  This holds whichever way
the dependency runs -- a library that opens this script's theory, or a
script that opens that library -- because a server has exactly three
inputs and none of them is another editor buffer: its own client's
text, the Holmake-built artifacts on disk, and `bin/hol.state`.

Isolation is not freshness, and the difference bites:

- **A server is pinned to the artifacts it first loaded.**  `Meta.load`
  records a module as loaded and never re-reads it, and the server
  keeps that record across recompiles on purpose -- re-reading a
  theory is impossible once it is sealed.  So rebuilding a dependency
  with `Holmake` does *not* update an already-running server.  Restart
  it.
- **The exception is a dependency that was missing.**  One that failed
  to resolve is genuinely re-read, which is what `$/hol/retryCompile`
  ("Compile the active script again", `M-h M-C`) is for.  A
  *half-built* dependency -- `.uo` present, a file it names absent --
  is the awkward case: nothing loaded but the module is marked, and
  only a restart clears it.
- **Stale locations look like cross-talk.**  Go-to-definition into a
  theory, and hover on a theorem, report the path, line and statement
  recorded in the *built* theory.  Edit that script in another window
  and the numbers drift, though nothing was shared.
- **`Holmakefile` `INCLUDES` are read once per directory per server.**
  Add one and restart.

Isolation is a property of the process boundary, not of the code: two
files served by one process would share the whole of HOL's `Context`,
the sealed-theory set and `Meta.loadedMods`.  The server therefore
declines to compile a file it is not bound to, so the guarantee does
not rest on the client starting one process per script.  A consequence
worth stating: `.sig` files and library `.sml` files get no IDE
features at all.

#### Symbols, completion and their scope

`textDocument/documentSymbol` is answered from the parser, not from
the last compile, so the outline works on a file that does not compile
-- including one the server has refused to compile because an ancestor
is missing.

`workspace/symbol` and `textDocument/completion` answer from HOL:
theorems of the theories this server loaded, and beyond them any
theory built in the project, read from its `Theory.dat` without being
loaded.  The two are distinguished, because only the first is usable
as it stands: a hit from the second is marked *not an ancestor*, and
using it means adding the theory to `Ancestors` first.  Neither
scans sources that have never been built; declarations of the buffers
you have open are included, so something typed a minute ago is still
findable.

There is no `textDocument/references`.  It was advertised for a long
time with no handler behind it; an honest implementation is not
available, since Poly records references only within the compilation
unit it is compiling and HOL keeps no index of which proofs cite a
theorem.

Then open a `*Script.sml` file.  Diagnostics appear as flymake
underlines; `M-x eldoc` (or `eldoc-mode`) shows hover at point;
`M-.` (`xref-find-definitions`) jumps to definitions; `M-x
eglot-events-buffer` shows the raw traffic.

Compile progress: with `eglot-report-progress` at its default `t`,
the mode-line reads `[eglot:HOL/42%]` and the token/title only appear
in the tooltip.  With `eglot-report-progress` set to `'messages`,
eglot unconditionally echoes `[eglot] <nick> <token>: <title>` on
every progress update — that's an eglot formatting choice, not
something the server can suppress.

### With lsp-mode

Lsp-mode documentation:
<https://emacs-lsp.github.io/lsp-mode/>.  Minimal `init.el`:

```elisp
(add-to-list 'load-path
             "/absolute/path/to/HOL/tools/editor-modes/emacs")
(require 'holscript-mode)

(with-eval-after-load 'lsp-mode
  (add-to-list 'lsp-language-id-configuration
               '(holscript-mode . "holsml"))
  (add-to-list 'lsp-language-id-configuration
               '(holscript-ts-mode . "holsml"))
  (lsp-register-client
   (make-lsp-client
    :new-connection
      (lsp-stdio-connection
       '("/absolute/path/to/HOL/bin/hol" "lsp"))
    :activation-fn (lsp-activate-on "holsml")
    :server-id 'hol-lsp)))

(add-hook 'holscript-mode-hook #'lsp)
(add-hook 'holscript-ts-mode-hook #'lsp)
```

This recipe shares one server across every script under a workspace
root, which is the arrangement described in **One server per buffer**
above: the second file you open gets wrong goals and dead hovers, and
the server will warn you about it.  Only the eglot setup arranges a
server per buffer today.  With lsp-mode, open one file per session, or
give each file its own workspace root.

## Vim / Neovim

The repo's `tools/editor-modes/vim/` mode is a REPL-oriented setup
without LSP client integration.  Two known-good LSP clients.  Both
attach one server per `rootPatterns`/root match, so the caveat in
**One server per buffer** applies to them as it does to lsp-mode.

### With coc.nvim

Coc.nvim: <https://github.com/neoclide/coc.nvim>.  Add to
`~/.config/nvim/coc-settings.json` (open with `:CocConfig`):

```json
{
  "languageserver": {
    "hol": {
      "command": "/absolute/path/to/HOL/bin/hol",
      "args": ["lsp"],
      "filetypes": ["hol4script"],
      "rootPatterns": ["Holmakefile", ".git/"]
    }
  }
}
```

`filetype=hol4script` is what the shipped `filetype.vim` sets for
`*Script.sml`, so the mapping picks up automatically.

### With vim-lsp

Vim-lsp: <https://github.com/prabirshrestha/vim-lsp>.  Add to
`~/.vimrc`:

```vim
let s:hol_bin = '/absolute/path/to/HOL/bin/hol'
if executable(s:hol_bin)
  au User lsp_setup call lsp#register_server({
    \ 'name': 'hol-lsp',
    \ 'cmd': {server_info->[s:hol_bin, 'lsp']},
    \ 'allowlist': ['hol4script'],
    \ })
endif
```

## VS Code

There is no first-party HOL extension for VS Code.  Two paths:

1. **Write a minimal client extension.**  Yeoman scaffold + a few
   lines of `LanguageClient` glue.  Marketplace has several LSP
   sample extensions; adapting one is under an hour.  Rough shape of
   `extension.ts`:

   ```typescript
   import { workspace, ExtensionContext } from "vscode";
   import { LanguageClient, LanguageClientOptions,
            ServerOptions } from "vscode-languageclient/node";

   let client: LanguageClient;
   export function activate(ctx: ExtensionContext) {
     const serverOptions: ServerOptions = {
       command: "/absolute/path/to/HOL/bin/hol",
       args: ["lsp"]
     };
     const clientOptions: LanguageClientOptions = {
       documentSelector: [{ scheme: "file", pattern: "**/*Script.sml" }],
     };
     client = new LanguageClient("hol", "HOL LSP",
                                 serverOptions, clientOptions);
     client.start();
   }
   export function deactivate() {
     return client ? client.stop() : undefined;
   }
   ```

2. **Use a generic-LSP extension** from the marketplace (search "LSP
   client generic").  Quality varies; expect to configure a JSON
   stanza much like coc.nvim's above.

## Troubleshooting

- **No responses at all** — check that `bin/hol.state` exists and
  matches `bin/hol` (`Fail "Saved state was exported from a different
  executable"` on stderr indicates a stale heap; rebuild with
  `bin/build`).
- **Diagnostics appear only after saving** — `$/setConfig`'s
  `elabOn` defaults to `Change` (auto-compile on edit).  Send
  `{"jsonrpc":"2.0","id":N,"method":"$/setConfig","params":{"elabOn":2}}`
  to switch to save-triggered compilation.
- **Client sees garbage on the wire** — capture the eglot events
  buffer / coc log; a genuine framing bug in the server would surface
  as `Content-Length` mismatch or malformed JSON.
- **Tactic errors don't surface** — expected; the fast-oracle path
  skips `tac`.  The pending proof-state work adds a background
  walker that evaluates tactics for `$/getState`; until it lands,
  tactic-level checking still requires a real `Holmake` build.
