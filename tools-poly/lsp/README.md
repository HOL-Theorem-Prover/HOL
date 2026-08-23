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
  `$/setConfig` (elabOn mode, holdep behaviour), `$/eval` (streamed
  arbitrary SML), `$/hol/goalState` (goal-state at cursor — see
  below), `$/cancelRequest`, `$/compileProgress` /
  `$/compileCompleted` / `$/compileInterrupted`.

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
    "position": {"line": <0-based>, "character": <0-based UTF-8 byte offset>}
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
  "error": <string or null>
}
```

- `step` — 0-based tactic-step index at the cursor, counting only
  `Expand` / `ExpandList` steps (structural markers like `>-` /
  `THEN1` don't advance it).
- `goals` — structured per-subgoal render for clients that want to
  format goals themselves.
- `pretty` — the whole state rendered by HOL's `goalFrag.pp_goalstate`
  via the VT100 backend, so bound / free variables carry ANSI colour
  escapes (`\x1B[…m`).  Clients that don't render ANSI can strip the
  escapes with `\x1B\[[0-9;]*m` or fall back to `goals`.
- `error` — non-null when the walker gave up (e.g. wall-clock budget
  exceeded); `goals` / `pretty` are empty and clients should render
  the message in place of the state.  A mid-walk partial state is
  complete for its own step but wrong for the cursor's step, so the
  server refuses to send it and returns `error` instead.  A stderr
  line `goal-state walker exceeded Nms budget; interrupting` is
  also emitted for visibility.

### Client cookbook

- **eglot (shipped in this repo)** — `hol-lsp-show-goal-state` bound
  to `M-h M-g`.  Set `hol-lsp-goals-follow-cursor` non-nil to make
  `*HOL Goals*` auto-refresh on cursor movement (debounced via
  `hol-lsp-goals-follow-delay`).  `hol-lsp--render-goals` runs
  `ansi-color-apply-on-region` on the inserted `pretty` text so the
  bound / free variable colouring survives.
- **VS Code (recipe, not shipped)** — `client.sendRequest("$/hol/goalState", params)`
  returns the response object.  For the simplest path, strip the ANSI
  escapes (regex `\x1B\[[0-9;]*m`) and display `pretty` as plain text
  in a `WebviewPanel`, or ignore `pretty` entirely and render the
  `goals` array structurally.  Keeping the colours requires an
  ANSI-to-HTML converter (e.g. `ansi_up` on npm) plus a small CSS
  palette in the webview.

The server negotiates `positionEncoding: "utf-8"` (LSP 3.17) during
`initialize`, so `position.character` is a byte offset within the
line for both `textDocument/hover` and `$/hol/goalState`.  Clients
that assume the LSP default of UTF-16 will send wrong offsets on
lines containing multibyte characters.

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
;; variant holscript-ts-mode, installs the HOLHEAP-clustered project
;; function, and auto-starts eglot from each mode hook.
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

## Vim / Neovim

The repo's `tools/editor-modes/vim/` mode is a REPL-oriented setup
without LSP client integration.  Two known-good LSP clients:

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
