# HOL4 tree-sitter Emacs mode

A tree-sitter-based major mode for HOL4 `*Script.sml` files —
`holscript-ts-mode`.  Provides syntax highlighting, indentation,
defun navigation, imenu, and structural motion built on an
incremental parse.

The traditional SMIE-based `holscript-mode` remains in place as
a fallback; the `holscript-pick-mode` dispatcher (in the sibling
`../holscript-mode.el`) chooses the tree-sitter mode when the
parser library is available, and falls back to SMIE otherwise.

## Prerequisites

- **Emacs 29+** built with tree-sitter support.  Check with
  `M-: (treesit-available-p) RET` — should return `t`.
- **A C compiler** (`cc` / `clang` / `gcc`).
- **`make`** (for the manual build route below).
- Optional: the [`tree-sitter` CLI][ts-cli], used by the
  Emacs-driven install path.

Windows is not currently supported (per the Makefile).

[ts-cli]: https://github.com/tree-sitter/tree-sitter/releases

## Build the parser library

Two paths — pick whichever fits your setup.

### Route A: Emacs-driven (recommended)

Add to your init file:

```elisp
(require 'treesit)
(add-to-list
 'treesit-language-source-alist
 '(holscript
   "https://github.com/HOL-Theorem-Prover/HOL"
   nil                                                                    ; REVISION (nil = default branch)
   "tools/editor-modes/emacs/tree-sitter/tree-sitter-holscript"))         ; SOURCE-DIR
```

The `treesit-language-source-alist` entries are positional —
`(LANG . (URL REVISION SOURCE-DIR CC C++))`, only URL is required
— not keyword args.

**Emacs 30+ only**: to use an existing local checkout instead of
cloning fresh, put the directory in the URL slot:

```elisp
(add-to-list
 'treesit-language-source-alist
 '(holscript
   "/path/to/your/HOL"
   nil
   "tools/editor-modes/emacs/tree-sitter/tree-sitter-holscript"))
```

Emacs 29 requires a real git URL here — it will clone into a
temporary directory each time.  If you need to build from an
unmerged local branch on Emacs 29, use **Route B** below instead.

Then run `M-x treesit-install-language-grammar RET holscript RET`.
Emacs invokes the `tree-sitter` CLI to generate `parser.c` from
`grammar.js`, compiles the shared object, and installs it under
`~/.emacs.d/tree-sitter/`.  You need the `tree-sitter` CLI on
`PATH` (`brew install tree-sitter` / your package manager /
release from <https://github.com/tree-sitter/tree-sitter/releases>).

### Route B: Build with make, install manually

The Makefile expects the generated `src/parser.c` and
`src/grammar.json` to already exist — those are the output of
`tree-sitter generate` and are gitignored, so a fresh checkout
doesn't have them.

```
cd tools/editor-modes/emacs/tree-sitter/tree-sitter-holscript
tree-sitter generate      # produces src/parser.c and src/grammar.json
make
```

That produces `libtree-sitter-holscript.so` (Linux) or
`libtree-sitter-holscript.dylib` (macOS) in the current directory.
Copy it into a directory Emacs's `treesit` searches:

```
mkdir -p ~/.emacs.d/tree-sitter
cp libtree-sitter-holscript.so ~/.emacs.d/tree-sitter/    # Linux
# or
cp libtree-sitter-holscript.dylib ~/.emacs.d/tree-sitter/ # macOS
```

Emacs also picks up shared objects listed in `treesit-extra-load-path`
if you'd rather not use `~/.emacs.d/tree-sitter/`.

## Wire the mode into Emacs

Add the `tools/editor-modes/emacs/` directory (the parent of this
one) to `load-path`, tell `treesit` where the shared object lives,
and require `holscript-mode`:

```elisp
(add-to-list 'load-path "/path/to/HOL/tools/editor-modes/emacs")

;; Where you installed the shared object.  Not searched automatically
;; on Emacs 29, so this line is mandatory unless the file happens to
;; be on your system's dynamic-linker path.
(add-to-list 'treesit-extra-load-path
             (expand-file-name "tree-sitter" user-emacs-directory))

(require 'holscript-mode)
```

`holscript-mode.el` puts its own sibling `tree-sitter/` subdirectory
on `load-path` for you, registers `holscript-pick-mode` as the
`auto-mode-alist` entry for `*Script.sml` files, and pulls in
`holscript-ts-mode` on demand.

## Verify

Open any `*Script.sml` file and look at the mode indicator at the
bottom of the frame:

- **`HOLScript[ts]`** — the tree-sitter mode is running.  ✓
- **`HOLscript`**    — the SMIE fallback is running.  The shared
                       object is either missing, at an unexpected
                       path, or won't load.

Alternatives:

- `C-h m` (`describe-mode`) — shows the current major-mode symbol.
  `holscript-ts-mode` means tree-sitter is active.
- `M-x treesit-explore-mode` — opens a live parse-tree side buffer.
  It's a no-op when tree-sitter isn't active for the buffer, so a
  visible tree is proof.

## Troubleshooting

If the mode line shows `HOLscript` (no `[ts]`) even after building
and installing the library:

1. `M-: (treesit-language-available-p 'holscript) RET` — if `nil`,
   Emacs can't find the shared object.  Check
   `treesit-extra-load-path` (`M-: treesit-extra-load-path RET`):
   the directory holding `libtree-sitter-holscript.{so,dylib}`
   must be listed there.  On Emacs 29, `~/.emacs.d/tree-sitter/`
   is *not* searched automatically — the `treesit-extra-load-path`
   line in the wiring section above is required.  The filename
   must be exactly `libtree-sitter-holscript.so` (Linux) or
   `libtree-sitter-holscript.dylib` (macOS).

2. `M-: (treesit-language-available-p 'holscript t) RET` returns
   `(nil . REASON)` when loading fails; the REASON tells you why.

   - `version-mismatch NN` — the shared object was generated at
     tree-sitter ABI NN but your Emacs's embedded runtime doesn't
     support that version.  Emacs 29 typically supports ABI ≤ 14;
     newer `tree-sitter` CLIs default to 15+.  Regenerate:
     ```
     cd tools/editor-modes/emacs/tree-sitter/tree-sitter-holscript
     tree-sitter generate --abi 14
     make clean && make
     cp libtree-sitter-holscript.{so,dylib} ~/.emacs.d/tree-sitter/
     ```
     Check your Emacs's exact supported ABI with
     `M-: (treesit-language-abi-version) RET`.

   - `symbol-error` — the file loaded but doesn't export the
     expected `tree_sitter_holscript` symbol.  Regenerate the
     parser from `grammar.js` (`tree-sitter generate`) and rebuild.

   - `not-found` — Emacs still can't find the file on
     `treesit-extra-load-path`.  Recheck step 1.

3. `make clean && make` in
   `tools/editor-modes/emacs/tree-sitter/tree-sitter-holscript`
   forces a fresh rebuild.

4. **macOS only** — if Emacs *crashes* on the first attempt to load
   the dylib (crash report says `Code Signature Invalid` /
   `Namespace CODESIGNING`), macOS is refusing an unsigned dylib
   inside a signed process.  Ad-hoc sign it:
   ```
   codesign --force --sign - ~/.emacs.d/tree-sitter/libtree-sitter-holscript.dylib
   ```
   The `--sign -` gives a placeholder signature that satisfies
   library validation for most Emacs.app builds.  If it still
   crashes, Emacs.app has strict library validation — either
   `sudo codesign --remove-signature /Applications/Emacs.app` or
   switch to an Emacs distribution built with the
   `com.apple.security.cs.disable-library-validation` entitlement.

If you want to force the SMIE mode (e.g. while iterating on the
grammar), swap the `auto-mode-alist` entry or override
`holscript-pick-mode` in your init file.
