# HOL4 for Neovim

A Neovim client for HOL's language server, `bin/hol lsp`
(`tools-poly/lsp`). Open a `*Script.sml` file and the server loads its
ancestors, compiles it as you edit, and reports errors as diagnostics.
On top of standard LSP features (hover, go to definition, completion), this
plugin adds:

- a **goals pane** that shows the goal state at the cursor and follows it
  through a proof
- **eval**, which runs SML in the server's session at the cursor's position
  and shows the output in a float in the middle of the screen
- **theorem search** (`DB.find`-style, by theory, name or term pattern) in a
  [Snacks](https://github.com/folke/snacks.nvim) or
  [Telescope](https://github.com/nvim-telescope/telescope.nvim) picker, or
  `vim.ui.select` with neither
- **proof checking** in the background, with failures as diagnostics, a `✓`
  after each proof that passes, a tally for your statusline, and commands to walk the unfinished proofs
- server control: retry compile, restart, and background proof checking

Syntax highlighting comes from the Vim mode's `hol4script.vim`, one directory
up. No extra work is necessary, it will be used automatically once the plugin is imported.

## Requirements

- Neovim 0.12 or later.
- A built HOL (`bin/hol`). For each script, the plugin runs the `hol` that
  last built the script's directory (from `.hol/make-deps/lastmaker`), falling
  back to the `bin/hol` of the HOL checkout the plugin is in.
- Optional: snacks.nvim or telescope.nvim, for search as you type.

## Installation

The plugin is this directory. With
[lazy.nvim](https://github.com/folke/lazy.nvim):

```lua
{
  dir = '/path/to/HOL/tools/editor-modes/vim/neovim',
  name = 'hol4',
  ft = 'hol4script',
  cmd = 'Hol',
  opts = {},
}
```

Or add the directory to `'runtimepath'` and, optionally, call
`require('hol4').setup()`. Without a `setup()` call, the plugin sets itself up
with the defaults when the first HOL script opens.

See `:help hol4`, which may need `:helptags ALL` first.

Run `:checkhealth hol4` to check the setup. Run from a HOL script, it also
checks the `hol` that script would use, and starts it to catch a stale build.
A lazy-loading plugin manager keeps the plugin off `'runtimepath'` until a
script opens, and `:checkhealth` can't find it before then: open a script
first, or with lazy.nvim run `:Lazy load hol4`.

## Options

```lua
require('hol4').setup {
  -- `hol` for a directory no Holmake has built yet
  hol = '/path/to/HOL/bin/hol', -- default: this checkout's, else `hol`
  check_proofs = false, -- replay every proof in the background
  goals_follow = true, -- goals pane follows the cursor
  -- How long a goal-state walk may run before it is cut off
  -- A slower tactic reports an error instead of a state
  walk_budget_ms = nil, -- default: the server's, 1500
  -- How long proof checking lets one proof run before calling it timed out
  -- 0 for no limit
  proof_timeout_ms = nil, -- default: the server's, 120000
  -- 'snacks', 'telescope' or 'select'; default: the first installed, in that order
  picker = nil,
  -- after a theorem's first line; false for nothing
  marks = { proved = '✓', checking = '⋯', failed = '✗' },
  goals = {
    -- 'right', 'below', or 'auto': right of a window 160+ columns wide
    position = 'auto',
    width = nil, -- columns on the right; default: a third of the window
    height = 15, -- lines below
    -- the pane's own keys; a key, a list, or false for none
    keys = { info = 'K', close = 'q' },
  },
  eval = {
    border = 'rounded',
    max_width = 100,
    max_height = 15,
    enter = true, -- move the cursor into the float as it opens
    keys = { close = { 'q', '<Esc>' } },
  },
  search = { limit = 200 }, -- most results a theorem search asks for
  hover_width = nil, -- columns hovers are laid out to. Defaults to the server's
}
```

## Commands

| Command | |
|---|---|
| `:Hol goals` | Toggle the goals pane |
| `:Hol refresh` | Refresh the goals at the cursor |
| `:Hol eval [code]` | Evaluate SML at the cursor: with a range, the selection; with neither, prompt |
| `:Hol search [name\|term]` | Search theorems by name (the default) or by term |
| `:Hol cancel` | Cancel the running eval |
| `:Hol retry` | Recompile after a missing ancestor has been built |
| `:Hol restart` | Restart this buffer's server (needed after rebuilding a loaded ancestor) |
| `:Hol checkproofs [on\|off\|toggle]` | Background proof checking |
| `:Hol nextproof`, `:Hol prevproof` | Move to the next or previous proof that's unchecked or went wrong |
| `:Hol follow [on\|off\|toggle]` | Whether the goals pane follows the cursor |

The goals pane's title shows the theorem, the step, and how long that step
took. The pane has two keys of its own: `K` shows the type of the symbol
under the cursor (from the goal state; it isn't LSP hover), and `q` closes the
pane. In the eval float, `q` or `<Esc>` closes it. Both are set by the `keys`
options.

## Theorem search

There are two searches. **By name** (`:Hol search name`), each word is part
of the theorem's name, and a term pattern in double backquotes narrows it
further:

```
ADD COMM
  arithmetic$ADD_COMM        ⊢ ∀m n. m + n = n + m

'arithmetic' MULT ASSOC
  arithmetic$MULT_ASSOC      ⊢ ∀m n p. m * (n * p) = m * n * p
  arithmetic$MULT_ASSOC_COMM ⊢ ∀m n p. m * (n * p) = m * p * n
  arithmetic$MULT_COMM_ASSOC ⊢ ∀m n p. m * (n * p) = n * (m * p)

LESS EQ ``_ + _``
  arithmetic$ADD_MONO_LESS_EQ ⊢ ∀m n p. m + n ≤ m + p ⇔ n ≤ p
  arithmetic$LESS_EQ_ADD      ⊢ ∀m n. m ≤ m + n
  arithmetic$LESS_EQ_EXISTS   ⊢ ∀m n. m ≤ n ⇔ ∃p. n = m + p
```

**By term** (`:Hol search term`), the prompt is a term pattern, and a name
fragment in double quotes narrows it further:

```
x * (y + z)
  arithmetic$LEFT_ADD_DISTRIB ⊢ ∀m n p. p * (m + n) = p * m + p * n
  numpair$tri_formula         ⊢ tri n = n * (n + 1) DIV 2
  numpair$twotri_formula      ⊢ 2 * tri n = n * (n + 1)

MAP f (MAP g l)
  list$MAP_COMPOSE ⊢ ∀f g l. MAP f (MAP g l) = MAP (f ∘ g) l
  list$MAP_MAP_o   ⊢ ∀f g l. MAP f (MAP g l) = MAP (f ∘ g) l

x + y = y + x "COMM"
  arithmetic$ADD_COMM ⊢ ∀m n. m + n = n + m
```

In both, `'theory'` keeps to one theory. In a term pattern a variable (`x`,
`_`) matches anything and a constant only itself; the pattern is read in the
current script's context, so a constant that script doesn't have (`+` before
arithmetic) is a variable too, and matches far more than intended.

## Keymaps

The plugin defines none. A visual-mode mapping should call the Lua functions,
which use the exact selection:

```lua
vim.api.nvim_create_autocmd('FileType', {
  pattern = 'hol4script',
  callback = function(ev)
    local hol = require('hol4')
    local function map(mode, lhs, rhs)
      vim.keymap.set(mode, lhs, rhs, { buffer = ev.buf })
    end
    map('n', '<localleader>g', require('hol4.goals').toggle)
    map('n', '<localleader>s', hol.eval_line)
    map('v', '<localleader>s', hol.eval_visual)
    map('n', '<localleader>S', hol.eval_prompt)
    map('n', '<localleader>f', require('hol4.search').by_name)
    map('n', '<localleader>m', require('hol4.search').by_term)
  end,
})
```

## Proof checking

Elaboration doesn't run tactics, which is what makes it fast, so a proof is
taken on trust until it's checked. With `check_proofs` on, a pool of workers
replays each proof in the background: that costs what the proofs cost.

After the theorem's first line, proofs that pass get a `✓`, proofs being
checked a `⋯`, and proofs that failed or timed out a `✗`. With checking off, a theorem gets a `✓` when the goals pane
shows its proof solved (the cursor after its last tactic); an edit takes the
ticks off the proof it's in and every proof after it.

`require('hol4').status()` returns a tally for a statusline, such as `⊢12/14!1`
(12 of 14 checked, 1 went wrong), and an empty string when nothing is left to
say. The `User Hol4ProofStates` autocommand fires when it changes. With
lualine:

```lua
{
  function() return require('hol4').status() end,
  cond = function() return package.loaded['hol4'] ~= nil end,
}
```

## Lua API

`require('hol4')`: `setup(opts)`, `eval(code, bufnr?, pos?)`, `eval_line()`,
`eval_visual()`, `eval_prompt()`, `cancel()`, `retry_compile()`, `restart()`,
`set_check_proofs(on)`, `set_goals_follow(on)`, `status(buf?)`,
`next_proof()`, `prev_proof()`, and the `check_proofs` flag.

`require('hol4.goals')`: `open()`, `close()`, `toggle()`, `refresh()`,
`is_open()`, and the `follow` flag.

`require('hol4.search')`: `by_name()`, `by_term()`, and
`open { mode?, limit?, picker? }`.

A position `pos` is `{row, col}` with a 1-based row and a 0-based byte column,
as `nvim_win_get_cursor` returns.

## Highlights


| Group | Default link | |
|---|---|---|
| `Hol4GoalsBound` | `@variable.parameter` | bound variables |
| `Hol4GoalsFree` | `@variable.builtin` | free variables |
| `Hol4GoalsConst` | `@function` | constants |
| `Hol4GoalsTyvar` | `@type` | type variables |
| `Hol4GoalsTitle` | `WinBar` | the pane's title, focused or not |
| `Hol4GoalsApplying` | `Comment` | `Applying tactic…` while a slow one runs |
| `Hol4ProofOk` | `DiagnosticOk` | a proof's `✓` |
| `Hol4ProofChecking` | `Comment` | a proof's `⋯` while it's checked |
| `Hol4ProofFailed` | `DiagnosticError` | a proof's `✗` |
| `Hol4EvalText` | `NormalFloat` | an error's text |
| `Hol4EvalError` | `DiagnosticError` | an error's first line |
| `Hol4EvalWarning` | `DiagnosticWarn` | a warning's first line |
| `Hol4EvalLabel` | `@label` | `Function:`, `Reason:` and so on |
| `Hol4EvalType` | `@type` | the type in a type error |
| `Hol4EvalOrigin` | `@function` | the function that raised a `HOL_ERR` |
| `Hol4EvalDetail` | `Comment` | where it was raised |
