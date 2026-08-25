# Using HOL4 from Visual Studio Code

This guide sets up the HOL4 extension for VS Code so that, as you write
a proof, VS Code shows you the current goal in a side pane and
underlines errors as you type.

It is written for someone who has used VS Code before — say, for
Python — but who has not built a VS Code extension and does not want
to become an expert in doing so.  Every command is given in full.  You
should be able to follow it start to finish in about fifteen minutes,
most of which is waiting.

## What you get

- **A HOL Goals pane.**  Put your cursor anywhere inside a
  `Proof … QED` block and the pane shows the goal as it stands *at
  that point in the proof* — what the tactic under your cursor is
  about to work on.  Move the cursor and the pane follows.
- **Errors as you type**, underlined in the file and listed in the
  Problems panel, without running `Holmake` by hand.
- **Hover information**: rest the pointer on an identifier to see its
  type, taken from a real HOL session rather than guessed.

## Before you start

This guide assumes you already have:

- **VS Code**, version 1.75 or later (any version from 2023 onwards).
- **HOL4, already built**, from a recent `develop`.  You must be able
  to run `bin/hol` in your HOL directory and get a HOL prompt.

You also need one thing you may not have yet:

- **Node.js**, version 20 or later.  This is only needed to *build*
  the extension; it plays no part in running HOL.  Check whether you
  have it by opening a terminal and typing:

  ```
  node --version
  ```

  If that prints something like `v20.11.0` or higher, you are fine.
  If it says "command not found", install Node from
  <https://nodejs.org> (take the "LTS" download) and try again.

Throughout, replace `/path/to/HOL` with the actual location of your
HOL directory — the one containing `bin/hol`.  If you are not sure
where that is, run `echo $HOLDIR`; if that prints nothing, find the
directory that has `bin/hol` inside it.

## Step 1 — Download the extension's source code

The HOL4 VS Code extension lives in its own repository, separate from
HOL itself.

**Important:** the LSP support is on a branch called
`lsp-integration`, *not* on the default `main` branch, and it is not
in the version published on the VS Code Marketplace.  So installing
"HOL4 mode" from the Marketplace, or cloning and stopping there, will
not give you the goals pane.  You must switch to that branch.

Open a terminal, go somewhere sensible to keep the code (your home
directory is fine), and run:

```
git clone https://github.com/HOL-Theorem-Prover/hol4-vscode.git
cd hol4-vscode
git switch lsp-integration
```

To confirm you are on the right branch:

```
ls src/lspClient.ts
```

If that prints `src/lspClient.ts`, you have the right code.  If it
says "No such file", the `git switch` did not take effect — re-run it
and read any error message.

## Step 2 — Build the extension

The extension is written in TypeScript and has to be translated into
JavaScript before VS Code can run it.  Two commands, from inside the
`hol4-vscode` directory:

```
npm install
npm run compile
```

`npm install` downloads the libraries the extension depends on (this
needs an internet connection, and takes a minute or two the first
time).  `npm run compile` does the translation, and prints nothing at
all if it succeeds — silence is success here.

You should now have a directory called `out` containing files ending
in `.js`.  Check with:

```
ls out/extension.js
```

## Step 3 — Install it into VS Code

VS Code loads extensions from a folder in your home directory.  You
install this one by putting a link to your built copy there.

On **macOS or Linux**:

```
mkdir -p ~/.vscode/extensions
ln -s "$(pwd)" ~/.vscode/extensions/hol4-mode-dev
```

On **Windows**, copy the whole `hol4-vscode` folder into
`%USERPROFILE%\.vscode\extensions\` instead.

Using a link rather than a copy means that when you later update the
extension (Step 8), VS Code picks up the new version with no further
installation.

Now **quit VS Code completely and start it again** — reloading a
window is not enough for a newly installed extension.

### Alternative: try it without installing

If you would rather test before installing, open the `hol4-vscode`
folder in VS Code and press `F5`.  That launches a second VS Code
window with the extension active.  It is a good way to check things
work, but the extension is only alive in that second window, and you
have to press `F5` again every time — so do the install above for
everyday use.

## Step 4 — Tell the extension where HOL is

The extension needs to know your HOL directory so it can run
`bin/hol`.  Either of these works; pick one.

**Option A — set `HOLDIR` in your environment.**  If you already have
`HOLDIR` set (many HOL users do), there is nothing to do.  Check with
`echo $HOLDIR`.

One wrinkle: VS Code only sees environment variables that were set
when it started.  If you launch VS Code by clicking its icon rather
than by typing `code` in a terminal, it may not see `HOLDIR` even
though your terminal does.  If that bites you, use Option B.

**Option B — set it in VS Code's settings.**  This always works.  Open
the Command Palette (`Ctrl+Shift+P`, or `Cmd+Shift+P` on macOS), type
"Preferences: Open User Settings (JSON)", and add:

```json
{
    "hol4-mode.holdir": "/path/to/HOL"
}
```

Save the file.

## Step 5 — Open a HOL file and check it is working

Use **File → Open Folder** to open the *directory containing the
theory file you want to work on* — for example `examples/lambda` or
your own project directory.  Opening a single file on its own is not
enough: HOL needs the surrounding directory to find the theories your
file depends on.

Now open a `*Script.sml` file in that folder.

Two things tell you the extension has connected:

1. **The status bar**, bottom-left, reads `HOL LSP`.
2. **HOL starts compiling your file.**  On a large file this takes a
   few seconds, and any errors then appear underlined in the editor
   and listed in the Problems panel (`Ctrl+Shift+M`).

If the status bar says `HOL LSP: exe missing` or `no executable`,
Step 4 has not taken effect — see Troubleshooting.

## Step 6 — Open the HOL Goals pane

Press **`Ctrl+H Ctrl+G`** (on macOS, `Cmd+H Cmd+G`).

That is a *chord*: hold `Ctrl` and press `H`, release, then hold
`Ctrl` and press `G`.  If nothing happens, use the Command Palette
instead and run **"HOL: Toggle HOL Goals pane"** — that always works,
and is worth knowing anyway.

A pane titled **HOL Goals** opens beside your file.  At first it says:

> Move the cursor into a Proof … QED body to see goals.

Do that — click anywhere inside a `Proof … QED` block — and it fills
in with the goal at that point.

## Step 7 — Reading the pane

Move the cursor down through a proof, one tactic at a time, and watch
the pane.  The rule is:

> The pane shows the state that the tactic **under the cursor** is
> about to act on.

So placing the cursor on a tactic shows you the goal *before* it runs;
moving past it to the next line shows the result.  This is the same
mental model as stepping through a proof interactively, except that
you step by moving the cursor and nothing is ever "left running".

Assumptions are listed above a horizontal line, numbered from 0, with
the goal below it.  When a tactic creates several subgoals, they are
all shown in order.

Two things worth knowing:

- Inside `‘tm’ by (tac)`, putting the cursor in the `tac` part shows
  you the *new subgoal* `tm` — the thing that `tac` has to prove — not
  the outer goal.
- If a tactic fails to run, the pane says so at the top with a ⚠ and
  shows the last state it reached.  That tells you *where* the proof
  stopped making sense.

## Step 8 — Keeping it up to date

The extension is on a development branch, so it changes.  To update:

```
cd ~/hol4-vscode
git pull
npm install
npm run compile
```

Then restart VS Code.  (If you installed with a link in Step 3, there
is nothing else to do.)

If you have updated HOL itself, you do not need to rebuild the
extension — but you should restart the language server so it picks up
the new HOL.  Command Palette → **"HOL: Restart LSP server"**.

## Troubleshooting

**The status bar shows `HOL LSP: exe missing` or `no executable`.**
The extension cannot find `bin/hol`.  Check that
`/path/to/HOL/bin/hol` really exists and is executable.  If it does,
set the path explicitly in your settings JSON:

```json
{
    "hol4-mode.lsp.executable": "/path/to/HOL/bin/hol"
}
```

**"HOL4 mode: HOLDIR environment variable not set".**
Step 4 did not take.  Use Option B (the settings file) — it does not
depend on how VS Code was launched.

**No goals pane, no errors, no status bar entry.**
Check the extension is loaded at all: Command Palette →
"Developer: Show Running Extensions" should list "HOL4 mode".  If it
does not, VS Code has not picked up your installation — confirm the
link or copy in Step 3, and make sure you fully quit and restarted VS
Code rather than reloading the window.

**Errors appear that `Holmake` does not report.**
Make sure the folder you opened is the one containing your theory
file, and that its dependencies have been built with `Holmake` at
least once.  The extension compiles your file in memory, but it still
needs the theories it imports to exist on disk.

**The pane says "Compile in progress — goal state pending".**
HOL is still working through your file.  Wait for it; on a long file
the first compile can take a while.

**The pane says "No goal state at this position".**
Your cursor is not inside a `Proof … QED` block.  This is normal
between theorems.

**Seeing the raw conversation with the server.**
Command Palette → **"HOL: Show LSP output channel"** shows what the
extension and HOL are saying to each other.  Worth including if you
report a problem.

## If you want to report a problem

Issues with the extension itself go to
<https://github.com/HOL-Theorem-Prover/hol4-vscode>; issues with the
goal states or the errors reported go to
<https://github.com/HOL-Theorem-Prover/HOL>.  In both cases, say which
HOL commit you built and paste the contents of the LSP output channel.

The protocol the extension and HOL speak to each other is documented
in [`README.md`](README.md) in this directory, if you ever need it.
