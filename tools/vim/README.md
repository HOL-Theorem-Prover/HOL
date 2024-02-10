# "HOL mode" for Vim.

Send the visually selected region of a Vim buffer to a HOL interactive session.

Feedback to: Ramana Kumar <ramana(at)member.fsf.org>

## Dependencies

HOL4, PolyML, Vim, and a POSIXly correct tail.

Uses the Thread structure from PolyML, and Unix and Posix structures from the
standard basis. Could be ported to another ML providing similar functionality.

## Contents

All files are located under tools/vim

- `vimhol.sml`: The extra code loaded with the prelude for a Vimhol session.
- `hol.vim`: Vim script to prepare a Vim buffer for sending to HOL.
- `*src`: Used to generate the above during the HOL build process.
- `holabs.vim`: Vim abbreviations for Unicode characters. (Optional.)
- `hol-config.sml`: Template hol-config file for automatically loading Vimhol
  when hol starts.
- `filetype.vim`: Template filetype.vim for automatically running hol.vim when
  vim starts.
- `vimhol.sh`: Wraps hol and vim side-by-side in tmux. Below you find the
  description of its usage. See below for an alternative approach of running
  an hol interactive session within vim.
- `hol4script.vim`: Syntax highlighting definitions for HOL4 scripts.
- `README.md`: Documentation. (This file.)

## Quickstart

1. Add the contents of `hol-config.sml` to your `~/.hol-config.sml` file
2. Add the contents of `filetype.vim` to your `~/.vim/filetype.vim`
3. Copy `hol4script.vim` to your `~/.vim/syntax/hol4script.vim`
4. Run hol to start the HOL session (only necessary when using vim without
   support for terminal buffers)
5. Run vim and open a HOL script
6. Select some SML value or declaration and type `hs` to send it to the HOL
   session. See below for more key mappings

If you don't have `filetype on` in vim, then this won't work. In that case, you
should forget step 2 and source `hol.vim` manually in step 3. To turn filetype
on, you can add `filetype on` to your `~/.vimrc`. Similarly, syntax
highlighting requires `syntax on`.

## WARNING

Use of HOL mode may cause your Vim to appear frozen and unresponsive. This
happens when the plugin is trying to write to a fifo that is not being read.
The remedy is to read the fifo: either start hol (if everything is set up
correctly) or simply cat `$(HOLDIR)/tools/vim/fifo` (or `$(VIMHOL_FIFO)` if you
are using a custom fifo path).

## HOL interactive session inside the vim editor

Neovim and some versions of vim can run the interactive HOL session (HOL repl) in a terminal buffer within the editor, right next to a file buffer.
Vim supports this feature if `:echo has('terminal')` prints `1`, neovim if `:echo exists(':terminal')` prints a non-zero value.
For the supported versions, this plugin offers additional keyboard mappings to open and close a terminal buffer running hol, as documented below in the section *key mappings for the HOL repl buffer*.
Whenever a new HOL interactive session is started, a new unique fifo is created.

The `hol` executable that is run in the interactive session is determined in the following order:
1. If `Holmake` was previously run in the current working directory of the loaded theory file before (and thus the file `.HOLMK/lastmaker` exists) the plugin attempts to run the `hol` that is relative to the previously used `Holmake`.
2. Otherwise, if the `$HOLDIR` environment variable is set the plugin attempts to run `$HOLDIR/bin/hol`.
3. Otherwise, simply `hol` will be run (expecting `hol` to be in the `$PATH` environment variable).

Read more in the documentation on [vim terminal buffers](https://vimhelp.org/terminal.txt.html) (or [neovim terminal buffers](https://neovim.io/doc/user/nvim_terminal_emulator.html)).

## Key mappings

(These are all set up in `hol.vim`)

The following commands work in visual mode:

Command  | Description
:------- | :------------------------------------
`hs`     | Send region to HOL.
`hu`     | Send region to HOL in quiet mode.
`hL`     | Send region to be split into words and each word `load`ed.
`hl`     | Same as above, but also send the region as a command afterwards.
`hg`     | Send region (should be a quotation) to `g`, to start a new proof.
`hG`     | Send region to `new_goalstack` after quoting it, to start a new proof. Any trailing `Proof[...]` modifiers are passed to HOL too.
`he`     | Send region (should be a tactic) to `e`, to expand a tactic.
`hS`     | Send region (should be a quotation) as a new subgoal.
`hF`     | Send region (should be a quotation) to be proved sufficient then proved.
`hP`     | Send region (should be a list of quotations) to select and rename a goal to match the given patterns.

If a visual mode command above is given in normal mode, the region will be the
line containing the cursor.

The following commands work in normal mode (only):

Command     | Description
:---------- | :-----------------------------------
`<count>hR` | Rotate subgoals `<count>` times (default 1).
`<count>hb` | Back up proof `<count>` times (by calling `b`) (default 1).
`<count>hd` | Drop `<count>` proof attempts (by calling `d`) (default 1).
`hp`        | Print the proof manager status (by calling `p`).
`hr`        | Restart the current proof (by calling restart).
`hv`        | Save the proof state (by calling save_proof).
`<count>hB` | Back up to the <count>th last save point (by calling Backup) (default 1).
`hc`        | Interrupt execution (of whichever of the things sent is running).
`ht`        | Select a quotation, including the  `` ` `` delimiters. Find `` ` `` left of (or under) cursor and select to next `` ` ``.  Also works for Unicode single quotes (`‘` and `’`).
`hT`        | Select a term: same as above, but with ``` `` ``` delimiters. (Or Unicode `“` and `”`.)
`ha`        | Select the previous (or if within current) `Theorem` or `Triviality` statement, including its `Proof` keyword and associated modifiers.
`hh`        | A normal h (usually means move cursor left). This one works in both normal and visual modes.
`hy`        | Toggle HOL's show types trace.
`hn`        | Toggle HOL's `PP.avoid_unicode` trace.

## Key mappings for the hol terminal buffer

For the HOL repl hosted by vim the following commands work in normal mode of
any `*Script.sml` file:

Command     | Description
:---------- | :-----------------------------------
`hx`        | Open a HOL session inside (neo)vim at the path of the currently edited file.
`hX`        | Close the HOL session.
`hw`        | Send region (visual and normal mode). Writes directly into the HOL session buffer and does not need a fifo.

The terminal buffer that is hosting the HOL repl can be navigated as usual (if in normal mode).
In vim, to leave insert mode of a terminal buffer and return to Terminal-Normal mode press `CTRL-\ CTRL-N`, as documented in [`:help terminal-typing`](https://vimhelp.org/terminal.txt.html#terminal-typing).

## Automatic stripping

`hL` and `hl` don't `load` these words: `local` `open` `in` `end.`

`hg` strips commas from the end of the region.

`hS` strips everything including and after the first `by` in the region, if any.
`hF` strips everything including and after the first `suffices_by` in the region, if any.

`he` and `hP` strip these tokens from the ends of the region

- start: `)` `]` `[`
- end:   `(` `[`
- both:  `,` `THEN` `THENL` `THEN1` `<<` `>>` `++` `\\` `by`

## Leading string

Vimhol uses `<LocalLeader>` as the leading string for all commands.
We have assumed above that `<LocalLeader>` is set to `h`.
You can change the key sequence used to signal the start of a Vimhol command by
setting the variable maplocalleader before loading hol.vim.
See filetype.vim for an example (by default, it is set there to "h").

## Unicode

An alternative to the abbreviations described below are built-in Vim digraphs.
See `:help digraph`. Briefly, type `CTRL-K <char1><char2>` to get a special
character. If you set the `digraph` option, you can enter them with
`<char1><BS><char2>` too. Digraphs have the advantage of being acceptable in
normal mode for the `f` (and related) commands.

The codes for common HOL Unicode characters are listed in holabs.vim as
comments. `NOTIN` (∉) doesn't seem to be built in to Vim, but you can add
a mapping with `:digraph (+ 8173` (this is done in holabs.vim too).

Abbreviations:
- The `holabs.vim` file contains abbreviations from ASCII strings to Unicode
  strings.
- Examples: `<>` to `≠`, and `UNION` to `∪`. Generally, we use the ASCII name
  of the HOL constant.
- When you type the ASCII, you get the Unicode.
- To turn unicode on, source `holabs.vim`.
- You can source `holabs.vim` automatically by uncommenting the line copied
  from `filetype.vim`.
- Sometimes might need `CTRL-]` or `ESC` or space after an abbreviation to make
  it happen.
- To avoid an abbreviation at one point, type `CTRL-V` after it
- During an editing session, use `:abc` to stop all abbreviation key maps.
  (Removes non `holabs.vim` stuff too.)
- Undo abbreviations in selected text with `:call HOLUnab()` in visual mode.

## Multiple sessions via different fifos

As explained in the next section, communication between HOL and Vim is done via
a fifo that is by default located in `$HOLDIR/tools/vim/fifo`. If you run
multiple HOL sessions sharing the same fifo, then the session that receives
input from Vim (sending to that fifo) is unpredictable, and hence not
recommended.

However, a custom fifo path can be used by setting the environment variable
`$VIMHOL_FIFO` with an absolute path to a fifo (it will be created if it does
not exist). This environment variable instructs both HOL and Vim. Set
`$VIMHOL_FIFO` to one path when you start one pair of a HOL and a Vim session,
and in another environment set it to a different path, then you can run two
instances of Vimhol in parallel without interference.

## Architecture, and the Vimhol structure

Vim sends short commands to `tools/vim/fifo` (or `$VIMHOL_FIFO`) containing the
names of temporary files. Vim writes the real code to be run to those temporary
files. Vimhol `use`es and deletes the temporary files in the order that their
names were received.

Vimhol runs four threads in total.
1. Main thread, which accepts input from stdIn and displays output in the
   terminal.
2. Tail thread, which is just tail following the end of `tools/vim/fifo` for
   commands from Vim.
3. Polling thread, which waits for and reads the output of the tail thread. The
   polling thread automatically starts the tail thread and the running thread
   when it needs to.
4. Running thread, which runs the code from Vim.
   The running thread is the one interrupted by `hc`.

In the main thread, the Vimhol structure will be in scope, containing the following values.
They're probably not useful except for debugging.

Value                         | Description
:---------------------------- | :-----------------------------------------
`pActive : unit -> bool`      | whether the polling thread is active
`rActive : unit -> bool`      | whether the running thread is active
`stopTail : unit -> unit`     | kill the tail thread
`restartTail : unit -> unit`  | restart the tail thread
`stop : unit -> unit`         | stop the polling and running threads
`restart : unit -> unit`      | restart the polling thread
`keepFiles : bool ref`        | don't delete temporary files (default: false)
`quiet : bool ref`            | don't print warn/info messages (default: false)
`queue : Vimhol.Queue.t `     | queue containing names of temporary files
`removeQueue  : unit -> unit` | delete all the files in the queue (respects keepFiles)
`fifoPath  : string`          | the fifo path being used by this session

`tools/vim/fifo` (or `$VIMHOL_FIFO`) is generated by vimhol whenever it doesn't
exist.  Temporary files are generated and should be automatically removed when
keepFiles is false.

## `vimhol.sh` script

The `vimhol.sh` bash script shall give an easier start to using hol and vim
with the above described vimhol mode. It places an editor of vim flavour (e.g.
vim or neovim) next to an instance of hol, wrapped within tmux.

The script requires:

- tmux, a terminal multiplexer.
- vim terminal editor. If desired set the `$EDITOR` environment variable to any
  other editor of the vim flavour.
- optionally `rlwrap`, a readline wrapper, for easier interaction with hol.
  By default `rlwrap` remembers the history of commands previously typed on the
  hol command prompt.

Hereafter, `$HOLDIR` abbreviates the location to the root directory of the HOL
sources.

The script `vimhol.sh` is called as
```
$HOLDIR/tools/vim/vimhol.sh $HOLDIR/src/coalgebras/*Script.sml
```

The above command opens the coalgebra theory files in the editor as declared by
the environment variable `EDITOR`, defaulting to vim. An instance of hol
(started from the first argument file's directory) is shown on the side. vim
and hol are connected by a unique fifo pipe used for example to set a proof
goal or sending tactics to hol. All available commands of the loaded vim
plugin, are documented above

The vimhol session may be quit by `Ctrl-b` followed by `Ctrl-q` (or if
configured differently tmux' prefix key followed by `Ctrl-q`). Permanently, it
is not recommended to quit the session like this, as vim might complain about
existing swap files, when opening the same files again. Make sure to save your
work. When quitting, the fifo pipe is deleted by tmux hooks (when not using the
configured `Ctrl-q` shortcut).

If the script is called in an environment where `HOLDIR` is set, then the hol
at the path `$HOLDIR/bin/hol` is run, otherwise it executes hol from the same
hol directory tree as vimhol.

For permanent usage you may add an alias to the script in the shell
configuration (e.g. in `~/.bash_profile`).
```
alias vimhol="$HOLDIR/tools/vim/vimhol.sh"
```
Provided that that the variable `$HOLDIR` is set, this makes a `vimhol` command
available, which can be called as in
```
vimhol $HOLDIR/src/coalgebras/*Script.sml
```

