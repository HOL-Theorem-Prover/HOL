---
title: LSP Server usage
author: Mario Carneiro
numbersections: yes
---

# LSP server

The [Language server protocol](https://microsoft.github.io/language-server-protocol/) is a standard protocol by Microsoft used for communicating between "language servers" which provide contextual language-specific information about files and "clients" or text editors. LSP client implementations exist for VSCode, Vim, Emacs among others so this makes a convenient common point for implementing HOL specific behaviors.

## Usage

One server serves one theory script, and this is a contract rather
than a limitation awaiting work.  The process binds to the first
`*Script.sml` it is given and never releases it, and it declines to
compile any other file: loading a theory *seals* it
(`Theory.load_complete` → `KernelSig.sealed_ref`, deliberately outside
the snapshot machinery as a soundness gate), so an ancestor loaded for
one file can be neither re-read nor withdrawn for a second.

What follows from that:

* Per-file state — buffers, versions, diagnostics — is isolated by
  URI.  HOL's state — `Context`, the sealed set, `Meta.loadedMods` —
  is process-global and is not.  Two files edited in two servers
  cannot affect each other's answers; two files in one process would
  corrupt each other, which is why the second is refused.
* Dependencies are consumed as built artifacts, loaded at most once
  per process.  Rebuilding one does not reach a running server;
  restart it.  A dependency that was *missing* is re-read, which is
  what `$/hol/retryCompile` is for.
* `$/setConfig` is process-wide, and `$/eval` runs in the shared
  process state with no snapshot bracket, so it can perturb the
  file's compiles.

To start a server, use `hol lsp`. This should be run in the project root (containing the files you are editing).

It will communicate using the LSP format (on stdio). This covers most of the basic operations of a language server, in particular:

* Initialization/shutdown
* Opening, modifying, closing files
* Hover and go to definition

### Initialization

The client sends a message describing the features it supports, and the LSP server responds by describing what features it has enabled.

This LSP server also supports the `$/setConfig` command for setting additional HOL-specific features.

### File operations

When opening or modifying a file, the server will compile the file and report any warnings or errors in a `Diagnostic` notification. It is also responsible for caching intermediate states in order to minimize the amount of work needed to update the list of diagnostics.

## Extensions

In addition to the usual LSP commands, the server supports the following extensions:

* Notification `$/cancelRequest`:

  This is a "standard" extension that allows cancelling a pending request. This is useful in particular for the `$/eval` command to terminate a long-running user evaluation.

  Parameters:
  * `id: integer | string` - The request id to cancel

* Request `$/setConfig`: This sets additional global state for the server.

  Parameters:
  * `elabOn?: ElabOn` where `enum ElabOn { None = 0, Change = 1, Save = 2 }` (default: `Change`)

    This controls whether elaboration/compilation should be triggered after every modification to the file, on save, or not at all.

* Request `$/eval`: This runs a chunk of HOL text, to allow for a similar behavior as `hol repl`.

  Parameters:
  * `uri: URI` - The file (or virtual path) associated to this chunk
  * `code: string` - The HOL text to compile
  * `incr?: Incr` where `enum Incr { None = 0, Chunk = 1, Stream = 2 }` (default: `None`)
  * `holdep?: HoldepKind` where `enum HoldepKind { None = 0, Quiet = 1, List = 2 }` (default: `Quiet`) - controls whether it should first call `holdep` to collect and preload any `open`s and other qualified names, and whether to print bindings (`List`) or not (`Quiet`).

  Depending on the options set, it will send various notifications back, in the following order:

  * If `holdep = List`, it will give a `$/eval/holdep` notification:
    * `uri: URI` - the original file
    * `id: integer | string` - the current request
    * `files: [string]` - The list of modules to load

  * It then loads the modules (if `holdep != None`).
  * If `holdep = List`, it will give a `$/eval/holdepCompleted` with the same `uri`,`id` when loading is complete
  * It then runs the code and reports results:
    * If `incr = None`, then the final response of the request is a `[report]` list containing all of the errors, warnings, etc.
    * If `incr = Chunk`, then it returns `null` immediately, but it compiles asynchronously, sending each report in a `$/eval/P` notification:
      * `id: integer | string` - the current request
      * `pos: Range` - the chunk of the text that was evaluated
      * `out: [Report]` - the results from this chunk
    * If `incr = Stream` then each report is sent as soon as possible in a `$/eval/1` notification:
      * `id: integer | string` - the current request
      * `out: Report` - the report

  The `Report` object is a possible output of the compiler:
  ```ts
  type Report = ErrorReport | CompilerOutReport | ToplevelOutReport | CompileProgressReport | { kind: "compileCompleted" } | { kind: "interrupted" };
  interface ErrorReport {
    kind: "error";
    hard: bool; // true = error, false = warning
    pos: Range;
    msg: string;
  }
  interface CompilerOutReport {
    kind: "compilerOut";
    pos: Range;
    body: string;
  }
  interface ToplevelOutReport {
    kind: "toplevelOut";
    pos: Range;
    body: string;
  }
  interface CompileProgressReport {
    kind: "compileProgress";
    pos: Range;
  }
  ```
  An asynchronous compile is always terminated by `"compileCompleted"` or `"interrupted"`.

* The `$/compileProgress` notification is sent during an asynchronous compile caused by a file open or modification event.
    * `uri: URI` - the file being compiled
    * `pos: Range` - the chunk of the text that was evaluated

* The `$/compileCompleted` notification is sent when an asynchronous compile caused by a file open or modification event is completed.
    * `uri: URI` - the file being compiled

* The `$/compileInterrupted` notification is sent when an asynchronous compile caused by a file open or modification event is interrupted.
    * `uri: URI` - the file being compiled

* **Position encoding.**  The server's own offsets are bytes, so it asks
  for `utf-8` when the client's `general.positionEncodings` offers it
  (eglot offers `["utf-32", "utf-8", "utf-16"]`) and answers `utf-16`
  otherwise, converting every `character` it reads or writes.  A client
  that offers nothing gets `utf-16`, which is what the spec says its
  silence means.  Declaring `utf-8` regardless is not a way of getting
  it: `vscode-languageclient` advertises only `utf-16` and throws on any
  other answer.

* The `$/compileBlocked` notification is sent instead of compiling a file
  whose declared dependencies are not available.  A file that names an
  ancestor or library it cannot get has nothing to be elaborated against,
  so the server compiles none of it, and answers `null` to
  `$/hol/goalState` for it.  Availability is decided by looking the
  declared structure up in the namespace, so it covers a dependency that
  loads without binding the name the header opens, and a retry that
  plans nothing because the module is still marked in
  `Meta.loadedMods` -- neither of which raises anything to catch.
  The failures themselves are published as
  diagnostics, positioned on the names in the header that asked for them;
  no `$/compileProgress` or `$/compileCompleted` follows.

  The block is cleared by an edit that changes the file's declared
  dependency list -- the `Ancestors` and `Libs` entries of its `Theory`
  header, plus the identifiers of any leading top-level `open` -- or by
  the `$/hol/retryCompile` notification below.  Nothing else lifts it:
  no edit to the body can make a missing ancestor appear.  The
  notification is re-sent on each later edit that leaves that list
  alone, so a client need not remember the state.
    * `uri: URI` - the file that is not being compiled
    * `modules: [string]` - its declared dependencies, i.e. the list
      whose change clears the block
    * `message: string` - what went wrong, e.g.
      `cannot load fooTheory: Cannot find file fooTheory.ui`

* `textDocument/documentSymbol` lists a file's declarations, answered
  from the parser rather than from the last compile — so it works on a
  file that does not compile, or one blocked on an unloadable
  ancestor.  A client advertising
  `hierarchicalDocumentSymbolSupport` gets nested `DocumentSymbol`s,
  with the keyword and any attributes (`[simp]`, `[local]`) as
  `detail`; otherwise flat `SymbolInformation`.

* `workspace/symbol` searches stored theorems: those of the theories
  this server loaded, plus any theory built in the project, read from
  its `Theory.dat` without loading it.  The latter are marked
  `(not an ancestor)` in `containerName`, since using one requires
  adding the theory to `Ancestors` first.  Declarations of the open
  buffers are included.  A query shorter than two characters answers
  nothing: the search matches substrings.

* `textDocument/completion` offers the SML names in scope for the file
  and the theorem names HOL knows, with `.` as a trigger character.
  An empty prefix answers nothing, marked `isIncomplete`, rather than
  the whole namespace.

* There is no `textDocument/references`, and `referencesProvider` is
  not advertised.  Poly records references only within the
  compilation unit it is compiling, and HOL has no index of which
  proofs cite a theorem — `DB.revlookup` gives where a theorem was
  stored, not who uses it.

* The `$/hol/retryCompile` notification asks the server to compile a file
  it has blocked, without waiting for the header to change.  It is for the
  case where the missing ancestor has been built outside the editor.
    * `uri: URI` - the file to compile

* > **TODO** unimplemented; this is an API proposal

  `$/getState` request to get the current goal view state:
  * `uri: URI` - the file being compiled
  * `pos: Range` - the selection

  The response is either `null` if it is not in a proof, or an object containing:
  * `tactic: Range`
  * `goals: [Goal]` where `struct Goal { asms: [string], concl: string }`

  `goals` contains the list of goals that would be operated on by a tactic at this position.

