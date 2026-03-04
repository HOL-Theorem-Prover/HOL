---
title: LSP Server usage
author: Mario Carneiro
numbersections: yes
---

# LSP server

The [Language server protocol](https://microsoft.github.io/language-server-protocol/) is a standard protocol by Microsoft used for communicating between "language servers" which provide contextual language-specific information about files and "clients" or text editors. LSP client implementations exist for VSCode, Vim, Emacs among others so this makes a convenient common point for implementing HOL specific behaviors.

## Usage

> **TODO** The server does not yet handle multiple files as well as it could

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
  * `incr: Incr` where `enum Incr { None = 0, Chunk = 1, Stream = 2 }`
  * `holdep: HoldepKind` where `enum HoldepKind { None = 0, Quiet = 1, List = 2 }` - controls whether it should first call `holdep` to collect and preload any `open`s and other qualified names, and whether to print bindings (`List`) or not (`Quiet`).

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

* The `$/compileInterrupted` notification is sent when an asynchronous compile caused by a file open or modification event is interrupteds.
    * `uri: URI` - the file being compiled
