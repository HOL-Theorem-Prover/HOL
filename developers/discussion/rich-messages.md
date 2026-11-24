# Messages that carry HOL values

How library code reports a term, type or theorem to the user, and why
the type it reports with is not a string.

## The problem

Until this change every message HOL produced was a string by the time
it left the place that raised it:

```sml
raise ERR "mulrelnorm" ("Not a " ^ term_to_string R)
```

There are about 181 sites in `src/` that do some version of this — a
term, type or theorem printed into a message within two lines of an
error or message constructor.  Three things are lost there, and a
fourth is paid for.

**Semantics.**  `Parse.term_to_string` pins `PPBackEnd.raw_terminal`,
so the constant/free-variable/bound-variable distinction, the theory a
constant comes from, and every type are thrown away before any front
end sees them.  HOL knows all of it at the moment of printing; the
string is where it stops.

**Layout.**  The text is wrapped at the raiser's `Globals.linewidth`,
not at the width of whatever ends up displaying it.

**Position.**  `HOL_WARNINGloc` flattens `locn.toString` into the
message text, and `parse_term.sml` bakes its own location into its
message.  The LSP then carries a `dropLocnTail` to parse that back
off.  Information that was structured becomes text and has to be
recovered by string surgery.

**Cost.**  `src/real/realSimps.sml` had

```sml
val (l,r) = dest_binop R (mkERR ("Not a " ^ term_to_string R)) t
```

and `dest_binop : term -> exn -> term -> term * term` takes its
exception *by value*.  So the relation was pretty-printed on every
call, failing or not, inside a simplifier conversion.  That is not an
unusual shape: `HolKernel` is full of `exn`-by-value destructors.

Measured, because the size of it is not obvious either way.  Building
that error costs **85 µs** — a constant is a small term, but printing
one goes through the whole grammar-driven printer — against 0 for the
suspension that replaces it, and the two render to the same text.
Building `src/real` enters `mulrelnorm0` **2736 times**, so this one
site was spending about **0.23 s** there, roughly half a percent of
that directory.  Real work, removed; not a figure to build a case on.
The argument for laziness is the 85 µs against the ubiquity of the
shape, not what one call site saves.

The last point is the one that decides the design.  Errors in this
tree are overwhelmingly speculative — 1819 `handle HOL_ERR`, 1611
`can`, 434 `Lib.total` in `src/` — so they are raised and discarded as
a control structure.  **A message type that rendered eagerly would be
unaffordable**, which is why the one below is lazy by construction
rather than as an optimisation.

## The type

`src/prekernel/HOLmessage.sig`:

```sml
type message

val empty    : message
val txt      : string -> message
val pp       : (unit -> HOLPP.pretty) -> message
val ^^       : message * message -> message
val concat   : message list -> message

val isEmpty  : message -> bool
val isPlain  : message -> bool
val toString : message -> string
val toPretty : message -> HOLPP.pretty
```

`Feedback_dtype` lives in `src/prekernel` and cannot name `Term`.  It
does not need to: the rich leaf is a *suspended pretty*, and that is
enough, because `Parse.pp_term` reads `Parse.current_backend` at the
moment it builds.  Nothing is rendered until someone forces the
suspension, and whoever forces it chooses the back end and the width.

That one indirection is what lets a single message serve a colour
terminal, EmitTeX, `statementDossierLib`'s HTML and the LSP without
any of them having to agree in advance.

## The combinators

`src/parse/Msg.sml` re-exports the above and adds the three that need
the kernel:

```sml
val tm : term -> message
val ty : hol_type -> message
val th : thm -> message
```

so a use site reads

```sml
infix 6 ^^
...
raise mk_HOL_ERRm "realSimps" "mulrelnorm" (Msg.txt "Not a " ^^ Msg.tm R)
```

The per-file `infix` line is the tree's existing idiom —
`src/parse/Preterm.sml` opens with `infix >> >- ++?`.

`Msg` cannot be used below `Parse`, which is where `Preterm` and
`typecheck_error` live.  They do not need it: `Preterm.typecheck` has
always taken its printers as a parameter, and that pair simply changed
from `(term -> string) * (hol_type -> string)` to one producing
messages.  `Parse.stdprinters` supplies it.  The seam was already
there.

## Carriage

```sml
datatype hol_error = HOL_ERROR of
        {origins : origin list,
         message : HOLmessage.message}   (* was: string *)
```

`mk_HOL_ERR : string -> string -> string -> exn` and `message_of :
hol_error -> string` keep their signatures, so the 2087 `raise ERR`
sites and the ~40 readers of `message_of` are untouched.  New:
`mk_HOL_ERRm`, `mk_HOL_ERRlocm`, `rich_message_of`,
`set_rich_message`, and `HOL_MESGm` / `HOL_WARNINGm` / `HOL_INFOm`.

`Feedback.pp_hol_error` already rendered a whole error as a
`HOLPP.pretty`, and `format_ERR` and `exn_to_string` already went
through it.  Its last line changed from `add_string message` to
`HOLmessage.toPretty message`, and the REPL's colour rendering and the
LSP's segment rendering both fall out of printers that already
existed.

### Two properties worth stating

**Text that went in through `txt` comes back byte for byte.**
`toString` concatenates `Txt` pieces literally and only runs the
pretty-printer over suspensions, so a message built only from `txt` is
indistinguishable from the string it was built from.  Without that,
every `lsp_tests.py` assertion on diagnostic text and every selftest
that matches on error text would shift at once.

**`toString` agrees with `term_to_string`.**  `Parse.term_to_string`
pins a raw back end and lays out at `Globals.linewidth`.  `toString`
must do both, or an error site that gains a `Msg.tm` silently changes
its text.  The prekernel cannot name a back end, so `HOLmessage` holds
a `plain_renderer` ref that `src/parse` fills in.  `toPretty`
deliberately does *not* go through it: that is the path the colour
terminal and the LSP's segment back end want.

Both are pinned by selftests (`src/prekernel/selftest.sml`,
`src/parse/selftest.sml`).

## Consequences that are not obvious

**`hol_error` is no longer an equality type.**  A message holds a
closure.  Exactly one site compared errors — `Feedback.sml`'s `if err
= empty_hol_error` — and it is now `is_empty_hol_error`.

**Forcing can fail, and does so while something has already gone
wrong.**  A printer that raises must not replace the error being
reported with itself, so every forcing is guarded and substitutes
`<unprintable>`.  `Interrupt` is let through.

**Force a message only where printing it makes sense.**  The
suspension reads `Parse.current_backend` and the ambient `Context` at
the moment it runs.  Anything that carries an error across a thread or
out of the context that raised it must render first.  This is the
reason the LSP's proof pool is the last thing that should be migrated:
its verdicts are formed on worker threads with thread-bound namespace
layers.

**MLton builds list their sources.**  A new module in
`src/prekernel` has to be added to `src/prekernel/mlton/prekernel.mlb`
or `src/postkernel/prooftrace` fails to build — and it fails there
rather than where the module is, because the Poly build of
`src/prekernel` is green either way.

Relatedly, a `.uo` under Poly is a dependency manifest rather than
proof that a module type-checked: the first attempt at this change had
`TermParse.sml` contradicting its own signature, `src/parse` built
clean, and the error appeared only when `boolScript` *loaded* it.

## What the front ends do with it

Covered in `tools-poly/lsp/README.md` under "What an error says about
its terms".  The short version: a `Diagnostic.message` is a plain
string in every version of the LSP and there is no way to hang a
tooltip off a word inside one, so the information travels by the hover
at the squiggle (which both editors already show beside a diagnostic)
and by a `$/hol/message` request for a client that wants to render the
message into a surface of its own.

## Not done

- **The message channels are only half structured.**  `HOL_MESGm`
  now offers its message to `Feedback.MESG_hook` before flattening it
  for `MESG_outstream`, so a consumer can get at the terms; the
  outstream's text is unchanged.  A plain ref rather than the
  `Listener.t` this section first proposed, because `Listener` is
  built on `Feedback` and naming it there would close a cycle — the
  `*_outstream` refs beside it are refs for the same reason.

  `HOL_WARNINGm` and `HOL_INFOm` still only flatten.  The warning
  channel is the one that wants care rather than another ref:
  `WARNINGs_as_ERRs` turns a warning into an exception built with
  `mk_HOL_ERR`, so it drops the message on a second floor, and
  fixing that means `mk_HOL_ERRm` there and a decision about whether
  a located `HOL_WARNING` should become a squiggle.  Still
  deliberately left: that decision is the hard part, not the
  plumbing.

  Nothing in the LSP installs a hook yet — what surface a plain
  `HOL_MESG` should get in an editor is a separate question from
  whether its terms survive the trip.  `src/num/theories/selftest.sml`
  is what holds the mechanism up: a term sent through `HOL_MESGm`,
  with its free variable's type and its constant's theory-qualified
  name recovered from the message the hook was handed.

- **Proof-pool failures.**  `LSPExtension.Failed of string` still
  reduces a tactic failure to text via `exn_to_string`, so a term
  error inside a tactic is reported against the failing step rather
  than carrying its terms.  See the threading note above for why this
  one needs care rather than just widening the constructor.

- **Most of the 181 sites.**  Migrated so far: `typecheck_error`,
  `Preterm`'s four message builders, `Defn`'s cross-clause
  `unify_error`, and `realSimps.mulrelnorm`.  The rest keep working
  unchanged, which is the point of leaving `mk_HOL_ERR` alone.
