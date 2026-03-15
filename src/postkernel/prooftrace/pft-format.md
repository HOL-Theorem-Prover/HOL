# HOL PFT Format Specification (Draft)

## Overview

A proof trace (PFT) is a linear stream of commands for a HOL theorem proving
kernel to construct a set of theorems.

Commands are topologically ordered — every object is constructed before it is
used.

## Object Namespaces

There are four namespaces, each with independently numbered IDs:

| Namespace        | Identifier |
|------------------|------------|
| Types            | `ty`       |
| Terms            | `tm`       |
| Theorems         | `th`       |
| Compute contexts | `ci`       |

IDs are reused: when an object is no longer needed, its ID may be assigned to
a new object in the same namespace. Each command assigns an ID in the
appropriate namespace (determined by the command type).

Since every command is typed, the assigned ID does not need a namespace
qualifier — it is unambiguously in the namespace of the command's result type.
DEL commands do require a namespace qualifier.

## Encodings

The format has two encodings: **binary** (primary, for production use) and
**JSON Lines** (for human inspection and interoperability). Both encode the
same abstract command stream. Producers and consumers SHOULD use the binary
encoding; the JSON Lines encoding is provided for debugging, testing, and
integration with tools that consume JSON.

## Header and Footer

Every trace begins with a header and ends with a footer.

### Header

The header specifies:

- **version**: the format version number (currently `1`). Covers the encoding
  and syntax of the format.
- **ruleset**: the name of the ruleset that defines the theorem commands
  available in the trace. The ruleset is specified separately (e.g.,
  [pft-ruleset-hol4.md](pft-ruleset-hol4.md) for the `hol4` ruleset).

### Footer

The footer declares the peak number of simultaneously live objects per
namespace: four counts for types, terms, theorems, and compute contexts
respectively.

A replayer can use these to pre-allocate fixed-size arrays. The footer is
placed at the end so that a producer can emit commands in a single pass
without needing to know the peak counts upfront. A reader can seek to the
end of the file to read the footer before processing commands from the start.

## Command Reference

Commands are divided into **format-level** commands (defined here, common to
all rulesets) and **theorem commands** (defined by the ruleset).

### Type Commands

| Command | Arguments | Description |
|---------|-----------|-------------|
| TYVAR   | id, name  | Construct a type variable |
| TYOP    | id, name, args: type-id list | Construct a type operator application |

### Term Commands

| Command | Arguments | Description |
|---------|-----------|-------------|
| VAR     | id, name, ty: type-id | Construct a variable |
| CONST   | id, name, ty: type-id | Construct a constant |
| COMB    | id, rator: term-id, rand: term-id | Construct a function application |
| ABS     | id, var: term-id, body: term-id | Construct a lambda abstraction |

### Control Commands

| Command | Arguments |
|---------|-----------|
| DEL | ns, id, upto: id (optional) |
| SAVE | name, th |
| LOAD | id, name |

**DEL** informs the replayer that the given object (or range of objects from
`id` to `upto` inclusive, if `upto` is present) is no longer needed. The
replayer MAY use this to free memory. A correct replayer MAY ignore all DEL
commands. Since IDs are reused, a slot will eventually be overwritten
regardless of whether DEL was issued; DEL allows the replayer to free the
underlying object earlier.

**SAVE** makes a theorem available by name. The replayer stores it in a
name→theorem table. The theorem remains available for subsequent LOAD commands
(including in concatenated traces).

**LOAD** retrieves a previously saved theorem by name and assigns it to a
theorem ID. The named theorem must have been saved by a prior SAVE command.

These commands enable modularity: a trace can be split into separate files
(e.g., one per theory), where each file LOADs its dependencies and SAVEs its
exports. Concatenating traces works as long as LOADs come after the
corresponding SAVEs.

### Theorem Commands

Theorem commands are defined by the ruleset. See the relevant ruleset
specification for the full list of commands, their arguments, and their
logical semantics.

## Name Semantics

Names in the trace are opaque strings. For systems with namespaced identifiers
(e.g., HOL4's `thy$name`), the namespace is encoded as part of the string.
The trace format does not interpret the structure of names.

Names carry the following semantics depending on context:

- **Type operator names** (in TYOP): Identify a type operator. Two TYOP
  commands with the same name and arguments produce the same type, even if
  assigned different IDs.
- **Type variable names** (in TYVAR): Identify a type variable. Two TYVAR
  commands with the same name produce the same type variable.
- **Constant names** (in CONST): Identify a constant. Two CONST commands with
  the same name and type produce the same constant.
- **Variable names** (in VAR): Identify a variable. Two VAR commands with the
  same name and type produce the same variable.
- **Save/Load names** (in SAVE, LOAD): Identify theorems in the name→theorem
  table. These are chosen by the producer and have no kernel significance.

Additional name semantics (e.g., for axiom or definition commands) are defined
by the ruleset.

A well-optimised producer SHOULD avoid creating duplicate IDs for the same
logical entity (i.e., should hash-cons types, terms, and sub-terms). However,
a valid trace MAY assign multiple IDs to equivalent objects — the replayer
will produce correct results either way.

## Binary Encoding

The binary format is the primary encoding. A binary trace starts with the
magic bytes `PFT\0` followed by the header, then a sequence of encoded
commands, and ends with a footer.

### Primitive encodings

- **Varint**: Variable-length unsigned integer encoding (LEB128). Each byte
  uses 7 data bits and 1 continuation bit (high bit). The last byte has its
  high bit clear.
- **String**: A varint length followed by that many bytes of UTF-8 text.

### Header

```
PFT\0 <version:varint> <ruleset:string>
```

### Footer

```
<n_ty:varint> <n_tm:varint> <n_th:varint> <n_ci:varint> <footer_len:uint16le>
```

The footer consists of four varint counts followed by a 2-byte little-endian
unsigned integer giving the byte length of the footer excluding the 2-byte
length field itself. A reader seeks to the last 2 bytes of the file to read
the length, then seeks back that many bytes to read the four counts.

### Command encoding

Each command is encoded as a single-byte opcode, followed by its arguments.
IDs and counts are encoded as varints. Names are encoded as strings.

### Format-level opcodes

| Opcode | Command       | Arguments                              |
|--------|---------------|----------------------------------------|
| 0x01   | TYVAR         | id name                                |
| 0x02   | TYOP          | id name n_args arg...                  |
| 0x03   | VAR           | id name type_id                        |
| 0x04   | CONST         | id name type_id                        |
| 0x05   | COMB          | id rator rand                          |
| 0x06   | ABS           | id var body                            |
| 0x50   | SAVE          | name th                                |
| 0x51   | LOAD          | id name                                |
| 0xE0   | DEL ty        | id                                     |
| 0xE1   | DEL tm        | id                                     |
| 0xE2   | DEL th        | id                                     |
| 0xE3   | DEL ci        | id                                     |
| 0xF0   | DEL ty range  | id_lo id_upto                          |
| 0xF1   | DEL tm range  | id_lo id_upto                          |
| 0xF2   | DEL th range  | id_lo id_upto                          |
| 0xF3   | DEL ci range  | id_lo id_upto                          |

Opcodes in the range 0x10–0x4F are reserved for theorem commands defined by
the ruleset.

Note: In the binary format, variable-length lists are preceded by a varint
count, since there are no delimiters.

## JSON Lines Encoding

The JSON Lines encoding represents the same abstract command stream as the
binary format. Each line of the file is a single JSON object. Empty lines
are ignored.

The file extension SHOULD be `.jsonl`.

### Header and footer

```json
{"cmd":"PFT","version":1,"ruleset":"hol4"}
```

```json
{"cmd":"LIMITS","n_ty":3,"n_tm":4,"n_th":2,"n_ci":0}
```

The footer is the last non-empty line. A reader can seek to the end of the
file and scan backwards for the last newline to read the footer.

### Type commands

```json
{"cmd":"TYVAR","id":0,"name":"'a"}
{"cmd":"TYOP","id":1,"name":"min$fun","args":[0,0]}
```

For TYOP, `args` is an array of type IDs (empty array for nullary operators).

### Term commands

```json
{"cmd":"VAR","id":0,"name":"x","ty":0}
{"cmd":"CONST","id":1,"name":"bool$T","ty":0}
{"cmd":"COMB","id":2,"rator":0,"rand":1}
{"cmd":"ABS","id":3,"var":0,"body":1}
```

### Control commands

```json
{"cmd":"DEL","ns":"tm","id":2}
{"cmd":"DEL","ns":"tm","id":2,"upto":5}
{"cmd":"SAVE","name":"bool$TRUTH","th":1}
{"cmd":"LOAD","id":0,"name":"bool$TRUTH"}
```

For DEL, `ns` is one of `"ty"`, `"tm"`, `"th"`, `"ci"`. When `upto` is
present, all IDs from `id` to `upto` inclusive are deleted.

### Theorem commands

The JSON encoding of theorem commands is defined by the ruleset. Each theorem
command is a JSON object with a `"cmd"` key identifying the command and an
`"id"` key for the assigned theorem ID (or other namespace ID as appropriate).

### Example

See the ruleset specification for a complete example including theorem
commands.
