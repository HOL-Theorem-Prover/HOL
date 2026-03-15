# HOL4 Proof Trace Format Specification (Draft)

## Overview

A proof trace is a linear stream of commands for a HOL theorem proving kernel
to construct a set of theorems.

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
- **ruleset**: the set of theorem commands that may appear in the trace
  (currently `hol4`). This allows future rulesets (e.g., a minimal ruleset)
  to be defined independently of format version changes.

### Footer

The footer declares the peak number of simultaneously live objects per
namespace: four counts for types, terms, theorems, and compute contexts
respectively.

A replayer can use these to pre-allocate fixed-size arrays. The footer is
placed at the end so that a producer can emit commands in a single pass
without needing to know the peak counts upfront. A reader can seek to the
end of the file to read the footer before processing commands from the start.

## Command Reference

Each command is described below with its abstract arguments. The binary and
JSON Lines encodings of each command are specified in their respective
sections.

### Type Commands

| Command | Arguments | Description |
|---------|-----------|-------------|
| TYVAR   | id, name  | Construct a type variable (`mk_vartype`) |
| TYOP    | id, name, args: type-id list | Construct a type operator application (`mk_thy_type`) |

### Term Commands

| Command | Arguments | Description |
|---------|-----------|-------------|
| VAR     | id, name, ty: type-id | Construct a variable (`mk_var`) |
| CONST   | id, name, ty: type-id | Construct a constant (`mk_thy_const`) |
| COMB    | id, rator: term-id, rand: term-id | Construct a function application (`mk_comb`) |
| ABS     | id, var: term-id, body: term-id | Construct a lambda abstraction (`mk_abs`) |

### Theorem Commands

#### Equality and rewriting

| Command | Arguments |
|---------|-----------|
| REFL | id, tm |
| ALPHA | id, tm1, tm2 |
| BETA_CONV | id, tm |
| SYM | id, th |
| TRANS | id, th1, th2 |
| EQ_MP | id, eq: thm-id, th: thm-id |

#### Congruence

| Command | Arguments |
|---------|-----------|
| MK_COMB | id, th1, th2 |
| ABS_THM | id, tm, th |
| AP_TERM | id, tm, th |
| AP_THM | id, th, tm |
| Beta | id, th |
| Mk_comb | id, eq: thm-id, rator: thm-id, rand: thm-id |
| Mk_abs | id, eq: thm-id, body: thm-id |

#### Implication and modus ponens

| Command | Arguments |
|---------|-----------|
| ASSUME | id, tm |
| MP | id, imp: thm-id, ant: thm-id |
| DISCH | id, tm, th |
| NOT_INTRO | id, th |
| NOT_ELIM | id, th |
| CCONTR | id, tm, th |
| deductAntisym | id, th1, th2 |

#### Conjunction

| Command | Arguments |
|---------|-----------|
| CONJ | id, th1, th2 |
| CONJUNCT1 | id, th |
| CONJUNCT2 | id, th |

#### Disjunction

| Command | Arguments |
|---------|-----------|
| DISJ1 | id, th, tm |
| DISJ2 | id, tm, th |
| DISJ_CASES | id, disj: thm-id, left: thm-id, right: thm-id |

#### Quantifiers

| Command | Arguments |
|---------|-----------|
| GEN | id, tm, th |
| SPEC | id, tm, th |
| Specialize | id, tm, th |
| GENL | id, th, tms: term-id list |
| EXISTS | id, tm1, tm2, th |
| CHOOSE | id, var: term-id, existence: thm-id, body: thm-id |

#### Abstraction lists

| Command | Arguments |
|---------|-----------|
| ABSL | id, th, tms: term-id list |
| GEN_ABS | id, th, tm, tms: term-id list |

#### Instantiation and substitution

| Command | Arguments |
|---------|-----------|
| INST | id, th, subst: {redex: term-id, residue: term-id} list |
| INST_TYPE | id, th, subst: {redex: type-id, residue: type-id} list |
| SUBST | id, template: term-id, th, subst: {redex: term-id, residue: thm-id} list |
| EQ_IMP_RULE1 | id, th |
| EQ_IMP_RULE2 | id, th |

#### Axioms and definitions

| Command | Arguments |
|---------|-----------|
| AXIOM | id, tm, name (optional) |
| DEF_SPEC | id, th, names: string list |
| DEF_TYOP | id, th, name |

#### Computation

| Command | Arguments |
|---------|-----------|
| COMPUTE_INIT | id, num_ty: type-id, cval_ty: type-id, char_eqns: {name: thm-id}, cval_terms: {name: term-id} |
| COMPUTE | id, ci: compute-id, tm, ths: thm-id list |

### Control Commands

| Command | Arguments |
|---------|-----------|
| DEL | ns, id, upto: id (optional) |
| SAVE | name, th |
| LOAD | id, name |

**DEL** informs the replayer that the given object (or range of objects from
`id` to `upto` inclusive, if `upto` is present) is no longer needed. The replayer
MAY use this to free memory. A correct replayer MAY ignore all DEL commands.
Since IDs are reused, a slot will eventually be overwritten regardless of
whether DEL was issued; DEL allows the replayer to free the underlying object
earlier.

**SAVE** makes a theorem available by name. The replayer stores it in a
name→theorem table. The theorem remains available for subsequent LOAD commands
(including in concatenated traces).

**LOAD** retrieves a previously saved theorem by name and assigns it to a
theorem ID. The named theorem must have been saved by a prior SAVE command.

These commands enable modularity: a trace can be split into separate files
(e.g., one per theory), where each file LOADs its dependencies and SAVEs its
exports. Concatenating traces works as long as LOADs come after the
corresponding SAVEs.

## Name Semantics

Names in the trace are opaque strings. For systems with namespaced identifiers
(e.g., HOL4's `thy$name`), the namespace is encoded as part of the string.
The trace format does not interpret the structure of names.

Names carry the following semantics depending on context:

- **Type operator names** (in TYOP, DEF_TYOP): Identify a type operator.
  Two TYOP commands with the same name and arguments produce the same type,
  even if assigned different IDs.
- **Type variable names** (in TYVAR): Identify a type variable. Two TYVAR
  commands with the same name produce the same type variable.
- **Constant names** (in CONST, DEF_SPEC): Identify a constant. Two CONST
  commands with the same name and type produce the same constant.
- **Variable names** (in VAR): Identify a variable. Two VAR commands with the
  same name and type produce the same variable.
- **Axiom names** (in AXIOM): Optional and purely informational. Each AXIOM
  command is a distinct axiom assertion — two commands with the same name and
  conclusion are two separate axioms.
- **Save/Load names** (in SAVE, LOAD): Identify theorems in the name→theorem
  table. These are chosen by the producer and have no kernel significance.

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

#### Opcodes

| Opcode | Command       | Arguments                              |
|--------|---------------|----------------------------------------|
| 0x01   | TYVAR         | id name                                |
| 0x02   | TYOP          | id name n_args arg...                  |
| 0x03   | VAR           | id name type_id                        |
| 0x04   | CONST         | id name type_id                        |
| 0x05   | COMB          | id rator rand                          |
| 0x06   | ABS           | id tm1 tm2                             |
| 0x10   | REFL          | id tm                                  |
| 0x11   | ALPHA         | id tm1 tm2                             |
| 0x12   | ASSUME        | id tm                                  |
| 0x13   | BETA_CONV     | id tm                                  |
| 0x14   | EQ_MP         | id eq th                               |
| 0x15   | MP            | id imp ant                             |
| 0x16   | SYM           | id th                                  |
| 0x17   | TRANS         | id th1 th2                             |
| 0x18   | CONJ          | id th1 th2                             |
| 0x19   | CONJUNCT1     | id th                                  |
| 0x1A   | CONJUNCT2     | id th                                  |
| 0x1B   | DISCH         | id tm th                               |
| 0x1C   | DISJ1         | id th tm                               |
| 0x1D   | DISJ2         | id tm th                               |
| 0x1E   | DISJ_CASES    | id disj left right                     |
| 0x1F   | NOT_ELIM      | id th                                  |
| 0x20   | NOT_INTRO     | id th                                  |
| 0x21   | CCONTR        | id tm th                               |
| 0x22   | EXISTS        | id tm1 tm2 th                          |
| 0x23   | CHOOSE        | id var existence body                  |
| 0x24   | GEN           | id tm th                               |
| 0x25   | SPEC          | id tm th                               |
| 0x26   | Specialize    | id tm th                               |
| 0x27   | GENL          | id th n_tms tm...                      |
| 0x28   | ABSL          | id th n_tms tm...                      |
| 0x29   | GEN_ABS       | id th tm n_tms tm...                   |
| 0x30   | ABS_THM       | id tm th                               |
| 0x31   | AP_TERM       | id tm th                               |
| 0x32   | AP_THM        | id th tm                               |
| 0x33   | MK_COMB       | id th1 th2                             |
| 0x34   | Beta          | id th                                  |
| 0x35   | Mk_abs        | id eq body                             |
| 0x36   | Mk_comb       | id eq rator rand                       |
| 0x37   | EQ_IMP_RULE1  | id th                                  |
| 0x38   | EQ_IMP_RULE2  | id th                                  |
| 0x39   | INST          | id th n_pairs (redex residue)...       |
| 0x3A   | INST_TYPE     | id th n_pairs (redex residue)...       |
| 0x3B   | SUBST         | id template th n_pairs (redex residue)... |
| 0x3C   | deductAntisym | id th1 th2                             |
| 0x40   | AXIOM         | id tm name                             |
| 0x41   | DEF_SPEC      | id th n_names name...                  |
| 0x42   | DEF_TYOP      | id th name                             |
| 0x43   | COMPUTE       | id ci tm n_ths th...                   |
| 0x44   | COMPUTE_INIT  | id ty1 ty2 n_eqns (name th)... n_terms (name tm)... |
| 0x50   | SAVE          | name th                                |
| 0x51   | LOAD          | id name                                |
| 0xE0   | DEL ty        | id                                     |
| 0xE1   | DEL tm        | id                                     |
| 0xE2   | DEL th        | id                                     |
| 0xE3   | DEL ci        | id                                     |
| 0xF0   | DEL ty range  | id_lo id_hi                            |
| 0xF1   | DEL tm range  | id_lo id_hi                            |
| 0xF2   | DEL th range  | id_lo id_hi                            |
| 0xF3   | DEL ci range  | id_lo id_hi                            |

Note: In the binary format, variable-length lists are preceded by a varint
count, since there are no delimiters.

Note: In the binary AXIOM encoding, the name is always present. An empty
string indicates no name.

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
{"cmd":"FOOTER","n_ty":3,"n_tm":4,"n_th":2,"n_ci":0}
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

### Theorem commands

Commands with generic arguments use short positional keys (`th`, `tm`,
`th1`/`th2`, `tm1`/`tm2`). Commands where argument roles are non-obvious
use descriptive keys.

#### Simple commands

```json
{"cmd":"REFL","id":0,"tm":1}
{"cmd":"ALPHA","id":0,"tm1":1,"tm2":2}
{"cmd":"ASSUME","id":0,"tm":1}
{"cmd":"BETA_CONV","id":0,"tm":1}
{"cmd":"SYM","id":0,"th":1}
{"cmd":"TRANS","id":0,"th1":1,"th2":2}
{"cmd":"MK_COMB","id":0,"th1":1,"th2":2}
{"cmd":"ABS_THM","id":0,"tm":1,"th":2}
{"cmd":"AP_TERM","id":0,"tm":1,"th":2}
{"cmd":"AP_THM","id":0,"th":1,"tm":2}
{"cmd":"Beta","id":0,"th":1}
{"cmd":"MP","id":0,"imp":1,"ant":2}
{"cmd":"DISCH","id":0,"tm":1,"th":2}
{"cmd":"NOT_INTRO","id":0,"th":1}
{"cmd":"NOT_ELIM","id":0,"th":1}
{"cmd":"CCONTR","id":0,"tm":1,"th":2}
{"cmd":"deductAntisym","id":0,"th1":1,"th2":2}
{"cmd":"CONJ","id":0,"th1":1,"th2":2}
{"cmd":"CONJUNCT1","id":0,"th":1}
{"cmd":"CONJUNCT2","id":0,"th":1}
{"cmd":"DISJ1","id":0,"th":1,"tm":2}
{"cmd":"DISJ2","id":0,"tm":1,"th":2}
{"cmd":"GEN","id":0,"tm":1,"th":2}
{"cmd":"SPEC","id":0,"tm":1,"th":2}
{"cmd":"Specialize","id":0,"tm":1,"th":2}
{"cmd":"EXISTS","id":0,"tm1":1,"tm2":2,"th":3}
{"cmd":"EQ_IMP_RULE1","id":0,"th":1}
{"cmd":"EQ_IMP_RULE2","id":0,"th":1}
```

#### Commands with descriptive keys

```json
{"cmd":"EQ_MP","id":0,"eq":1,"th":2}
{"cmd":"DISJ_CASES","id":0,"disj":1,"left":2,"right":3}
{"cmd":"CHOOSE","id":0,"var":1,"existence":2,"body":3}
{"cmd":"Mk_comb","id":0,"eq":1,"rator":2,"rand":3}
{"cmd":"Mk_abs","id":0,"eq":1,"body":2}
```

#### Commands with lists

```json
{"cmd":"GENL","id":0,"th":1,"tms":[2,3]}
{"cmd":"ABSL","id":0,"th":1,"tms":[2,3]}
{"cmd":"GEN_ABS","id":0,"th":1,"tm":2,"tms":[3,4]}
```

#### Substitution commands

Substitution lists use `redex` and `residue` keys:

```json
{"cmd":"INST","id":0,"th":1,"subst":[{"redex":2,"residue":3}]}
{"cmd":"INST_TYPE","id":0,"th":1,"subst":[{"redex":2,"residue":3}]}
{"cmd":"SUBST","id":0,"template":1,"th":2,"subst":[{"redex":3,"residue":4}]}
```

For INST and INST_TYPE, `redex` and `residue` are term IDs and type IDs
respectively. For SUBST, `redex` is a term ID and `residue` is a theorem ID.

#### Axioms and definitions

```json
{"cmd":"AXIOM","id":0,"tm":1,"name":"MY_AXIOM"}
{"cmd":"AXIOM","id":0,"tm":1}
{"cmd":"DEF_SPEC","id":0,"th":1,"names":["c1","c2"]}
{"cmd":"DEF_TYOP","id":0,"th":1,"name":"mytype"}
```

For AXIOM, the `name` key is omitted when no name is provided.

#### Computation

```json
{"cmd":"COMPUTE_INIT","id":0,"num_ty":1,"cval_ty":2,
 "char_eqns":{"alt_zero":10,"cond_T":11,"cond_F":12,...},
 "cval_terms":{"truth":20,"false":21,...}}
{"cmd":"COMPUTE","id":0,"ci":1,"tm":2,"ths":[3,4,5]}
```

`char_eqns` is an object mapping equation names to theorem IDs.
`cval_terms` is an object mapping operator names to term IDs.

### Control commands

```json
{"cmd":"DEL","ns":"tm","id":2}
{"cmd":"DEL","ns":"tm","id":2,"upto":5}
{"cmd":"SAVE","name":"bool$TRUTH","th":1}
{"cmd":"LOAD","id":0,"name":"bool$TRUTH"}
```

For DEL, `ns` is one of `"ty"`, `"tm"`, `"th"`, `"ci"`. When `upto` is
present, all IDs from `id` to `upto` inclusive are deleted.

### Example

```json
{"cmd":"PFT","version":1,"ruleset":"hol4"}
{"cmd":"TYOP","id":0,"name":"bool$bool","args":[]}
{"cmd":"TYOP","id":1,"name":"min$fun","args":[0,0]}
{"cmd":"CONST","id":0,"name":"bool$=","ty":1}
{"cmd":"CONST","id":1,"name":"bool$T","ty":0}
{"cmd":"COMB","id":2,"rator":0,"rand":1}
{"cmd":"COMB","id":3,"rator":2,"rand":1}
{"cmd":"DEL","ns":"tm","id":2}
{"cmd":"REFL","id":0,"tm":1}
{"cmd":"AP_TERM","id":1,"tm":3,"th":0}
{"cmd":"DEL","ns":"th","id":0}
{"cmd":"DEL","ns":"tm","id":0,"upto":1}
{"cmd":"DEL","ns":"tm","id":3}
{"cmd":"SAVE","name":"bool$TRUTH","th":1}
{"cmd":"FOOTER","n_ty":3,"n_tm":4,"n_th":2,"n_ci":0}
```

## Specification of the Theorem Commands

We write `A` for hypothesis sets and `⊢` for entailment.

### Equality and rewriting

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| REFL | `t` | `⊢ t = t` | |
| ALPHA | `t1` `t2` | `⊢ t1 = t2` | `t1` and `t2` are alpha-equivalent |
| BETA_CONV | `(λx. t) u` | `⊢ (λx. t) u = t[u/x]` | |
| SYM | `A ⊢ t1 = t2` | `A ⊢ t2 = t1` | |
| TRANS | `A ⊢ t1 = t2`, `B ⊢ t2 = t3` | `A ∪ B ⊢ t1 = t3` | |
| EQ_MP | `A ⊢ p = q`, `B ⊢ p` | `A ∪ B ⊢ q` | |

### Congruence

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| MK_COMB | `A ⊢ f = g`, `B ⊢ x = y` | `A ∪ B ⊢ f x = g y` | types must be compatible |
| ABS_THM | `x`, `A ⊢ t1 = t2` | `A ⊢ (λx. t1) = (λx. t2)` | `x` not free in `A` |
| AP_TERM | `f`, `A ⊢ x = y` | `A ⊢ f x = f y` | `f` has compatible function type |
| AP_THM | `A ⊢ f = g`, `x` | `A ⊢ f x = g x` | types must be compatible |
| Beta | `A ⊢ t1 = (λx. b) u` | `A ⊢ t1 = b[u/x]` | RHS must be a beta-redex |

### Implication and modus ponens

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| ASSUME | `p` | `{p} ⊢ p` | `p` has type `bool` |
| MP | `A ⊢ p ⇒ q`, `B ⊢ p` | `A ∪ B ⊢ q` | |
| DISCH | `p`, `A ⊢ q` | `A \ {p} ⊢ p ⇒ q` | |
| NOT_INTRO | `A ⊢ p ⇒ F` | `A ⊢ ¬p` | |
| NOT_ELIM | `A ⊢ ¬p` | `A ⊢ p ⇒ F` | |
| CCONTR | `p`, `A ⊢ F` | `A \ {¬p} ⊢ p` | |
| deductAntisym | `A ⊢ p`, `B ⊢ q` | `(A \ {q}) ∪ (B \ {p}) ⊢ p = q` | |

### Conjunction

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| CONJ | `A ⊢ p`, `B ⊢ q` | `A ∪ B ⊢ p ∧ q` | |
| CONJUNCT1 | `A ⊢ p ∧ q` | `A ⊢ p` | |
| CONJUNCT2 | `A ⊢ p ∧ q` | `A ⊢ q` | |

### Disjunction

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| DISJ1 | `A ⊢ p`, `q` | `A ⊢ p ∨ q` | |
| DISJ2 | `q`, `A ⊢ p` | `A ⊢ q ∨ p` | |
| DISJ_CASES | `A ⊢ p ∨ q`, `B ⊢ r`, `C ⊢ r` | `A ∪ (B \ {p}) ∪ (C \ {q}) ⊢ r` | |

### Quantifiers

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| GEN | `x`, `A ⊢ p` | `A ⊢ ∀x. p` | `x` not free in `A` |
| SPEC | `t`, `A ⊢ ∀x. p` | `A ⊢ p[t/x]` | `t` has same type as `x` |
| Specialize | `t`, `A ⊢ ∀x. p` | `A ⊢ p[t/x]` | `t` has the same type as `x` |
| GENL | `A ⊢ p`, `[x1,...,xn]` | `A ⊢ ∀x1...xn. p` | each `xi` not free in `A` |
| EXISTS | `(∃x. p)`, `t`, `A ⊢ p[t/x]` | `A ⊢ ∃x. p` | |
| CHOOSE | `v`, `A ⊢ ∃x. P`, `B ⊢ q` | `A ∪ (B \ {P[v/x]}) ⊢ q` | `v` not free in `∃x. P`, `q`, or the remaining hypotheses |

Note: `Specialize` has the same logical semantics as `SPEC`, but indicates
a request to delay the substitution in kernel implementations whose terms
support doing that.

### Abstraction lists

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| ABSL | `A ⊢ t1 = t2`, `[x1,...,xn]` | `A ⊢ (λx1...xn. t1) = (λx1...xn. t2)` | each `xi` not free in `A` |
| GEN_ABS | `A ⊢ t1 = t2`, `c`, `[x1,...,xn]` | `A ⊢ (c (λx1. c (λx2. ... c (λxn. t1)...))) = (c (λx1. c (λx2. ... c (λxn. t2)...)))` | types are compatible; each `xi` not free in `A` |

### Parallel congruence (Mk rules)

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| Mk_comb | `A ⊢ t = f x`, `B ⊢ f = f'`, `C ⊢ x = x'` | `A ∪ B ∪ C ⊢ t = f' x'` | RHS of first thm must be an application; LHS of second must be alpha-equivalent to the rator; LHS of third must be alpha-equivalent to the rand |
| Mk_abs | `A ⊢ t = λv. b`, `B ⊢ b = b'` | `A ∪ B ⊢ t = λv. b'` | RHS of first thm must be an abstraction; LHS of second must be alpha-equivalent to the body; `v` not free in `B` |

In the kernel API, `Mk_comb` and `Mk_abs` return continuations. In the trace,
all arguments are provided directly.

### Instantiation and substitution

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| INST | `A ⊢ p`, `[(t1,x1),...,(tn,xn)]` | `A[ti/xi] ⊢ p[ti/xi]` | each `ti` has same type as `xi` |
| INST_TYPE | `A ⊢ p`, `[(ty1,a1),...,(tyn,an)]` | `A[tyi/ai] ⊢ p[tyi/ai]` | type variable substitution |
| SUBST | `[(v1, A1 ⊢ t1 = t1'),...,(vn, An ⊢ tn = tn')]`, `template`, `B ⊢ p` | `A1 ∪...∪ An ∪ B ⊢ p'` | `p'` is `p` with each `vi` in template replaced by corresponding `ti'` |
| EQ_IMP_RULE1 | `A ⊢ p = q` | `A ⊢ p ⇒ q` | |
| EQ_IMP_RULE2 | `A ⊢ p = q` | `A ⊢ q ⇒ p` | |

### Axioms and definitions

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| AXIOM | `t`, optional name | `⊢ t` | `t` has type `bool` |
| DEF_SPEC | `⊢ ∃v1...vn. P`, `[c1,...,cn]` | `⊢ P[c1/v1,...,cn/vn]` | Creates new constants `c1,...,cn`; the input theorem must have no hypotheses and no free variables; each `ci` gets the type of the corresponding `vi` |
| DEF_TYOP | `⊢ ∃v. P v`, name | `⊢ ∃rep. TYPE_DEFINITION P rep` | Creates a new type operator with the given name; `P : dom → bool` must be a closed term; the input theorem must have no hypotheses; the new type has the type variables of `P` as parameters |

### Computation

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| COMPUTE | ci, `[th1,...,thn]`, `t` | `⊢ t = v` | See below |

#### COMPUTE_INIT

Creates a compute context from four components:

- **`num_ty`**: the type of natural numbers (`:num`)
- **`cval_ty`**: the type of computed values (`:cv`)
- **`cval_terms`**: an object mapping operator names to term IDs. The
  following names must be present, each bound to a constant of the
  appropriate type:

  | Name | Description | Name | Description |
  |------|-------------|------|-------------|
  | `truth` | `T` | `false` | `F` |
  | `cond` | conditional | `let` | let-binding |
  | `zero` | `0 : num` | `alt_zero` | alternate zero |
  | `suc` | successor | `numeral` | numeral wrapper |
  | `bit1` | binary encoding | `bit2` | binary encoding |
  | `add` | addition | `sub` | subtraction |
  | `mul` | multiplication | `div` | division |
  | `mod` | modulus | `lt` | less-than |
  | `cv_pair` | cv pair constructor | `cv_num` | cv numeral constructor |
  | `cv_fst` | cv first projection | `cv_snd` | cv second projection |
  | `cv_ispair` | cv pair test | `cv_eq` | cv equality |
  | `cv_add` | cv addition | `cv_sub` | cv subtraction |
  | `cv_mul` | cv multiplication | `cv_div` | cv division |
  | `cv_mod` | cv modulus | `cv_lt` | cv less-than |
  | `cv_if` | cv conditional | | |

- **`char_eqns`**: an object mapping equation names to theorem IDs. Each
  theorem must have no hypotheses. The required equations are:

  | Name | Equation |
  |------|----------|
  | `alt_zero` | `ALT_ZERO = ZERO` |
  | `cond_T` | `COND T a b = a` |
  | `cond_F` | `COND F a b = b` |
  | `numeral` | `NUMERAL n = n` |
  | `bit1` | `BIT1 n = n + (n + SUC ZERO)` |
  | `bit2` | `BIT2 n = n + (n + SUC (SUC ZERO))` |
  | `add1` | `ZERO + n = n` |
  | `add2` | `SUC m + n = SUC (m + n)` |
  | `sub1` | `ZERO − m = ZERO` |
  | `sub2` | `SUC m − n = if m < n then ZERO else SUC (m − n)` |
  | `mul1` | `ZERO * n = ZERO` |
  | `mul2` | `SUC m * n = m * n + n` |
  | `div` | `m DIV n = if n = 0 then 0 else if m < n then 0 else SUC ((m − n) DIV n)` |
  | `mod` | `m MOD n = if n = 0 then m else if m < n then m else (m − n) MOD n` |
  | `lt1` | `m < ZERO = F` |
  | `lt2` | `m < SUC n = if m = n then T else m < n` |
  | `suc1` | `(SUC m = ZERO) = F` |
  | `suc2` | `(SUC m = SUC n) = (m = n)` |
  | `cval1` | `(cv_pair p q = cv_pair r s) = if p = r then q = s else F` |
  | `cval2` | `(cv_pair p q = cv_num n) = F` |
  | `cval3` | `(cv_num m = cv_num n) = (m = n)` |
  | `cv_add1`–`cv_add4` | cv_add on all four constructor combinations |
  | `cv_sub1`–`cv_sub4` | cv_sub on all four constructor combinations |
  | `cv_mul1`–`cv_mul4` | cv_mul on all four constructor combinations |
  | `cv_div1`–`cv_div4` | cv_div on all four constructor combinations |
  | `cv_mod1`–`cv_mod4` | cv_mod on all four constructor combinations |
  | `cv_lt1`–`cv_lt4` | cv_lt on all four constructor combinations |
  | `cv_if1`–`cv_if3` | cv_if on cv_num/cv_pair conditions |
  | `cv_fst1`–`cv_fst2` | cv_fst on cv_pair/cv_num |
  | `cv_snd1`–`cv_snd2` | cv_snd on cv_pair/cv_num |
  | `cv_ispair1`–`cv_ispair2` | cv_ispair on cv_pair/cv_num |
  | `cv_eq` | `cv_eq p q = cv_num (if p = q then SUC ZERO else ZERO)` |
  | `let` | `LET f x = f x` |

  The "four constructor combinations" for binary cv operations are:
  `(cv_num, cv_num)`, `(cv_num, cv_pair)`, `(cv_pair, cv_num)`,
  `(cv_pair, cv_pair)`.

The context is created once and reused across multiple COMPUTE calls.

#### COMPUTE

Takes a compute context `ci`, a list of code equation theorems
`[th1,...,thn]`, and a term `t`. Returns `⊢ t = v` (no hypotheses) where `v`
is the normal form of `t` under evaluation.

**Conditions on code equations**: Each `thi` must be a theorem with no
hypotheses whose conclusion has the form `f x1 ... xk = r` where:
- `f` is a constant
- each `xi` is a variable of type `cval_type`
- the `xi` are all distinct
- the RHS `r` has type `cval_type`
- all free variables in `r` are among `x1,...,xk`
- all constants in `f` are among the LHS head constants of the code equations

## Production from HOL4 Proof Traces

A PFT trace can be produced from HOL4's internal proof trace format by
replaying the internal trace and emitting PFT commands as each object is
constructed. The process has two passes:

### Pass 1: Analysis

Walk the internal proof DAG to determine:

1. **Reachability**: Starting from target theorems, find the minimal set of
   theorem, term, and type nodes needed.
2. **Reference counts**: For each reachable node, count how many times it
   will be accessed during replay (for DEL placement).
3. **Peak live sets**: Track the maximum number of simultaneously live objects
   per namespace (for the footer).
4. **ID assignment**: Assign IDs with reuse — maintain a free list per
   namespace, always assigning the lowest available ID. When a node's
   reference count reaches zero, return its ID to the free list.

### Pass 2: Emission

Replay the internal trace in topological order. For each kernel operation:

1. Emit the corresponding PFT command with the assigned ID.
2. Decrement reference counts of arguments. When a count reaches zero,
   emit a DEL command (or batch into range DELs).
3. For term construction, convert from the internal de Bruijn/explicit
   substitution representation to the public API (VAR, CONST, COMB, ABS)
   — the existing replay code already does this.

The footer is emitted last with the peak counts accumulated during emission.
