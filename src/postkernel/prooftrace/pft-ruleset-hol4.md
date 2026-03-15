# PFT Ruleset: `hol4` (Draft)

This document defines the `hol4` ruleset for the
[PFT format](pft-format.md). It specifies the theorem commands available
in traces with `"ruleset":"hol4"`, their binary opcodes, JSON encodings,
and logical semantics.

## Primitive Constants and Types

The `hol4` ruleset assumes three primitive types and constants provided by
the `min` theory. These are not defined by the trace; they are built into
the kernel.

The primitive type operators are:

| Type operator | Name | Arity |
|---------------|------|-------|
| Booleans | `min$bool` | 0 |
| Functions | `min$fun` | 2 |

We write these as simply `bool` and `_ → _` henceforth.

The primitive constants are:

| Constant | Name | Type |
|----------|------|------|
| Equality | `min$=` | `'a → 'a → bool` |
| Implication | `min$==>` | `bool → bool → bool` |
| Choice | `min$@` | `('a → bool) → 'a` |

Here `'a` is the concrete type variable name (i.e., the string one would
pass to TYVAR). When applied to arguments, we write `_ = _`, `_ ⇒ _`,
and `@` without the `min$` prefix.

## Required Constant Definitions

Several kernel rules refer to logical connectives (¬, ∧, ∨, ∀, ∃, etc.)
that are not primitive. Before these rules can be used, the corresponding
constants must be defined via DEF_SPEC, producing a theorem
`⊢ c = <expected RHS>` whose RHS exactly matches what the kernel expects
(up to alpha-equivalence).

The constants must be defined in the order listed below, because later
definitions depend on earlier ones. Each definition introduces a constant
in the `bool` theory.

### 1. `bool$T` (truth)

```
bool$T = ((λx:bool. x) = (λx:bool. x))
```

No dependencies beyond the primitive `min$=`.

**Required by**: no rules directly, but needed by `bool$!`.

### 2. `bool$!` (universal quantification)

```
bool$! = (λP:'a→bool. P = (λx:'a. T))
```

The type variable `'a` is concrete. The constant has type
`('a → bool) → bool`.

Depends on: `bool$T`.

**Required by**: SPEC, Specialize, GEN, GENL, EXISTS, CHOOSE, and
indirectly by all rules that depend on constants defined using `!`.

### 3. `bool$?` (existential quantification)

```
bool$? = (λP:'a→bool. P (@ P))
```

The type variable `'a` is concrete. The constant has type
`('a → bool) → bool`.

Depends on: `min$@` (primitive).

**Required by**: EXISTS, CHOOSE, DEF_TYOP.

### 4. `bool$F` (falsity)

```
bool$F = bool$!(λt:bool. t)
```

Depends on: `bool$!`.

**Required by**: NOT_INTRO, NOT_ELIM, CCONTR (via `bool$~`).

### 5. `bool$~` (negation)

```
bool$~ = (λt:bool. t ⇒ bool$F)
```

Depends on: `bool$F`, `min$==>`.

**Required by**: NOT_INTRO, NOT_ELIM, CCONTR.

### 6. `bool$/\` (conjunction)

```
bool$/\ = (λt1:bool. λt2:bool. bool$!(λt:bool. (t1 ⇒ t2 ⇒ t) ⇒ t))
```

Depends on: `bool$!`, `min$==>`.

**Required by**: CONJ, CONJUNCT1, CONJUNCT2, DEF_TYOP (via
`bool$TYPE_DEFINITION`).

### 7. `bool$\/` (disjunction)

```
bool$\/ = (λt1:bool. λt2:bool. bool$!(λt:bool. (t1 ⇒ t) ⇒ (t2 ⇒ t) ⇒ t))
```

Depends on: `bool$!`, `min$==>`.

**Required by**: DISJ1, DISJ2, DISJ_CASES.

### 8. `bool$TYPE_DEFINITION`

```
bool$TYPE_DEFINITION =
  (λP:'a→bool. λrep:'b→'a.
    (∀x':'b. ∀x'':'b. (rep x' = rep x'') ⇒ (x' = x'')) ∧
    (∀x:'a. P x = ∃x':'b. x = rep x'))
```

The type variables `'a` and `'b` are concrete. The constant has type
`('a → bool) → ('b → 'a) → bool`.

Depends on: `bool$!`, `bool$?`, `bool$/\`, `min$=`, `min$==>`.

**Required by**: DEF_TYOP.

### Summary of rule dependencies

| Rules | Required constants |
|-------|-------------------|
| REFL, ALPHA, BETA_CONV, SYM, TRANS, EQ_MP, MK_COMB, ABS_THM, AP_TERM, AP_THM, Beta, Mk_comb, Mk_abs, ASSUME, MP, DISCH, deductAntisym, EQ_IMP_RULE1, EQ_IMP_RULE2, INST, INST_TYPE, SUBST, ABSL, GEN_ABS, DEF_SPEC | *(none)* |
| GEN, GENL | `bool$!` |
| SPEC, Specialize | `bool$!` |
| EXISTS | `bool$?` |
| CHOOSE | `bool$?` |
| NOT_INTRO, NOT_ELIM | `bool$~`, `bool$F` |
| CCONTR | `bool$~`, `bool$F` |
| CONJ, CONJUNCT1, CONJUNCT2 | `bool$/\` |
| DISJ1, DISJ2, DISJ_CASES | `bool$\/` |
| DEF_TYOP | `bool$TYPE_DEFINITION` |

## Command Reference

### Equality and rewriting

| Command | Arguments |
|---------|-----------|
| REFL | id, tm |
| ALPHA | id, tm1, tm2 |
| BETA_CONV | id, tm |
| SYM | id, th |
| TRANS | id, th1, th2 |
| EQ_MP | id, eq: thm-id, th: thm-id |

### Congruence

| Command | Arguments |
|---------|-----------|
| MK_COMB | id, th1, th2 |
| ABS_THM | id, tm, th |
| AP_TERM | id, tm, th |
| AP_THM | id, th, tm |
| Beta | id, th |
| Mk_comb | id, eq: thm-id, rator: thm-id, rand: thm-id |
| Mk_abs | id, eq: thm-id, body: thm-id |

### Implication and modus ponens

| Command | Arguments |
|---------|-----------|
| ASSUME | id, tm |
| MP | id, imp: thm-id, ant: thm-id |
| DISCH | id, tm, th |
| NOT_INTRO | id, th |
| NOT_ELIM | id, th |
| CCONTR | id, tm, th |
| deductAntisym | id, th1, th2 |

### Conjunction

| Command | Arguments |
|---------|-----------|
| CONJ | id, th1, th2 |
| CONJUNCT1 | id, th |
| CONJUNCT2 | id, th |

### Disjunction

| Command | Arguments |
|---------|-----------|
| DISJ1 | id, th, tm |
| DISJ2 | id, tm, th |
| DISJ_CASES | id, disj: thm-id, left: thm-id, right: thm-id |

### Quantifiers

| Command | Arguments |
|---------|-----------|
| GEN | id, tm, th |
| SPEC | id, tm, th |
| Specialize | id, tm, th |
| GENL | id, th, tms: term-id list |
| EXISTS | id, tm1, tm2, th |
| CHOOSE | id, var: term-id, existence: thm-id, body: thm-id |

### Abstraction lists

| Command | Arguments |
|---------|-----------|
| ABSL | id, th, tms: term-id list |
| GEN_ABS | id, th, tm, tms: term-id list |

### Instantiation and substitution

| Command | Arguments |
|---------|-----------|
| INST | id, th, subst: {redex: term-id, residue: term-id} list |
| INST_TYPE | id, th, subst: {redex: type-id, residue: type-id} list |
| SUBST | id, template: term-id, th, subst: {redex: term-id, residue: thm-id} list |
| EQ_IMP_RULE1 | id, th |
| EQ_IMP_RULE2 | id, th |

### Definitions

| Command | Arguments |
|---------|-----------|
| DEF_SPEC | id, th, names: string list |
| DEF_TYOP | id, th, name |

### Computation

| Command | Arguments |
|---------|-----------|
| COMPUTE_INIT | id, num_ty: type-id, cval_ty: type-id, char_eqns: {name: thm-id}, cval_terms: {name: term-id} |
| COMPUTE | id, ci: compute-id, tm, ths: thm-id list |

## Binary Opcodes

| Opcode | Command       | Arguments                              |
|--------|---------------|----------------------------------------|
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
| 0x39   | INST          | id th n_subst (redex residue)...       |
| 0x3A   | INST_TYPE     | id th n_subst (redex residue)...       |
| 0x3B   | SUBST         | id template th n_subst (redex residue)...|
| 0x3C   | deductAntisym | id th1 th2                             |
| 0x40   | DEF_SPEC      | id th n_names name...                  |
| 0x41   | DEF_TYOP      | id th name                             |
| 0x42   | COMPUTE       | id ci tm n_ths th...                   |
| 0x43   | COMPUTE_INIT  | id ty1 ty2 n_eqns (name th)... n_terms (name tm)... |

## JSON Lines Encoding

### Simple commands

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

### Commands with descriptive keys

```json
{"cmd":"EQ_MP","id":0,"eq":1,"th":2}
{"cmd":"MP","id":0,"imp":1,"ant":2}
{"cmd":"DISJ_CASES","id":0,"disj":1,"left":2,"right":3}
{"cmd":"CHOOSE","id":0,"var":1,"existence":2,"body":3}
{"cmd":"Mk_comb","id":0,"eq":1,"rator":2,"rand":3}
{"cmd":"Mk_abs","id":0,"eq":1,"body":2}
```

### Commands with lists

```json
{"cmd":"GENL","id":0,"th":1,"tms":[2,3]}
{"cmd":"ABSL","id":0,"th":1,"tms":[2,3]}
{"cmd":"GEN_ABS","id":0,"th":1,"tm":2,"tms":[3,4]}
```

### Substitution commands

Substitution lists use `redex` and `residue` keys:

```json
{"cmd":"INST","id":0,"th":1,"subst":[{"redex":2,"residue":3}]}
{"cmd":"INST_TYPE","id":0,"th":1,"subst":[{"redex":2,"residue":3}]}
{"cmd":"SUBST","id":0,"template":1,"th":2,"subst":[{"redex":3,"residue":4}]}
```

For INST and INST_TYPE, `redex` and `residue` are term IDs and type IDs
respectively. For SUBST, `redex` is a term ID and `residue` is a theorem ID.

### Definitions

```json
{"cmd":"DEF_SPEC","id":0,"th":1,"names":["c1","c2"]}
{"cmd":"DEF_TYOP","id":0,"th":1,"name":"mytype"}
```

### Computation

```json
{"cmd":"COMPUTE_INIT","id":0,"num_ty":1,"cval_ty":2,
 "char_eqns":{"alt_zero":10,"cond_T":11,"cond_F":12},
 "cval_terms":{"truth":20,"false":21}}
{"cmd":"COMPUTE","id":0,"ci":1,"tm":2,"ths":[3,4,5]}
```

`char_eqns` is an object mapping equation names to theorem IDs.
`cval_terms` is an object mapping operator names to term IDs.

## Example

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
{"cmd":"LIMITS","n_ty":3,"n_tm":4,"n_th":2,"n_ci":0}
```

## Specification of the Theorem Commands

We write `A` for hypothesis sets and `⊢` for entailment. The following
Unicode notation is used for readability:

| Symbol | Meaning |
|--------|---------|
| `λ` | lambda abstraction (primitive) |
| `⇒` | implication (`min$==>`) |
| `∀` | universal quantification (`bool$!`) |
| `∃` | existential quantification (`bool$?`) |
| `¬` | negation (`bool$~`) |
| `∧` | conjunction (`bool$/\`) |
| `∨` | disjunction (`bool$\/`) |

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
| NOT_INTRO | `A ⊢ p ⇒ F` | `A ⊢ ¬p` | Requires `bool$~` and `bool$F` |
| NOT_ELIM | `A ⊢ ¬p` | `A ⊢ p ⇒ F` | Requires `bool$~` and `bool$F` |
| CCONTR | `p`, `A ⊢ F` | `A \ {¬p} ⊢ p` | Requires `bool$~` and `bool$F` |
| deductAntisym | `A ⊢ p`, `B ⊢ q` | `(A \ {q}) ∪ (B \ {p}) ⊢ p = q` | |

### Conjunction

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| CONJ | `A ⊢ p`, `B ⊢ q` | `A ∪ B ⊢ p ∧ q` | Requires `bool$/\` |
| CONJUNCT1 | `A ⊢ p ∧ q` | `A ⊢ p` | Requires `bool$/\` |
| CONJUNCT2 | `A ⊢ p ∧ q` | `A ⊢ q` | Requires `bool$/\` |

### Disjunction

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| DISJ1 | `A ⊢ p`, `q` | `A ⊢ p ∨ q` | Requires `bool$\/` |
| DISJ2 | `q`, `A ⊢ p` | `A ⊢ q ∨ p` | Requires `bool$\/` |
| DISJ_CASES | `A ⊢ p ∨ q`, `B ⊢ r`, `C ⊢ r` | `A ∪ (B \ {p}) ∪ (C \ {q}) ⊢ r` | Requires `bool$\/` |

### Quantifiers

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| GEN | `x`, `A ⊢ p` | `A ⊢ ∀x. p` | `x` not free in `A`; requires `bool$!` |
| SPEC | `t`, `A ⊢ ∀x. p` | `A ⊢ p[t/x]` | `t` has same type as `x`; requires `bool$!` |
| Specialize | `t`, `A ⊢ ∀x. p` | `A ⊢ p[t/x]` | `t` has the same type as `x`; requires `bool$!` |
| GENL | `A ⊢ p`, `[x1,...,xn]` | `A ⊢ ∀x1...xn. p` | each `xi` not free in `A`; requires `bool$!` |
| EXISTS | `(∃x. p)`, `t`, `A ⊢ p[t/x]` | `A ⊢ ∃x. p` | Requires `bool$?` |
| CHOOSE | `v`, `A ⊢ ∃x. P`, `B ⊢ q` | `A ∪ (B \ {P[v/x]}) ⊢ q` | `v` not free in `∃x. P`, `q`, or the remaining hypotheses; requires `bool$?` |

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
| DEF_SPEC | `⊢ ∃v1...vn. P`, `[c1,...,cn]` | `⊢ P[c1/v1,...,cn/vn]` | Creates new constants `c1,...,cn`; the input theorem must have no hypotheses and no free variables; each `ci` gets the type of the corresponding `vi` |
| DEF_TYOP | `⊢ ∃v. P v`, name | `⊢ ∃rep. TYPE_DEFINITION P rep` | Creates a new type operator with the given name; `P : dom → bool` must be a closed term; the input theorem must have no hypotheses; the new type has the type variables of `P` as parameters. Requires `bool$TYPE_DEFINITION` |

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
  theorem must have no hypotheses. The equations use the `cval_terms`
  constants and operate at `num_ty` and `cval_ty` types. We write `ZERO`,
  `SUC`, `+`, `−`, `*`, `DIV`, `MOD`, `<` for the `zero`, `suc`, `add`,
  `sub`, `mul`, `div`, `mod`, `lt` constants; `T`, `F`, `COND` for
  `truth`, `false`, `cond`; `NUMERAL`, `ALT_ZERO`, `BIT1`, `BIT2` for
  `numeral`, `alt_zero`, `bit1`, `bit2`; `LET` for `let`; and `cv_num`,
  `cv_pair`, etc. for the cv constants. Variables `m`, `n` have type
  `num_ty`; variables `p`, `q`, `r`, `s` have type `cval_ty`; variables
  `f`, `a`, `b`, `x` are polymorphic as indicated.

  The required equations are:

  | Name | Equation |
  |------|----------|
  | `alt_zero` | `⊢ ALT_ZERO = ZERO` |
  | `cond_T` | `⊢ COND T a b = a` |
  | `cond_F` | `⊢ COND F a b = b` |
  | `numeral` | `⊢ NUMERAL n = n` |
  | `bit1` | `⊢ BIT1 n = n + (n + SUC ZERO)` |
  | `bit2` | `⊢ BIT2 n = n + (n + SUC (SUC ZERO))` |
  | `add1` | `⊢ ZERO + n = n` |
  | `add2` | `⊢ SUC m + n = SUC (m + n)` |
  | `sub1` | `⊢ ZERO − m = ZERO` |
  | `sub2` | `⊢ SUC m − n = COND (m < n) ZERO (SUC (m − n))` |
  | `mul1` | `⊢ ZERO * n = ZERO` |
  | `mul2` | `⊢ SUC m * n = m * n + n` |
  | `div` | `⊢ m DIV n = COND (n = ZERO) ZERO (COND (m < n) ZERO (SUC ((m − n) DIV n)))` |
  | `mod` | `⊢ m MOD n = COND (n = ZERO) m (COND (m < n) m ((m − n) MOD n))` |
  | `lt1` | `⊢ (m < ZERO) = F` |
  | `lt2` | `⊢ (m < SUC n) = COND (m = n) T (m < n)` |
  | `suc1` | `⊢ (SUC m = ZERO) = F` |
  | `suc2` | `⊢ (SUC m = SUC n) = (m = n)` |
  | `cval1` | `⊢ (cv_pair p q = cv_pair r s) = COND (p = r) (q = s) F` |
  | `cval2` | `⊢ (cv_pair p q = cv_num n) = F` |
  | `cval3` | `⊢ (cv_num m = cv_num n) = (m = n)` |
  | `cv_add1` | `⊢ cv_add (cv_num m) (cv_num n) = cv_num (m + n)` |
  | `cv_add2` | `⊢ cv_add (cv_num m) (cv_pair p q) = cv_num m` |
  | `cv_add3` | `⊢ cv_add (cv_pair p q) (cv_num n) = cv_num n` |
  | `cv_add4` | `⊢ cv_add (cv_pair p q) (cv_pair r s) = cv_num ZERO` |
  | `cv_sub1` | `⊢ cv_sub (cv_num m) (cv_num n) = cv_num (m − n)` |
  | `cv_sub2` | `⊢ cv_sub (cv_num m) (cv_pair p q) = cv_num m` |
  | `cv_sub3` | `⊢ cv_sub (cv_pair p q) (cv_num n) = cv_num ZERO` |
  | `cv_sub4` | `⊢ cv_sub (cv_pair p q) (cv_pair r s) = cv_num ZERO` |
  | `cv_mul1` | `⊢ cv_mul (cv_num m) (cv_num n) = cv_num (m * n)` |
  | `cv_mul2` | `⊢ cv_mul (cv_num m) (cv_pair p q) = cv_num ZERO` |
  | `cv_mul3` | `⊢ cv_mul (cv_pair p q) (cv_num n) = cv_num ZERO` |
  | `cv_mul4` | `⊢ cv_mul (cv_pair p q) (cv_pair r s) = cv_num ZERO` |
  | `cv_div1` | `⊢ cv_div (cv_num m) (cv_num n) = cv_num (m DIV n)` |
  | `cv_div2` | `⊢ cv_div (cv_num m) (cv_pair p q) = cv_num ZERO` |
  | `cv_div3` | `⊢ cv_div (cv_pair p q) (cv_num n) = cv_num ZERO` |
  | `cv_div4` | `⊢ cv_div (cv_pair p q) (cv_pair r s) = cv_num ZERO` |
  | `cv_mod1` | `⊢ cv_mod (cv_num m) (cv_num n) = cv_num (m MOD n)` |
  | `cv_mod2` | `⊢ cv_mod (cv_num m) (cv_pair p q) = cv_num m` |
  | `cv_mod3` | `⊢ cv_mod (cv_pair p q) (cv_num n) = cv_num ZERO` |
  | `cv_mod4` | `⊢ cv_mod (cv_pair p q) (cv_pair r s) = cv_num ZERO` |
  | `cv_lt1` | `⊢ cv_lt (cv_num m) (cv_num n) = cv_num (COND (m < n) (SUC ZERO) ZERO)` |
  | `cv_lt2` | `⊢ cv_lt (cv_num m) (cv_pair p q) = cv_num ZERO` |
  | `cv_lt3` | `⊢ cv_lt (cv_pair p q) (cv_num n) = cv_num ZERO` |
  | `cv_lt4` | `⊢ cv_lt (cv_pair p q) (cv_pair r s) = cv_num ZERO` |
  | `cv_if1` | `⊢ cv_if (cv_num (SUC m)) p q = p` |
  | `cv_if2` | `⊢ cv_if (cv_num ZERO) p q = q` |
  | `cv_if3` | `⊢ cv_if (cv_pair r s) p q = q` |
  | `cv_fst1` | `⊢ cv_fst (cv_pair p q) = p` |
  | `cv_fst2` | `⊢ cv_fst (cv_num m) = cv_num ZERO` |
  | `cv_snd1` | `⊢ cv_snd (cv_pair p q) = q` |
  | `cv_snd2` | `⊢ cv_snd (cv_num m) = cv_num ZERO` |
  | `cv_ispair1` | `⊢ cv_ispair (cv_pair p q) = cv_num (SUC ZERO)` |
  | `cv_ispair2` | `⊢ cv_ispair (cv_num m) = cv_num ZERO` |
  | `cv_eq` | `⊢ cv_eq p q = cv_num (COND (p = q) (SUC ZERO) ZERO)` |
  | `let` | `⊢ LET f x = f x` |

The context is created once and reused across multiple COMPUTE calls.

#### COMPUTE

Takes a compute context `ci`, a list of code equation theorems
`[th1,...,thn]`, and a term `t`. Returns `⊢ t = v` (no hypotheses) where `v`
is the normal form of `t` under evaluation.

**Conditions on code equations**: Each `thi` must be a theorem with no
hypotheses whose conclusion has the form `f x1 ... xk = r` where:
- `f` is a constant
- each `xi` is a variable of type `cval_ty`
- the `xi` are all distinct
- the RHS `r` has type `cval_ty`
- all free variables in `r` are among `x1,...,xk`
- all constants in `r` are among the LHS head constants of the code equations
  or the `cval_terms` constants
