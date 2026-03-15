# PFT Ruleset: `candle` (Draft)

This document defines the `candle` ruleset for the
[PFT format](pft-format.md). It specifies the theorem commands available
in traces with `"ruleset":"candle"`, their binary opcodes, JSON encodings,
and logical semantics.

The `candle` ruleset corresponds to the kernel of
[Candle](https://github.com/CakeML/cakeml/tree/master/candle), a verified
implementation of a HOL Light-like prover.

## Primitive Constants and Types

The primitive type operators are:

| Type operator | Name | Arity |
|---------------|------|-------|
| Booleans | `bool` | 0 |
| Functions | `fun` | 2 |

We write `bool` and `_ → _` for these henceforth.

There is one primitive constant:

| Constant | Name | Type |
|----------|------|------|
| Equality | `=` | `A → A → bool` |

Here `A` is the concrete type variable name (i.e., the string one would pass
to TYVAR). Candle uses unprimed type variable names.

Constant names in Candle are bare (no theory prefix): `=`, `@`, `T`, `!`,
etc.

No constant definitions are required before any inference rules can be used.
The kernel rules are purely structural and do not depend on the existence of
any defined constants.

## Command Reference

### Core inference rules

| Command | Arguments |
|---------|-----------|
| REFL | id, tm |
| TRANS | id, th1, th2 |
| MK_COMB | id, th1, th2 |
| ABS | id, tm, th |
| BETA | id, tm |
| ASSUME | id, tm |
| EQ_MP | id, eq: thm-id, th: thm-id |
| DEDUCT_ANTISYM_RULE | id, th1, th2 |
| INST | id, th, subst: {redex: term-id, residue: term-id} list |
| INST_TYPE | id, th, subst: {redex: type-id, residue: type-id} list |

### Derived rules (in-kernel)

These rules are logically derivable from the core rules but are implemented
directly in the kernel for efficiency.

| Command | Arguments |
|---------|-----------|
| SYM | id, th |
| PROVE_HYP | id, th1, th2 |
| ALPHA_THM | id, th, tms: term-id list, tm |

### Axioms and definitions

| Command | Arguments |
|---------|-----------|
| new_axiom | id, tm |
| new_specification | id, th |
| new_type_definition | id, th, tyname: string, absname: string, repname: string |

### Computation

| Command | Arguments |
|---------|-----------|
| COMPUTE_INIT | id, ths: thm-id list |
| COMPUTE | id, ci: compute-id, tm, ths: thm-id list |

## Binary Opcodes

| Opcode | Command                    | Arguments                              |
|--------|----------------------------|----------------------------------------|
| 0x10   | REFL                       | id tm                                  |
| 0x11   | TRANS                      | id th1 th2                             |
| 0x12   | MK_COMB                    | id th1 th2                             |
| 0x13   | ABS                        | id tm th                               |
| 0x14   | BETA                       | id tm                                  |
| 0x15   | ASSUME                     | id tm                                  |
| 0x16   | EQ_MP                      | id eq th                               |
| 0x17   | DEDUCT_ANTISYM_RULE        | id th1 th2                             |
| 0x18   | INST                       | id th n_pairs (redex residue)...       |
| 0x19   | INST_TYPE                  | id th n_pairs (redex residue)...       |
| 0x20   | SYM                        | id th                                  |
| 0x21   | PROVE_HYP                  | id th1 th2                             |
| 0x22   | ALPHA_THM                  | id th n_tms tm... tm                   |
| 0x30   | new_axiom                  | id tm                                  |
| 0x31   | new_specification          | id th                                  |
| 0x32   | new_type_definition        | id th tyname absname repname           |
| 0x40   | COMPUTE_INIT               | id n_ths th...                         |
| 0x41   | COMPUTE                    | id ci tm n_ths th...                   |


Note: In `new_type_definition`, the three names are encoded as strings.

Note: In `ALPHA_THM`, the last `tm` after the list is the new conclusion
term.

## JSON Lines Encoding

### Core inference rules

```json
{"cmd":"REFL","id":0,"tm":1}
{"cmd":"TRANS","id":0,"th1":1,"th2":2}
{"cmd":"MK_COMB","id":0,"th1":1,"th2":2}
{"cmd":"ABS","id":0,"tm":1,"th":2}
{"cmd":"BETA","id":0,"tm":1}
{"cmd":"ASSUME","id":0,"tm":1}
{"cmd":"EQ_MP","id":0,"eq":1,"th":2}
{"cmd":"DEDUCT_ANTISYM_RULE","id":0,"th1":1,"th2":2}
{"cmd":"INST","id":0,"th":1,"subst":[{"redex":2,"residue":3}]}
{"cmd":"INST_TYPE","id":0,"th":1,"subst":[{"redex":2,"residue":3}]}
```

### Derived rules

```json
{"cmd":"SYM","id":0,"th":1}
{"cmd":"PROVE_HYP","id":0,"th1":1,"th2":2}
{"cmd":"ALPHA_THM","id":0,"th":1,"tms":[2,3],"tm":4}
```

### Axioms and definitions

```json
{"cmd":"new_axiom","id":0,"tm":1}
{"cmd":"new_specification","id":0,"th":1}
{"cmd":"new_type_definition","id":0,"th":1,"tyname":"mid","absname":"mid_ABS","repname":"mid_REP"}
```

`new_type_definition` produces **two** theorems. The `id` field is
the first theorem's ID; the second theorem is assigned `id + 1`. The
replayer must reserve both IDs.

### Computation

```json
{"cmd":"COMPUTE_INIT","id":0,"ths":[1,2,3]}
{"cmd":"COMPUTE","id":0,"ci":1,"tm":2,"ths":[3,4,5]}
```

## Specification of the Theorem Commands

We write `H` for hypothesis sets (represented as lists with a set-like
union) and `⊢` for entailment.

### Core inference rules

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| REFL | `t` | `⊢ t = t` | |
| TRANS | `H1 ⊢ l = m1`, `H2 ⊢ m2 = r` | `H1 ∪ H2 ⊢ l = r` | `m1` and `m2` are alpha-equivalent |
| MK_COMB | `H1 ⊢ f = g`, `H2 ⊢ x = y` | `H1 ∪ H2 ⊢ f x = g y` | `f x` must be well-typed |
| ABS | `v`, `H ⊢ l = r` | `H ⊢ (λv. l) = (λv. r)` | `v` is a variable; `v` not free in `H` |
| BETA | `(λx. t) x` | `⊢ (λx. t) x = t` | argument must be exactly the bound variable |
| ASSUME | `p` | `{p} ⊢ p` | `p` has type `bool` |
| EQ_MP | `H1 ⊢ p = q`, `H2 ⊢ p'` | `H1 ∪ H2 ⊢ q` | `p` and `p'` are alpha-equivalent |
| DEDUCT_ANTISYM_RULE | `H1 ⊢ p`, `H2 ⊢ q` | `(H1 \ {q}) ∪ (H2 \ {p}) ⊢ p = q` | |
| INST | `H ⊢ p`, `[(t1,x1),...,(tn,xn)]` | `H[ti/xi] ⊢ p[ti/xi]` | each `xi` is a variable; each `ti` has same type as `xi` |
| INST_TYPE | `H ⊢ p`, `[(ty1,a1),...,(tyn,an)]` | `H[tyi/ai] ⊢ p[tyi/ai]` | type variable substitution |

Note: BETA only applies to terms of the form `(λx. t) x` where the argument
is exactly the bound variable. This is more restrictive than a general
beta-reduction.

### Derived rules

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| SYM | `H ⊢ l = r` | `H ⊢ r = l` | |
| PROVE_HYP | `H1 ⊢ p`, `H2 ⊢ q` | `H2 ∪ (H1 \ {q}) ⊢ p` | |
| ALPHA_THM | `H ⊢ c`, `H'`, `c'` | `H' ⊢ c'` | `c'` alpha-equivalent to `c`; every hypothesis in `H` is alpha-equivalent to some element of `H'`; all elements of `H'` have type `bool` |

### Axioms and definitions

| Rule | Inputs | Result | Side Conditions |
|------|--------|--------|-----------------|
| new_axiom | `t` | `⊢ t` | `t` has type `bool` |
| new_specification | `[v1=t1,...,vn=tn] ⊢ p` | `⊢ p[c1/v1,...,cn/vn]` | each `ti` is closed; type vars in `ti` ⊆ type vars in type of `vi`; `p` is closed under the `vi`; each `ci` is a fresh constant |
| new_type_definition | `⊢ P x`, tyname, absname, repname | `⊢ abs (rep a) = a` and `⊢ P r = (rep (abs r) = r)` | `P` is closed; hypotheses must be empty; creates a new type operator `tyname` and two new constants `absname` (rep-type → new-type) and `repname` (new-type → rep-type) |

### Computation

#### COMPUTE_INIT

Initialises a compute context from a fixed list of characteristic equation
theorems, provided in a specific order. Each theorem must have no
hypotheses.

The characteristic equations use BIT0/BIT1 numeral encoding, with `_0` as
the zero constant and `NUMERAL` as the numeral wrapper. The compute value
type is named `Cexp`, with constructors `Cexp_num` and `Cexp_pair`.

The required equations (in order):

| # | Equation |
|---|----------|
| 1 | `⊢ COND T m n = m` |
| 2 | `⊢ COND F m n = n` |
| 3 | `⊢ IF T x y = x` |
| 4 | `⊢ IF F x y = y` |
| 5 | `⊢ NUMERAL n = n` |
| 6 | `⊢ BIT0 n = n + n` |
| 7 | `⊢ BIT1 n = SUC (n + n)` |
| 8 | `⊢ (NUMERAL _0) + n = n` |
| 9 | `⊢ (SUC m) + n = SUC (m + n)` |
| 10 | `⊢ (NUMERAL _0) − n = NUMERAL _0` |
| 11 | `⊢ m − (NUMERAL _0) = m` |
| 12 | `⊢ (SUC m) − (SUC n) = m − n` |
| 13 | `⊢ (NUMERAL _0) * n = NUMERAL _0` |
| 14 | `⊢ (SUC m) * n = n + (m * n)` |
| 15 | `⊢ m DIV n = COND (n = NUMERAL _0) (NUMERAL _0) (COND (m < n) (NUMERAL _0) (SUC ((m − n) DIV n)))` |
| 16 | `⊢ m MOD n = COND (n = NUMERAL _0) m (COND (m < n) m ((m − n) MOD n))` |
| 17 | `⊢ m < (NUMERAL _0) = F` |
| 18 | `⊢ (NUMERAL _0) < (SUC n) = T` |
| 19 | `⊢ (SUC m) < (SUC n) = m < n` |
| 20 | `⊢ ((NUMERAL _0) = (NUMERAL _0)) = T` |
| 21 | `⊢ ((NUMERAL _0) = (SUC n)) = F` |
| 22 | `⊢ ((SUC m) = (NUMERAL _0)) = F` |
| 23 | `⊢ ((SUC m) = (SUC n)) = (m = n)` |
| 24 | `⊢ Cexp_add (Cexp_num m) (Cexp_num n) = Cexp_num (m + n)` |
| 25 | `⊢ Cexp_add (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num m` |
| 26 | `⊢ Cexp_add (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num n` |
| 27 | `⊢ Cexp_add (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num (NUMERAL _0)` |
| 28 | `⊢ Cexp_sub (Cexp_num m) (Cexp_num n) = Cexp_num (m − n)` |
| 29 | `⊢ Cexp_sub (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num m` |
| 30 | `⊢ Cexp_sub (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num (NUMERAL _0)` |
| 31 | `⊢ Cexp_sub (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num (NUMERAL _0)` |
| 32 | `⊢ Cexp_mul (Cexp_num m) (Cexp_num n) = Cexp_num (m * n)` |
| 33 | `⊢ Cexp_mul (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num (NUMERAL _0)` |
| 34 | `⊢ Cexp_mul (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num (NUMERAL _0)` |
| 35 | `⊢ Cexp_mul (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num (NUMERAL _0)` |
| 36 | `⊢ Cexp_div (Cexp_num m) (Cexp_num n) = Cexp_num (m DIV n)` |
| 37 | `⊢ Cexp_div (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num (NUMERAL _0)` |
| 38 | `⊢ Cexp_div (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num (NUMERAL _0)` |
| 39 | `⊢ Cexp_div (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num (NUMERAL _0)` |
| 40 | `⊢ Cexp_mod (Cexp_num m) (Cexp_num n) = Cexp_num (m MOD n)` |
| 41 | `⊢ Cexp_mod (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num m` |
| 42 | `⊢ Cexp_mod (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num (NUMERAL _0)` |
| 43 | `⊢ Cexp_mod (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num (NUMERAL _0)` |
| 44 | `⊢ Cexp_less (Cexp_num m) (Cexp_num n) = Cexp_num (COND (m < n) (SUC (NUMERAL _0)) (NUMERAL _0))` |
| 45 | `⊢ Cexp_less (Cexp_num m) (Cexp_pair p1 q1) = Cexp_num (NUMERAL _0)` |
| 46 | `⊢ Cexp_less (Cexp_pair p1 q1) (Cexp_num n) = Cexp_num (NUMERAL _0)` |
| 47 | `⊢ Cexp_less (Cexp_pair p1 q1) (Cexp_pair p2 q2) = Cexp_num (NUMERAL _0)` |
| 48 | `⊢ Cexp_if (Cexp_num (SUC m)) p1 q1 = p1` |
| 49 | `⊢ Cexp_if (Cexp_pair p2 q2) p1 q1 = q1` |
| 50 | `⊢ Cexp_if (Cexp_num (NUMERAL _0)) p1 q1 = q1` |
| 51 | `⊢ Cexp_fst (Cexp_pair p1 q1) = p1` |
| 52 | `⊢ Cexp_fst (Cexp_num m) = Cexp_num (NUMERAL _0)` |
| 53 | `⊢ Cexp_snd (Cexp_pair p1 q1) = q1` |
| 54 | `⊢ Cexp_snd (Cexp_num m) = Cexp_num (NUMERAL _0)` |
| 55 | `⊢ Cexp_ispair (Cexp_pair p1 q1) = Cexp_num (SUC (NUMERAL _0))` |
| 56 | `⊢ Cexp_ispair (Cexp_num m) = Cexp_num (NUMERAL _0)` |
| 57 | `⊢ Cexp_eq p1 q1 = Cexp_num (COND (p1 = q1) (SUC (NUMERAL _0)) (NUMERAL _0))` |
| 58 | `⊢ (Cexp_pair p1 q1 = Cexp_pair p2 q2) = IF (p1 = p2) (q1 = q2) F` |
| 59 | `⊢ (Cexp_num m = Cexp_num n) = (m = n)` |
| 60 | `⊢ (Cexp_num m = Cexp_pair p1 q1) = F` |
| 61 | `⊢ (Cexp_pair p1 q1 = Cexp_num n) = F` |
| 62 | `⊢ LET f p1 = f p1` |

Note: Candle uses both `COND` (conditional on `bool`) and `IF` (conditional
on the `Cexp` type). The `<` (less-than) equations use three structural
cases on natural numbers rather than a two-case pattern with `COND`.

#### COMPUTE

Takes a compute context `ci`, a list of code equation theorems
`[th1,...,thn]`, and a term `t`. Returns `⊢ t = v` (no hypotheses) where `v`
is the normal form of `t` under evaluation.

**Conditions on code equations**: Each `thi` must be a theorem with no
hypotheses whose conclusion has the form `f x1 ... xk = r` where:
- `f` is a constant
- each `xi` is a variable of type `Cexp`
- the `xi` are all distinct
- the RHS `r` has type `Cexp`
- all free variables in `r` are among `x1,...,xk`
- all constants in `r` appear as LHS head constants of some code equation
