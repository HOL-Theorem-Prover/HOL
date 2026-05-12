# .tr file format

The output of the `--trknl` proof tracer ([#1309](https://github.com/HOL-Theorem-Prover/HOL/pull/1309))
is a compressed proof trace for each theory, e.g. `src/bool/.hol/objs/boolTheory.tr.gz`.
If you uncompress it with `gzip`, the resulting data file is in the `.tr` file format.

There are two variants of the format: a **64-bit** variant (the original, produced
by PolyML's `exportSmallToFD` directly) and a **32-bit** narrow variant (produced
by the `recode32` pipeline stage). The 32-bit variant starts with a 4-byte magic
`FF 00 00 00`; the 64-bit variant has no magic (its first byte is always `00`–`03`,
the flags byte of the first object header).

The 64-bit variant is a PolyML memory dump; the 32-bit variant recodes each word
from 8 bytes to 4 bytes but preserves the same logical structure.

## 64-bit file structure: bit level

The outer structure of the dump is a sequence of objects, followed by a root pointer:

```c
file64 ::= object64* tagptr64
```

A tagged pointer `tagptr64` is a little-endian 64 bit value which can be either an integer or a pointer.
If the low bit is `0`, then the remaining 63 bits are an index into the object list
(1-based, with 0 denoting the null pointer), and if the low bit is `1` then the
remaining bits denote a signed 63 bit integer.
```c
tagptr64 ::= 0 ptr63 | 1 int63
```

An object begins with a 64 bit header word, with the top 8 bits reserved for flags:
```c
header64 ::= len56 flags8
```
In all cases, an object will have exactly `len56` 64-bit words following it:
```c
object64 ::= header64 data64[len56]
```
The contents of those bytes depends on the object kind.

The low 2 bits of the flags denote the object kind: (the low bit is drawn on the left here, i.e. little-endian)
```c
flags8 ::= 00xxxxxx  // 0: Regular
        |  10xxxxxx  // 1: Bytes
        |  01xxxxxx  // 2: Code
        |  11xxxxxx  // 3: Closure
```
* For the `Code` and `Closure` kinds, the exporter does not export the contents, and `len56` will be 0.

* For `Bytes`, the data is an opaque byte region occupying `len56 * 8` bytes.
  Some byte objects (notably strings) begin with an 8-byte word giving the logical
  byte length of the array, followed by that many bytes of content and then padding
  to an 8-byte boundary. Other byte-array-like objects (used internally by PolyML)
  do **not** have a length prefix — the entire `len56 * 8` bytes are content.
  Since the two cases cannot be distinguished from the header alone, consumers
  that need to handle arbitrary byte objects should treat the whole region as opaque.

* For `Regular`, the data is a sequence of tagged pointers:
  ```c
  regular_data ::= tagptr64[len56]
  ```

## 32-bit file structure

The 32-bit variant has the same logical structure but every word is 4 bytes instead
of 8. It is produced by the standalone `recode32` binary
(`src/tracing/recode32.sml`) which reads a 64-bit dump from stdin and writes the
32-bit form to stdout, streaming with constant memory.

```c
file32 ::= magic32 object32* tagptr32

magic32 ::= FF 00 00 00          // 4 bytes, distinguishes from 64-bit

tagptr32 ::= 0 ptr31 | 1 int31   // 4-byte little-endian
                                  // ptr: 31-bit object index (1-based)
                                  // int: signed 31-bit integer

header32 ::= len24 flags8        // 4-byte little-endian
                                  // low 24 bits = word count, high 8 bits = flags
object32 ::= header32 data32[len24]
```

**Regular** objects: each data slot is a `tagptr32` (4 bytes). Word count `len24`
equals the 64-bit `len56` — same number of slots, each half as wide.

**Bytes** objects: the recoder copies the original `len56 * 8` raw bytes verbatim.
The 32-bit word count is `len24 = len56 * 2` (double the word count, half the word
width, same byte count). The raw content is byte-identical to the 64-bit form,
including any internal length prefix and padding. This means bytes objects have
**no size reduction** in the 32-bit format; savings come only from Regular objects
and headers.

**Code/Closure** objects: `len24 = 0`, same as 64-bit.

### Decoding 32-bit files

The parser (`ProofTraceParser.sml`) detects the magic byte and constructs a `Heap32`
variant internally. All `sh*` accessor functions dispatch on the variant:

* `flags_of` reads byte 3 (vs byte 7 for 64-bit) for the flags.
* `obj'` returns data start at `header + 4` (vs `header + 8`).
* `arg'` reads 4-byte words via `get32_se` (sign-extended to 64-bit) at
  `byte_offset / 2` — all structural offsets used by the `sh*` functions are
  multiples of 8, so the halving is exact.
* `str` reads the 8-byte length word and subsequent raw bytes from the data area;
  the data area is byte-identical between formats.

### Width assumptions

The 32-bit format requires that all pointer indices fit in 31 bits and all integer
values fit in 31 signed bits. Empirical verification across 279 CakeML theory files
confirmed:
* max pointer index: ~250M (~28 bits)
* max absolute integer: ~15K (~14 bits)
* max object word count: 10

There is ample headroom. If a future file exceeds 31 bits, the recoder will
silently truncate — readers should verify width limits on critical deployments.

## File structure: encoding types

We can summarize the file structure more abstractly like so:

```c
tagptr ::= int | ptr
bytes ::= int8*
regular ::= tagptr*
code ::= ()
closure ::= ()
object ::= bytes | regular | code | closure
file ::= object* tagptr
```

If we ignore the indirection in `Ptr`, this can be represented as an ADT:
```sml
datatype tagptr = Int of int | Ptr of object
and object = Bytes of word8 array | Regular of tagptr array | Code | Closure
```

Now we will describe how SML datatypes are encoded as elements of `tagptr`.

* `n: int` is represented as `Int n`
* `()` is represented as `Int 0`
* `b: bool` is represented with false as `Int 0` and true as `Int 1`
* `c: char` is also represented as an `Int`
* `s: string` is represented as `Ptr (Bytes s)` where `s` is encoded as a byte array
* An n-tuple `(a1, a2, ..., an)` is represented as `Ptr (Regular [a1, a2, ..., an])` using the interpretation of the `ai` at their respective types.
* An array `Array.fromList[a1, a2, ..., an]` or vector is also represented as `Ptr (Regular [a1, a2, ..., an])`.
* A ref `ref a` is represented like a 1-tuple: `Ptr (Regular [a])`.
* An empty list `[]` is `Int 0`, and a cons cell `a :: l` is `Ptr (Regular [a, l])`.
* A function value `fn x => e` is represented as `Ptr Closure`.
* A record type `{c1 = a1, ..., cn = an}` is laid out the same as an n-tuple, but the field names are first sorted, first by length and then in ASCIIbetical order. So `{B=10, A=20, AA=30, a=40}` is re-sorted to `{A=20, B=10, a=40, AA=30}` and laid out as `Ptr (Regular [20, 10, 40, 30])`.
* Given a datatype declaration `datatype T = C1 of args | ... | CN of args`:
  * Each constructor is assigned a discriminant value, based on its order after sorting the constructors in ASCIIbetical order. So if the constructors are `[B, A, AA, a]` then this is re-sorted to `[A, AA, B, a]` and the discriminants are `A = 0, AA = 1, B = 2, a = 3`.
  * The arguments are treated as a list, where `C1` has zero arguments, `C1 of T` has one argument, `C1 of T * T` is two arguments, `C1 of T * T * T` is three arguments and so on. If there are more than 4 arguments, then it is instead treated as if it has one argument, which is an n-tuple (n > 4). (This situation does not arise below.)
  * The encoding of `C(a, b, c)` is then `Ptr (Regular [Int n, a, b, c])` where `n` is the discriminant of `C`.
* If a datatype has at most one variant `V` which has n > 0 arguments, it uses an alternative layout:
  * The variants are sorted as before, but `V` is skipped and is not assigned a discriminant.
  * The layout of `C` is `Int n` where `n` is the discriminant of `C != V`.
  * The layout of `V(a, b, c)` is `Ptr (Regular [a, b, c])`.
  Note that the layout of lists above is consistent with a datatype declaration
  `datatype 'a list = nil | cons of 'a * 'a list` under this rule. We will call these datatypes "option-like" below, since `'a option` also uses this optimization.

## File structure: SML data declarations

Now that we can encode arbitrary datatypes inside the file, it suffices to give the type of the root pointer. This is more or less a copy of the sources, but we have re-sorted the constructors according to the above sort criteria where applicable. A `clos` means the value in this position is a function type.
```sml
type id = {Thy: string, Name: string}

datatype hol_type
  = Tyapp of (id * int) * hol_type list
  | Tyv of string

datatype holty
  = GRND of hol_type
  | POLY of hol_type

datatype subs
  = Cons  of subs * term
  | Id
  | Lift  of int * subs
  | Shift of int * subs

datatype term
  = Abs   of term * term
  | Bv    of int
  | Clos  of subs * term
  | Comb  of term * term
  | Const of id * holty
  | Fv    of string * hol_type

datatype 'a tree
  = BLACK of 'a * 'a tree * 'a tree
  | LEAF
  | RED   of 'a * 'a tree * 'a tree

type 'a set = clos * 'a tree * int

datatype dep
  = DEP_SAVED of (string * int) * (string * int list) list
  | DEP_UNSAVED of (string * int list) list

type tag = dep * string list * string ref list

type thm = tag * term set * term * proof ref

datatype thm_id
  = SavedAnon of int
  | SavedName of string

datatype proof
  = ABS_prf of term * thm
  | ALPHA_prf of term * term
  | AP_TERM_prf of term * thm
  | AP_THM_prf of thm * term
  | ASSUME_prf of term
  | Axiom_prf
  | BETA_CONV_prf of term
  | Beta_prf of thm
  | CCONTR_prf of term * thm
  | CHOOSE_prf of term * thm * thm
  | CONJUNCT1_prf of thm
  | CONJUNCT2_prf of thm
  | CONJ_prf of thm * thm
  | DISCH_prf of term * thm
  | DISJ1_prf of thm * term
  | DISJ2_prf of term * thm
  | DISJ_CASES_prf of thm * thm * thm
  | Def_const_list_prf of thm * term list
  | Def_const_prf of term * term
  | Def_spec_prf of thm * term list
  | Def_tyop_prf of hol_type list * thm * hol_type
  | Disk_prf of string * thm_id
  | EQ_IMP_RULE1_prf of thm
  | EQ_IMP_RULE2_prf of thm
  | EQ_MP_prf of thm * thm
  | EXISTS_prf of term * term * thm
  | Exported_prf of string * thm_id
  | GENL_prf of term list * thm
  | GEN_ABS_prf of term option * term list * thm
  | GEN_prf of term * thm
  | INST_TYPE_prf of (hol_type * hol_type) list * thm
  | INST_prf of (term * term) list * thm
  | MK_COMB_prf of thm * thm
  | MP_prf of thm * thm
  | Mark_prf of string * thm
  | Mk_abs_prf of thm * term * thm
  | Mk_comb_prf of thm * thm * thm
  | NOT_ELIM_prf of thm
  | NOT_INTRO_prf of thm
  | REFL_prf of term
  | SPEC_prf of term * thm
  | SUBST_prf of (term * thm) list * term * thm
  | SYM_prf of thm
  | Specialize_prf of term * thm
  | TRANS_prf of thm * thm
  | compute_prf of (compute_args * thm list) * term
  | deductAntisym_prf of thm * thm
  | deleted_prf
  | save_dep_prf of thm

type compute_args =
  { num_type   : hol_type,
    char_eqns  : (string * thm) list,
    cval_type  : hol_type,
    cval_terms : (string * term) list }

datatype class = Axm | Def | Thm

datatype thm_src_location (* option-like *)
  = Unknown
  | Located of {exact: bool, linenum: int, scriptpath: string}

type thminfo = {loc: thm_src_location, class: class, private: bool}

type trace_file =
  { types     : (string * int) list,
    mldeps    : string list,
    theory    : string,
    parents   : (string * string) list,
    all_thms  : (string * thm * thminfo) list,
    anon_thms : thm list,
    constants : (string * hol_type) list }
```

### New proof constructors

**`Exported_prf of string * thm_id`** — Stub left behind by `Tracing.export_proof`.
The string is the path to the side `.tr.gz` file containing the serialized proof
tree; the `thm_id` identifies the theorem within it (typically `SavedName name`).
The original proof tree has been freed from memory.

**`Mark_prf of string * thm`** — No-op identity wrapper inserted by `Thm.mark`.
The string is a user-provided label; the inner thm has the same statement. Visible
in the trace as a named boundary for source-level instrumentation (e.g., wrapping
a tactic call to attribute its proof-tree cost).

**`save_dep_prf of thm`** — Wrapper inserted by `Theory.save_dep` when a theorem
is registered in the current theory. The inner thm is the original.

### Side files from `export_proof`

When `Tracing.export_proof name th` is called during a theory build, it writes the
proof tree of `th` to `.hol/objs/<thyname>Theory.<name>.tr.gz` using the same
pipeline (recode32 → gzip) as the main theory trace. The theorem's proof ref is
then set to `Exported_prf (filepath, SavedName name)`.

At theory-export time, `trace_theory` writes the main `.tr.gz` as usual. Any
theorem whose proof was previously exported will appear with an `Exported_prf` stub
in the main trace; the reader should chase the file reference to find the full proof.
