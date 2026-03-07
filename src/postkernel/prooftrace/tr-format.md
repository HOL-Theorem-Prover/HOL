# .tr file format

The output of the `--trknl` proof tracer ([#1309](https://github.com/HOL-Theorem-Prover/HOL/pull/1309))
is a compressed proof trace for each theory, e.g. `src/bool/.hol/objs/boolTheory.tr.gz`.
If you uncompress it with `gzip`, the resulting data file is in the `.tr` file format.

This is a PolyML memory dump, but it can still be decoded to get to the proof matter.

## File structure: bit level

The outer structure of the dump is a sequence of objects, followed by a root pointer:

```c
file ::= object* tagptr
```

A tagged pointer `tagptr` is a little-endian 64 bit value which can be either an integer or a pointer.
If the low bit is `0`, then the remaining 63 bits are an index into the object list
(1-based, with 0 denoting the null pointer), and if the low bit is `1` then the
remaining bits denote a signed 63 bit integer.
```c
tagptr ::= 0 ptr63 | 1 int63
```

An object begins with a 64 bit header word, with the top 8 bits reserved for flags:
```c
header ::= len56 flags8
```
In all cases, an object will have exactly `len56` 64-bit words following it:
```c
object ::= header data64[len56]
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

* For `Bytes`, the data is a packed byte-array. The first word is the byte length of the array,
  and it is followed by that many bytes. It is then padded to a multiple of 8 bytes.

  ```c
  bytes_data ::= blen64 data8[blen64] pad
  ```

* For `Regular`, the data is a sequence of tagged pointers:
  ```c
  regular_data ::= tagptr[len56]
  ```

## File structure: encoding types

We can summarize the file structure more abstractly like so:

```c
tagptr ::= int63 | ptr63
bytes ::= int8*
regular ::= tagptr*
code ::= ()
closure ::= ()
object ::= bytes | regular | code | closure
file ::= object* tagptr
```

If we ignore the indirection in `Ptr`, this can be represented as an ADT:
```sml
datatype tagptr = Int of int63 | Ptr of object
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
  | Def_const_list_prf of string * (string * hol_type) list * thm
  | Def_const_prf of {Thy: string, Name: string} * term
  | Def_spec_prf of term list * thm
  | Def_tyop_prf of {Thy: string, Tyop: string} * hol_type list * thm * hol_type
  | EQ_IMP_RULE1_prf of thm
  | EQ_IMP_RULE2_prf of thm
  | EQ_MP_prf of thm * thm
  | EXISTS_prf of term * term * thm
  | GENL_prf of term list * thm
  | GEN_ABS_prf of term option * term list * thm
  | GEN_prf of term * thm
  | INST_TYPE_prf of (hol_type * hol_type) list * thm
  | INST_prf of (term * term) list * thm
  | MK_COMB_prf of thm * thm
  | MP_prf of thm * thm
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

type trace_file = (
  (* theory *)    string,
  (* parents *)   (string * string) list,
  (* types *)     (string * (* arity *) int) list,
  (* constants *) (string * hol_type) list,
  (* all_thms *)  (string * thm * thminfo) list,
  (* mldeps *)    string list)
```
