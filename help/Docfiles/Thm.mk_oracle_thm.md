## `mk_oracle_thm`

``` hol4
Thm.mk_oracle_thm : string -> term list * term -> thm
```

------------------------------------------------------------------------

Construct a theorem without proof, and tag it.

In principle, nearly every theorem of interest can be proved in HOL by
using only the axioms and primitive rules of inference. The use of ML to
orchestrate larger inference steps from the primitives, along with
support in HOL for goal-directed proof, considerably eases the task of
formal proof. Nearly every theorem of interest can therefore be produced
as the end product of a chain of primitive inference steps, and HOL
implementations strive to keep this purity.

However, it is occasionally useful to interface HOL with trusted
external tools that also produce, in some sense, theorems that would be
derivable in HOL. It is clearly a burden to require that HOL proofs
accompany such theorems so that they can be (re-)derived in HOL. In
order to support greater interoperation of proof tools, therefore, HOL
provides the notion of a 'tagged' theorem.

A tagged theorem is manufactured by invoking `mk_oracle_thm tag (A,w)`,
where `A` is a list of HOL terms of type `bool`, and `w` is also a HOL
term of boolean type. No proof is done; the sequent is merely injected
into the type of theorems, and the `tag` value is attached to it. The
result is the theorem `A |- w`.

The `tag` value stays with the theorem, and it propagates in a
hereditary fashion to any theorem derived from the tagged theorem. Thus,
if one examines a theorem with `Thm.tag` and finds that it has no tag,
then the theorem has been derived purely by proof steps in the HOL
logic. Otherwise, shortcuts have been taken, and the external tools,
also known as 'oracles', used to make the shortcuts are signified by the
tags.

### Failure

If some element of `A` does not have type `bool`, or `w` does not have
type `bool`, or the tag string doesn't represent a valid tag (which
occurs if it is the string `"DISK_THM"`, or if it is a string containing
unprintable characters).

### Example

In the following, we construct a tag and then make a rogue rule of
inference.

``` hol4
   - val tag = "SimonSays";
   > val tag = "SimonSays" : string

   - val SimonThm = mk_oracle_thm tag;
   > val SimonThm = fn : term list * term -> thm

   - val th = SimonThm ([], Term `!x. x`);
   > val th = |- !x. x : thm

   - val th1 = SPEC F th;
   > val th1 = |- F : thm

   - (show_tags := true; th1);
   > val it = [oracles: SimonSays] [axioms: ] [] |- F : thm
```

Tags accumulate in a manner similar to logical hypotheses.

``` hol4
   - CONJ th1 th1;
   > val it = [oracles: SimonSays] [axioms: ] [] |- F /\ F : thm

   - val SerenaThm = mk_oracle_thm "Serena";
   > val SerenaThm = fn : term list * term -> thm

   - CONJ th1 (SerenaThm ([],T));
   > val it = [oracles: Serena, SimonSays] [axioms: ] [] |- F /\ T : thm
```

### Comments

It is impossible to detach a tag from a theorem.

### See also

[`Thm.add_tag`](#Thm.add_tag), [`Thm.mk_thm`](#Thm.mk_thm),
[`Tag.read`](#Tag.read), [`Thm.tag`](#Thm.tag)
