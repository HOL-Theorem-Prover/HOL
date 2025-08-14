## `cv_trans_deep_embedding`

``` hol4
cv_transLib.cv_trans_deep_embedding : conv -> thm -> unit
```

------------------------------------------------------------------------

Translates equations defining a deeply embedded AST to the `cv_compute`
subset of HOL.

This function is similar to `cv_transLib.cv_trans`, but can only
translate constants. It is designed for the translation of large deep
embeddings to `:cv` functions. It takes as an argument a conversion
which must evaluate terms such as `from <deep_embedding>`
(e.g. `computeLib.EVAL`).

### Failure

When the input term is not a constant defining a suitable deep
embedding.

### Example

``` hol4
> Datatype:
    exp = Const num | Add exp exp
  End
<<HOL message: Defined type: "exp">>
> Definition sem_def:
    sem (Const n) = n ∧
    sem (Add e1 e2) = sem e1 + sem e2
  End
Definition has been stored under "sem_def"
val sem_def =
   ⊢ (∀n. sem (Const n) = n) ∧ ∀e1 e2. sem (Add e1 e2) = sem e1 + sem e2: thm
> Definition deep_def:
    deep = Add (Const 5) (Add (Const 2) (Const 3))
  End
Definition has been stored under "deep_def"
val deep_def = ⊢ deep = Add (Const 5) (Add (Const 2) (Const 3)): thm
> cv_trans sem_def;
Definition has been stored under "from_scratch_exp_def"
Equations stored under "cv_sem_def".
Induction stored under "cv_sem_ind".
Finished translating sem, stored in cv_sem_thm
val it = (): unit
> cv_trans_deep_embedding EVAL deep_def;
val it = (): unit
> cv_eval “sem deep”;
val it = ⊢ sem deep = 10: thm
```

### Comments

Designed to produce definitions suitable for evaluation by
`cv_transLib.cv_eval`.

### See also

[`cv_transLib.cv_trans`](#cv_transLib.cv_trans),
[`cv_transLib.cv_eval`](#cv_transLib.cv_eval)
