## `DNF_ss` {#boolSimps.DNF_ss}


```
DNF_ss : ssfrag
```



A simpset fragment that does aggressive propositional and quantifier
normalisation.


Adding the `DNF_ss` simpset fragment to a simpset augments it with
rewrites that make the simplifier normalise “towards” disjunctive
normal form. This normalisation at the propositional level does leave
implications alone (rather than convert them to disjunctions).
`DNF_ss` also includes normalisations pertaining to quantifiers. The
complete list of rewrites is
    
       |- !P Q. (!x. P x /\ Q x) <=> (!x. P x) /\ !x. Q x
       |- !P Q. (?x. P x \/ Q x) <=> (?x. P x) \/ ?x. Q x
       |- !P Q R. P \/ Q ==> R <=> (P ==> R) /\ (Q ==> R)
       |- !P Q R. P ==> Q /\ R <=> (P ==> Q) /\ (P ==> R)
       |- !A B C. (B \/ C) /\ A <=> B /\ A \/ C /\ A
       |- !A B C. A /\ (B \/ C) <=> A /\ B \/ A /\ C
       |- !P Q. (?x. P x) ==> Q <=> !x. P x ==> Q
       |- !P Q. P ==> (!x. Q x) <=> !x. P ==> Q x
       |- !P Q. (?x. P x) /\ Q <=> ?x. P x /\ Q
       |- !P Q. P /\ (?x. Q x) <=> ?x. P /\ Q x
    

### Failure

As a value rather than a function, `DNF_ss` can’t fail.

### Example

    
    > SIMP_CONV (bool_ss ++ DNF_ss) []
                ``!x. (?y. P x y) /\ Q z ==> R1 x z /\ R2 z x``;
    <<HOL message: inventing new type variable names: 'a, 'b, 'c>>
    val it =
       |- (!x. (?y. P x y) /\ Q z ==> R1 x z /\ R2 z x) <=>
            (!x y. P x y /\ Q z ==> R1 x z) /\
            !x y. P x y /\ Q z ==> R2 z x : thm
    

### Comments

The `DNF_ss` fragment interacts well with the one-point elimination
rules for equalities under quantifiers (provided in `bool_ss` and its
descendants).

### See also

[`boolSimps.bool_ss`](#boolSimps.bool_ss), [`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV)

