## `Hol_reln`

``` hol4
bossLib.Hol_reln : term quotation -> (thm * thm * thm)
```

------------------------------------------------------------------------

Defines inductive relations.

The `Hol_reln` function is used to define inductively characterised
relations. It takes a term quotation as input and attempts to define the
relations there specified. The input term quotation must parse to a term
that conforms to the following grammar:

``` hol4
   <input-format> ::= <clause> /\ <input-format> | <clause>
   <clause>       ::= (!x1 .. xn. <hypothesis> ==> <conclusion>)
                   |  (!x1 .. xn. <conclusion>)
   <conclusion>   ::= <con> sv1 sv2 ....
   <hypothesis>   ::= any term
   <con>          ::= a new relation constant
```

The `sv1` terms that appear after a constant name are so-called
"schematic variables". The same variables must always follow the same
constant name throughout the definition. These variables and the names
of the constants-to-be must not be quantified over in each `<clause>`.
Otherwise, a `<clause>` must not include any free variables. (The
universal quantifiers at the head of the clause can be used to bind free
variables, but it is also permissible to use existential quantification
in the hypotheses. If a clause has no free variables, it is permissible
to have no universal quantification.)

The `Hol_reln` function may be used to define multiple relations. These
may or may not be mutually recursive. The clauses for each relation need
not be contiguous.

The function returns three theorems. Each is also saved in the current
theory segment. The first is a conjunction of implications that will be
the same as the input term quotation. This theorem is saved under the
name `<stem>_rules`, where `<stem>` is the name of the first relation
defined by the function. The second is the induction principle for the
relations, saved under the name `<stem>_ind`. The third is the cases
theorem for the relations, saved under the name `<stem>_cases`. The
cases theorem is of the form

``` hol4
   (!a0 .. an.  R1 a0 .. an = <R1's first rule possibility> \/
                              <R1's second rule possibility> \/ ...)
                   /\
   (!a0 .. am.  R2 a0 .. am = <R2's first rule possibility> \/
                              <R2's second rule possibility> \/ ...)
                   /\
   ...
```

### Failure

The `Hol_reln` function will fail if the provided quotation does not
parse to a term of the specified form. It will also fail if a clause's
only free variables do not follow a relation name, or if a relation name
is followed by differing schematic variables. If the definition
principle can not prove that the characterisation is inductive (as would
happen if a hypothesis included a negated occurence of one of the
relation names), then the same theorems are returned, but with extra
assumptions stating the required inductive property.

If the name of the new constants are such that they will produce invalid
SML identifiers when bound in a theory file, using `export_theory` will
fail, and suggest the use of `set_MLname` to fix the problem.

### Example

Defining `ODD` and `EVEN`:

``` hol4
   - Hol_reln`EVEN 0 /\
              (!n. ODD n ==> EVEN (n + 1)) /\
              (!n. EVEN n ==> ODD (n + 1))`;
   > val it =
       (|- EVEN 0 /\ (!n. ODD n ==> EVEN (n + 1)) /\
           !n. EVEN n ==> ODD (n + 1),

        |- !EVEN' ODD'.
             EVEN' 0 /\ (!n. ODD' n ==> EVEN' (n + 1)) /\
             (!n. EVEN' n ==> ODD' (n + 1)) ==>
             (!a0. EVEN a0 ==> EVEN' a0) /\ !a1. ODD a1 ==> ODD' a1,

        |- (!a0. EVEN a0 = (a0 = 0) \/
                           ?n. (a0 = n + 1) /\ ODD n) /\
           !a1. ODD a1 = ?n. (a1 = n + 1) /\ EVEN n)

      : thm * thm * thm
```

Defining reflexive and transitive closure, using a schematic variable.
This is appropriate because it is `RTC R` that has the inductive
characterisation, not `RTC` itself.

``` hol4
   - Hol_reln `(!x. RTC R x x) /\
               (!x z. (?y. R x y /\ RTC R y z) ==> RTC R x z)`;
   <<HOL message: inventing new type variable names: 'a>>
   > val it =
       (|- !R. (!x. RTC R x x) /\
               !x z. (?y. R x y /\ RTC R y z) ==> RTC R x z,

        |- !R RTC'.
             (!x. RTC' x x) /\
             (!x z. (?y. R x y /\ RTC' y z) ==> RTC' x z) ==>
             !a0 a1. RTC R a0 a1 ==> RTC' a0 a1,

        |- !R a0 a1. RTC R a0 a1 =
                       (a1 = a0) \/ ?y. R a0 y /\ RTC R y a1)

     : thm * thm * thm
```

### Comments

Being a definition principle, the `Hol_reln` function takes a quotation
rather than a term. The structure `IndDefRules` provides functions for
applying the results of an invocation of `Hol_reln`.

### See also

[`bossLib.Define`](#bossLib.Define),
[`bossLib.Hol_datatype`](#bossLib.Hol_datatype),
[`IndDefRules`](#IndDefRules)
