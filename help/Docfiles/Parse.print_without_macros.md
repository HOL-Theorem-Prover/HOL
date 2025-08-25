## `print_without_macros`

``` hol4
Parse.print_without_macros : term -> unit
```

------------------------------------------------------------------------

Prints a term to standard output, using the current grammars but without
non-trivial overloading

Where `print_term` uses the (implicit) global grammars to control the
printing of its term argument, the `print_without_macros` uses these
grammars, modified to remove non-trivial overloading. (Each constant is
overloaded with itself, which avoids the printing of the theory name for
every constant).

### Failure

Never fails.

Sometimes one wants to see how a term is built up, where the
pretty-printing simplifies it to the point where this is not clear.

For example:

``` hol4
``MEM`` ;
val it = ``\x l. MEM x l`` ;
print_without_macros ``MEM`` ;
 \x l. x IN LIST_TO_SET l

concl ratTheory.RATND_RAT_OF_NUM ;
val it = (RATN (&n) = &n) /\ (RATD (&n) = 1): term
Parse.print_without_macros (concl ratTheory.RATND_RAT_OF_NUM) ;
(RATN (rat_of_num n) = int_of_num n) /\ (RATD (rat_of_num n) = 1n)
```

### Comments

To change the (implicit) global grammars to remove overloading, see
`clear_overloads`

### See also

[`Parse.print_term_by_grammar`](#Parse.print_term_by_grammar),
[`term_grammar.clear_overloads`](#term_grammar.clear_overloads)
