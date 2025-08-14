## `clear_overloads`

``` hol4
term_grammar.clear_overloads : term_grammar.grammar -> term_grammar.grammar
```

------------------------------------------------------------------------

Remove non-trivial overloading from a term grammar

For a term grammar `tmG`, `clear_overloads tmG` is the similar grammar,
changed to remove non-trivial overloading. (Each constant remains
overloaded with itself, which avoids the printing of the theory name for
every constant).

Sometimes overloading can be too helpful, when we would like to see the
structure of a term (eg, in finding which theorems could simplify it).

### Example

In this example we obtain the current type and term grammars `tyG` and
`tmG`, then reset the current grammars to be these, except with
overloading cleared from the term grammar. We print some theorems (eg,
to view their internal structure), and finally we reset the current
grammars to the original ones.

``` hol4
> ratTheory.RATND_RAT_OF_NUM;
val it = |- (RATN (&n) = &n) /\ (RATD (&n) = 1): thm
> rich_listTheory.MEM_TAKE;
val it = |- !m l. m <= LENGTH l ==> !x. MEM x (TAKE m l) ==> MEM x l: thm

val (tyG, tmG) = Parse.current_grammars () ;
Parse.temp_set_grammars (tyG, term_grammar.clear_overloads tmG) ;

> ratTheory.RATND_RAT_OF_NUM;
val it = |- (RATN (rat_of_num n) = int_of_num n) /\ 
  (RATD (rat_of_num n) = 1n): thm
> rich_listTheory.MEM_TAKE;
val it = |- !m l.  m <= LENGTH l ==>
  !x. x IN LIST_TO_SET (TAKE m l) ==> x IN LIST_TO_SET l: thm

Parse.temp_set_grammars (tyG, tmG) ;
```

### Comments

To print just a few terms without overloading, `print_without_macros`
may be easier.

### See also

[`Parse.print_without_macros`](#Parse.print_without_macros),
[`Parse.current_grammars`](#Parse.current_grammars),
[`Parse.temp_set_grammars`](#Parse.temp_set_grammars)
