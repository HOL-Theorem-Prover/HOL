## `PROVE` {#bossLib.PROVE}


```
PROVE : thm list -> term -> thm
```



Prove a theorem with use of supplied lemmas.


An invocation `PROVE thl M` attempts to prove `M` using an automated
reasoner supplied with the lemmas in `thl`. The automated reasoner
performs a first order proof search. It currently provides some support
for polymorphism and higher-order values (lambda terms).

### Failure

If the proof search fails, or if `M` does not have type `bool`.

### Example

    
    - PROVE []  (concl SKOLEM_THM);
    Meson search level: ........
    > val it = |- !P. (!x. ?y. P x y) = ?f. !x. P x (f x) : thm
    
    - let open arithmeticTheory
      in
        PROVE [ADD_ASSOC, ADD_SYM, ADD_CLAUSES]
          (Term `x + 0 + y + z = y + (z + x)`)
      end;
    Meson search level: ............
    > val it = |- x + 0 + y + z = y + (z + x) : thm
    

### Comments

Some output (a row of dots) is currently generated as `PROVE` works. If
the frequency of dot emission becomes slow, that is a sign that the
term is not likely to be proved with the current lemmas.

Unlike `MESON_TAC`, `PROVE` can handle terms with conditionals.

### See also

[`bossLib.PROVE_TAC`](#bossLib.PROVE_TAC), [`mesonLib.MESON_TAC`](#mesonLib.MESON_TAC), [`mesonLib.ASM_MESON_TAC`](#mesonLib.ASM_MESON_TAC)

