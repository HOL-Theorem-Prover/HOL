## `uptodate_thm` {#Theory.uptodate_thm}


```
uptodate_thm : thm -> bool
```



Tells if a theorem is out of date.


Operations in the current theory segment of HOL allow one to redefine
types and constants. This can cause theorems to become invalid. As a
result, HOL has a rudimentary consistency maintenance system built
around the notion of whether type operators and term constants are
"up-to-date".

An invocation `uptodate_thm th` should check `th` to see if it
has been proved from any out-of-date components. However, HOL does
not currently keep the proofs of theorems, so a simpler approach is
taken. Instead, `th` is checked to see if its hypotheses and
conclusions are up-to-date.

All items from ancestor theories are fixed, and unable to
be overwritten, thus are always up-to-date.

### Failure

Never fails.

### Example

    
    - Define `fact x = if x=0 then 1 else x * fact (x-1)`;
    Equations stored under "fact_def".
    Induction stored under "fact_ind".
    > val it = |- fact x = (if x = 0 then 1 else x * fact (x - 1)) : thm
    
    - val th = EVAL (Term `fact 3`);
    > val th = |- fact 3 = 6 : thm
    
    - uptodate_thm th;
    > val it = true : bool
    
    - delete_const "fact";
    > val it = () : unit
    
    - uptodate_thm th;
    > val it = false : bool
    

### Comments

It may happen that a theorem `th` is proved with the use of another
theorem `th1` that subsequently becomes garbage because a
constant `c` was deleted. If `c` does not occur in `th`, then `th` does
not become garbage, which may be contrary to expectation. The conservative
extension property of HOL says that `th` is still provable, even in
the absence of `c`.

### See also

[`Theory.uptodate_type`](#Theory.uptodate_type), [`Theory.uptodate_term`](#Theory.uptodate_term), [`Theory.delete_const`](#Theory.delete_const), [`Theory.delete_type`](#Theory.delete_type)

