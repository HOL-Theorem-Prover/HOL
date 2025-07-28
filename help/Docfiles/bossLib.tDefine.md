## `tDefine` {#bossLib.tDefine}


```
tDefine : string -> term quotation -> tactic -> thm
```



General-purpose function definition facility.


`tDefine` is a definition package similar to `Define` except that it
has a tactic parameter which is used to perform the termination proof
for the specified function. `tDefine` accepts the same syntax used by
`Define` for specifying functions.

If the specification is a simple abbreviation, or is primitive
recursive (i.e., it exactly follows the recursion pattern
of a previously declared HOL datatype) then the invocation of
`tDefine` succeeds and stores the derived equations in the
current theory segment. Otherwise, the function is not an instance of
primitive recursion, and the termination prover may succeed or fail.

When processing the specification of a recursive function,
`tDefine` must perform a termination proof. It automatically constructs
termination conditions for the function, and invokes the supplied
tactic in an attempt to prove the termination conditions. If that
attempt fails, then `tDefine` fails.

If it succeeds, then `tDefine` stores the specified equations in the
current theory segment, using the string argument as a stem for the name.
An induction theorem customized for the defined function is also
stored in the current segment. Note, however, that an induction
theorem is not stored for primitive recursive functions, since that
theorem would be identical to the induction theorem resulting from the
declaration of the datatype.

If the tactic application fails, then `tDefine` fails.

### Failure

`tDefine` fails if its input fails to parse and typecheck.

`tDefine` fails if it cannot prove the termination of the
specified recursive function. In that case, one has to embark on the
following multi-step process: (1) construct the function and synthesize its
termination conditions with `Hol_defn`; (2) set up a goal to prove the
termination conditions with `tgoal`; (3) interactively prove the
termination conditions, usually by starting with an invocation of
`WF_REL_TAC`; and (4) package everything up with an invocation
of `tDefine`.



### Example

The following attempt to invoke `Define` fails because the
current default termination prover for `Define` is too weak:
    
       Hol_datatype`foo = c1 | c2 | c3`;
    
       Define `(f c1 x = x) /\
               (f c2 x = x + 3) /\
               (f c3 x = f c2 (x + 6))`;
    
The following invocation of `tDefine` uses the supplied tactic
to prove termination.
    
       tDefine "f"
          `(f c1 x = x) /\
           (f c2 x = x + 3) /\
           (f c3 x = f c2 (x + 6))`
        (WF_REL_TAC `measure (\p. case FST p of c3 -> 1 || _ -> 0)`);
    
       Equations stored under "f_def".
       Induction stored under "f_ind".
       > val it = |- (f c1 x = x) /\ (f c2 x = x + 3) /\ (f c3 x = f c2 (x + 6)) : thm
    

### Comments

`tDefine` automatically adds the definition it makes into the hidden
‘compset‘ accessed by `EVAL` and `EVAL_TAC`.

### See also

[`bossLib.Define`](#bossLib.Define), [`bossLib.xDefine`](#bossLib.xDefine), [`TotalDefn.DefineSchema`](#TotalDefn.DefineSchema), [`bossLib.Hol_defn`](#bossLib.Hol_defn), [`Defn.tgoal`](#Defn.tgoal), [`Defn.tprove`](#Defn.tprove), [`bossLib.WF_REL_TAC`](#bossLib.WF_REL_TAC), [`bossLib.recInduct`](#bossLib.recInduct), [`bossLib.EVAL`](#bossLib.EVAL), [`bossLib.EVAL_TAC`](#bossLib.EVAL_TAC)

