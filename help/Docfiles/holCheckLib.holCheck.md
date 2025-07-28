## `holCheck` {#holCheckLib.holCheck}


```
holCheck : model -> model
```



Basic symbolic model checker.


User specifies a model by specifying (at least) the initial states, a labelled transition system, and a list of CTL or mu-calculus propertes. This model is then passed to the model checker which returns the model with the results of the checking filled in. These can be recovered by calling get_results on the returned model and are presented as a list of : the BDD semantics of each property, a theorem if the property holds in the model, and a counterexample or witness trace if appropriate.

### Failure

holCheck should not fail, except on malformed input e.g. mu-calculus properties that are not well-formed mu-formulas or a supplied state tuple that does not include all state variables etc.

### Example

We choose a mod-8 counter as our example, which starts at 0 and counts up to 7, and then loops from 0 again. We wish to show that the most significant bit eventually goes high.

1. Load the HolCheck library:
    
    - load "holCheckLib"; open holCheckLib; (* we don't show the output from the "open" here *)
    > val it = () : unit
    

2. Specify the labelled transition system as a list of (string, term) pairs, where each string is a transition label and each term represents a transition relation (three booleans required to encode numbers 0-7; next-state variable values indicated by priming; note we expand the xor, since HolCheck requires purely propositional terms) :
    
    - val xor_def = Define `xor x y = (x \/ y) /\ ~(x=y)`;
      val TS = List.map (I ## (rhs o concl o (fn tm => REWRITE_CONV [xor_def] tm handle ex => REFL tm)))
    				  [("v0",``(v0'=~v0)``),("v1",``v1' = xor v0 v1``),("v2",``v2' = xor (v0 /\ v1) v2``)]
    Definition has been stored under "xor_def".
    > val xor_def = |- !x y. xor x y = (x \/ y) /\ ~(x = y) : thm
    > val TS =
        [("v0", ``v0' = ~v0``), ("v1", ``v1' = (v0 \/ v1) /\ ~(v0 = v1)``),
         ("v2", ``v2' = (v0 /\ v1 \/ v2) /\ ~(v0 /\ v1 = v2)``)] :
      (string * term) list
    

3. Specify the initial states (counter starts at 0):
    
    - val S0 = ``~v0 /\ ~v1 /\ ~v2``;
    > val S0 = ``~v0 /\ ~v1 /\ ~v2`` : term
    

4. Specify whether the transitions happen synchronously (it does):
    
    - val ric = true;
    > val ric = true : bool
    

5. Set up the state tuple:
    
    - val state = mk_state S0 TS;
    > val state = ``(v0,v1,v2)`` : term
    

6. Specify a property (there exists a future in which the most significant bit will go high) :
    
    - val ctlf = ("ef_msb_high",``C_EF (C_BOOL (B_PROP ^(pairSyntax.mk_pabs(state,``v2:bool``))))``);
    > val ctlf = ("ef_msb_high",``C_EF (C_BOOL (B_PROP (\(v0,v1,v2). v2))``) : string * term
    

Note how atomic propositions are represented as functions on the state.

7. Create the model:
    
    - val m = ((set_init S0) o (set_trans TS) o (set_flag_ric ric) o (set_state state) o  (set_props [ctlf])) empty_model;
    > val m = <model> : model
    

8. Call the model checker:
    
    - val m2 = holCheck m;
    > val m2 = model : <model>
    

9. Examine the results:
    
    - get_results m2;
    > val it =
        SOME [(<term_bdd>,
               SOME [............................]
                   |- CTL_MODEL_SAT ctlKS (C_EF (C_BOOL (B_PROP (\(v0,v1,v2). v2)))),
               SOME [``(~v0,~v1,~v2)``, ``(v0,~v1,~v2)``, ``(~v0,v1,~v2)``,
                     ``(v0,v1,~v2)``, ``(~v0,~v1,v2)``])] :
      (term_bdd * thm option * term list option) list option
    

The result is a list of triples, one triple per property checked. The first component contains the BDD representation of the set of states satisfying the property. The second component contains a theorem certifying that the property holds in the model i.e. it holds in the initial states. The third contains a witness trace that counts up to 4, at which point v2 goes high.

Note that since we did not supply a name for the model (via holCheckLib.set_name), the system has chosen the default name ctlKS, which stands for "CTL Kripke structure", since models are internally represented formally as Kripke structures.

10. Verify the proof:
    
    - val m3 = prove_model m2; (* we don't show the prove_model "chatting" messages here *)
    > val m3 = <model> : model
    

11. Examine the verified results:
    
    - get_results m3;
    > val it =
        SOME [(<term_bdd>,
               SOME|- CTL_MODEL_SAT ctlKS (C_EF (C_BOOL (B_PROP (\(v0,v1,v2). v2)))),
               SOME [``(~v0,~v1,~v2)``, ``(v0,~v1,~v2)``, ``(~v0,v1,~v2)``,
                     ``(v0,v1,~v2)``, ``(~v0,~v1,v2)``])] :
      (term_bdd * thm option * term list option) list option
    

Note that the theorem component now has no assumptions. Any assumptions to the term_bdd would also have been discharged.

### Comments

For more detail, read the section on the HolCheck library in the HOL System Description.

### See also

[`holCheckLib.empty_model`](#holCheckLib.empty_model), [`holCheckLib.get_init`](#holCheckLib.get_init), [`holCheckLib.get_trans`](#holCheckLib.get_trans), [`holCheckLib.get_flag_ric`](#holCheckLib.get_flag_ric), [`holCheckLib.get_name`](#holCheckLib.get_name), [`holCheckLib.get_vord`](#holCheckLib.get_vord), [`holCheckLib.get_state`](#holCheckLib.get_state), [`holCheckLib.get_props`](#holCheckLib.get_props), [`holCheckLib.get_results`](#holCheckLib.get_results), [`holCheckLib.get_flag_abs`](#holCheckLib.get_flag_abs), [`holCheckLib.set_init`](#holCheckLib.set_init), [`holCheckLib.set_trans`](#holCheckLib.set_trans), [`holCheckLib.set_flag_ric`](#holCheckLib.set_flag_ric), [`holCheckLib.set_name`](#holCheckLib.set_name), [`holCheckLib.set_vord`](#holCheckLib.set_vord), [`holCheckLib.set_state`](#holCheckLib.set_state), [`holCheckLib.set_props`](#holCheckLib.set_props), [`holCheckLib.set_flag_abs`](#holCheckLib.set_flag_abs), [`holCheckLib.mk_state`](#holCheckLib.mk_state), [`holCheckLib.prove_model`](#holCheckLib.prove_model)

