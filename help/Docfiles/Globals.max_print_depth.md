## `max_print_depth` {#Globals.max_print_depth}


```
max_print_depth : int ref
```



Sets depth bound on prettyprinting.


The reference variable `max_print_depth` is used to define the
maximum depth of printing for the pretty printer. If the number of
blocks (an internal notion used by the prettyprinter) becomes greater
than the value set by `max_print_depth` then the blocks are
abbreviated by the holophrast `...`. By default, the value of
`max_print_depth` is `~1`. This is interpreted to mean ‘print everything’.

### Failure

Never fails.

### Example

To change the maximum depth setting to `10`, the command will be:
    
       - max_print_depth := 10;
       > val it = () : unit
    
The theorem `numeralTheory.numeral_distrib` then prints as
follows:
    
    - numeralTheory.numeral_distrib;
    > val it =
        |- (!n. 0 + n = n) /\ (!n. n + 0 = n) /\
           (!n m. NUMERAL n + NUMERAL m = NUMERAL (iZ (n + m))) /\
           (!n. 0 * n = 0) /\ (!n. n * 0 = 0) /\
           (!n m. ... ... * ... ... = NUMERAL (... * ...)) /\
           (!n. ... - ... = 0) /\ (!n. ... = ...) /\ (!... .... ...) /\ ... /\ ...
         : thm
    


