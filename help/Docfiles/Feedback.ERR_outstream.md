## `ERR_outstream` {#Feedback.ERR_outstream}


```
ERR_outstream : TextIO.outstream ref
```



Reference to output stream used when printing `HOL_ERR`


The value of reference cell `ERR_outstream` controls where `Raise`
prints its argument.

The default value of `ERR_outstream` is `TextIO.stdErr`.

### Example

    
    - val ostrm = TextIO.openOut "foo";
    > val ostrm = <outstream> : outstream
    
    - ERR_outstream := ostrm;
    > val it = () : unit
    
    - Raise (mk_HOL_ERR "Foo" "bar" "incomprehensible input");
    ! Uncaught exception:
    ! HOL_ERR
    
    - TextIO.closeOut ostrm;
    > val it = () : unit
    
    - val istrm = TextIO.openIn "foo";
    > val istrm = <instream> : instream
    
    - print (TextIO.inputAll istrm);
    
    Exception raised at Foo.bar:
    incomprehensible input
    



### See also

[`Feedback`](#Feedback), [`Feedback.HOL_ERR`](#Feedback.HOL_ERR), [`Feedback.Raise`](#Feedback.Raise), [`Feedback.MESG_outstream`](#Feedback.MESG_outstream), [`Feedback.WARNING_outstream`](#Feedback.WARNING_outstream)

