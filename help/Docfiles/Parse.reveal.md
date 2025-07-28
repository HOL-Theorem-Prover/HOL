## `reveal` {#Parse.reveal}


```
reveal : string -> unit
```



Restores recognition of a constant by the quotation parser.


A call `reveal c`, where `c` the name of a (perhaps) hidden constant,
will ‘unhide’ the constant, that is, will make the quotation parser map
the identifier `c` to all current constants with the same name (there may
be more than one such as different theories may re-use the same name).

### Failure

Never fails, but prints a warning message if the string does not
correspond to an actual constant.

### Comments

The hiding of a constant only affects the quotation parser;
the constant is still there in a theory.  If the parameter `c` is
already overloaded so as to map to other constants, these overloadings
are not altered.

### See also

[`Parse.hide`](#Parse.hide), [`Parse.hidden`](#Parse.hidden), [`Parse.remove_ovl_mapping`](#Parse.remove_ovl_mapping), [`Parse.update_overload_maps`](#Parse.update_overload_maps)

