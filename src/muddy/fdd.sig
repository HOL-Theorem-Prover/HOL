local 
  open bdd
in

  type precision = int
  type domain = int
  type fddvar

  val extDomain: domain list -> fddvar list
  val clearAll: unit -> unit
  val domainNum: unit -> int
  val domainSize: fddvar -> domain
  val varNum: fddvar -> precision
  val vars: fddvar -> varnum list
  val ithSet: fddvar -> varSet
  val domain: fddvar -> bdd
  val setPairs: (fddvar * fddvar) list -> pairSet
end

(* fdd

Implements BuDDy's fdd functions.

The following table shows how ML types and values in this modules
relates to C types and function declarations in fdd.h:

MuDDy       BuDDy                   Comment
-----------------------------------------------------------------
Types:
precision   int
domain      int
fddvar      int

Values:
extDomain   fdd_extdomain
?	    fdd_overlapdomain
clearAll    fdd_clearall
domainNum   fdd_domainnum
domainSize  fdd_domainsize
varNum	    fdd_varnum
vars	    fdd_vars
?	    fdd_ithvar
?	    fdd_scanvar
?	    fdd_scanallvar
ithSet	    fdd_ithset
domain	    fdd_domain
?	    fdd_equals
?	    fdd_file_hook
?	    fdd_printset
?	    fdd_fprintset
?	    fdd_scanset
makeSet     fdd_makeset
?	    fdd_intaddvarblock
?           fdd_setpair              (use setPair)
setPairs    fdd_setpairs

*)
