(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)
signature fdd =
sig
    type precision = int
    type domain = int
    type fddvar

    val extDomain: domain list -> fddvar list
    val clearAll: unit -> unit
    val domainNum: unit -> int
    val domainSize: fddvar -> domain
    val varNum: fddvar -> precision
    val vars: fddvar -> bdd.varnum list
    val ithSet: fddvar -> bdd.varSet
    val domain: fddvar -> bdd.bdd
    val setPairs: (fddvar * fddvar) list -> bdd.pairSet
end

(* Structure fdd implements BuDDy's fdd functions.

  Type [precision] is used to express the number of bits in an fdd.

  Type [domain] is used to express a domain size.  A value n
  represents a domain [0..(n-1)].

  Type [fddvar] is the type of fdd variables.  An fdd variable
  represents a set of bdd variables.

  [extDomain [d1, ..., dn] ] returns a list of fddvars [v1, ... vn].
  The domain di represents the domain of the i'th variable vi.  See
  also [ordering].

  [clearAll()], [domainNum() ], [domainSize v], [varNum v], [vars v],
  [ithSet v], [domain v], [setPairs pairl]: see the Buddy
  documentation.

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
  ?	      fdd_overlapdomain
  clearAll    fdd_clearall
  domainNum   fdd_domainnum
  domainSize  fdd_domainsize
  varNum      fdd_varnum
  vars	      fdd_vars
  ?	      fdd_ithvar
  ?	      fdd_scanvar
  ?	      fdd_scanallvar
  ithSet      fdd_ithset
  domain      fdd_domain
  ?	      fdd_equals
  ?	      fdd_file_hook
  ?	      fdd_printset
  ?	      fdd_fprintset
  ?	      fdd_scanset
  makeSet     fdd_makeset
  ?	      fdd_intaddvarblock
  ?           fdd_setpair              (use setPair)
  setPairs    fdd_setpairs
*)
