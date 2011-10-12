signature AC_Sort =
sig

  include Abbrev
  val sort : {assoc : thm, comm : thm,
              dest : term -> term * term, mk : term * term -> term,
              cmp : term * term -> order,
              combine : conv, preprocess : conv} -> conv

end

(*

  [sort {assoc,comm,dest,mk,cmp,combine,preprocess}] is a conversion for
  sorting terms with respect to an associative and commutative operator.
  It uses a merge sort internally, so should be reasonably efficient.

  The record's fields are:

    assoc:      associativity theorem in standard r-to-l format:
                 a + (b + c) = (a + b) + c
                can be universally quantified

    comm:       commutativity theorem (can be universally quantified)

    dest:       destructor function for operator

    mk:         constructor function for operator

    cmp:        comparison function for performing sort.  Terms identified
                as EQUAL will be combined by combine conversion.

    combine:    conv taking terms of the form (t1 op t2) where t1 and t2
                have compared as equal.  Should always succeed (can be
                ALL_CONV).

    preprocess: applied to all leaf terms as term is first examined.
                If it fails or raises UNCHANGED (i.e., both ALL_CONV and
                NO_CONV are OK here), nothing further is done.  If it
                succeeds, further processing is performed on the resulting
                term

   E.g., combine can combine numeric literals; preprocess could convert
   a - b into a + -b, or -x into -1 * x, or ~~p into p.

*)
