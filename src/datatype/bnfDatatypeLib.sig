signature bnfDatatypeLib =
sig

  include Abbrev

  (* ----------------------------------------------------------------------
      The package's entry point: a specification as written, to a
      datatype the rest of HOL can use.

        bnfDatatype `stack[map=STMAP] = Empty | Push 'a stack`

      What it does, in order: parses the specification and the names it
      asks for; builds the type — the fixed point when the
      specification recurses, a copy of the functor when it does not;
      splits the constructor along the functor's shape; derives the
      axiom, the induction principle and the case constants; registers
      the type as a functor of its own, so a later specification can
      recurse through it; and makes the TypeBase entry, with the size
      function and the map and set equations in its simplification set.

      The theorems are saved under the names the old package uses —
      <ty>_11, <ty>_distinct, <ty>_nchotomy, <ty>_Axiom, <ty>_induction,
      <ty>_case_cong, <ty>_case_eq — so that a development that says
      nothing about which package defined its types does not notice.
     ---------------------------------------------------------------------- *)
  val bnfDatatype : hol_type quotation -> unit

  (* the same for a caller that has parsed already, which is what the
     older entry point's syntax needs *)
  val bnfDatatypeASTs : ParseDatatype.AST list -> unit

  (* Whether this construction can express the specification: every
     occurrence of a type it defines has to be somewhere a map can move
     it.  A recursion through an operator that holds no elements of its
     argument — `t = c of 'a => t itself` — is not something a fixed
     point can be taken of, and the caller sends it elsewhere. *)
  val expressible : ParseDatatype.AST list -> bool


  (* the same, handing back the entries it made, for a caller that wants
     to look at them rather than trust them *)
  val bnfDatatypeInfo : hol_type quotation -> TypeBasePure.tyinfo list

  (* ----------------------------------------------------------------------
      Registering a functor the package built, by name: the database
      records a theorem's name rather than the theorem, so each law is
      saved in the current theory first.  The names are the type's, with
      the law's own suffix.
     ---------------------------------------------------------------------- *)
  val registerBNF : {tyname : string} ->
                    KernelSig.kernelname * thm bnfBase_dtype.info -> unit

end
