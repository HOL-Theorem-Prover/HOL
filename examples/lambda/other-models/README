dBScript.sml
   develops a theory of (untyped) "locally nameless" de Bruijn terms.

ncScript.sml
   builds a theory of name-carrying terms, where terms are identified
   up to alpha-conversion.  This development underlies the paper

                "5 Axioms of Alpha Conversion",
                 Andy Gordon and Tom Melham,
                 Proceedings of TPHOLs'96, Springer LNCS 1125.

   Proves a recursion combinator for these terms as per the paper 

                "Recursive Function Definition for Types with Binders"
                 Michael Norrish
                 Proceedings of TPHOLs'2004, Springer LNCS 3223

gmtermScript.sml
   develops a theory of "traditional" lambda-calculus terms by
   creating a type like that in ncScript, but without the CON
   constructor.  

                    ------------------------------

diagsScript.sml
   a type of rewriting style diagrams and how rewriting relations do
   or do not satisfy them.  Also a proof that "diagram-satisfaction"
   is preserved and reflected by strong onto homomorphisms.  (This is
   discussed in the NICTA/JAIST technical report "Structural
   preservation and reflection of diagrams", and is joint work with
   René Vestergaard.)

raw_syntaxScript.sml
   proof that a raw syntax of lambda terms (not identified up to alpha
   equivalence) with its own notions of substitution, alpha
   equivalence and beta reduction can indeed be collapsed into the
   type of terms from termTheory.  Use diagrams to show confluence for
   beta-alpha reduction at this raw level by appeal to result in
   barendregt/chap3Theory.

                    ------------------------------

string_numScript.sml
   a proof by construction that strings and numbers are in bijection

pure_dBScript.sml
   mechanisation of the type of "pure" de Bruijn terms, following
   Tobias Nipkow's paper "More Church-Rosser Proofs".  (They are
   "pure" in contrast with Andy Gordon's de Bruijn terms, which have
   indices for bound variables and strings for free variables.)

   Demonstration that this type and its notions of beta- and
   eta-reduction are isomorphic to the quotiented type in termTheory.
   This work is described in

                "Proof Pearl: de~Bruijn Terms Really Do Work"
                 Michael Norrish and René Vestergaard
                 Proceedings of TPHOLs'2007, Springer LNCS 4732

                    ------------------------------

MPlambdaScript.sml
   Mechanisation of the McKinna-Pollack two-sorted lambda-calculus.

                    ------------------------------

lnamelessScript.sml
   Mechanisation of the approach from the POPL paper "Engineering
   Formal Metatheory" by Brian Aydemir, Arthur Charguéraud, Benjamin
   Pierce, Randy Pollack and Stephanie Weirich.  That paper is more
   concerned with typing the simple lambda calculus than
   beta-reduction, so that's what's covered here too.  (Further, these
   locally nameless terms are basically the same as Andy Gordon's dB
   terms.)

