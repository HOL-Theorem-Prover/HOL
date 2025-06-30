# The Mechanisation of [Barendregt 1984]

chap2Script.sml :
               mechanisation of chapter 2 of Hankin's "Lambda calculi:
               a guide for computer scientists"

chap3Script.sml :
               mechanisation of much of chapter 3 of Hankin with bits
               of Barendregt's chapter 3 thrown in too

chap11_1Script.sml :
               mechanisation of section 11.1 from Barendregt's "The
               lambda calculus: its syntax and semantics"

horeductionScript.sml :
head_reductionScript.sml :

term_posnsScript.sml :
               establishes a type for labelling reductions, and
               positions within terms more generally

labelledTermsScript.sml :
               establishes the type of lambda calculus
               terms with labelled redexes.  Called $\Lambda'$ in
               Barendregt.

finite_developmentsScript.sml :
               Barendregt's proof of the finite-ness of developments
               (section 11.2), mechanising this notion as well as that
               of residuals.

standardisationScript.sml :
               Barendregt's proof of the standardisation theorem, from
               section 11.4.

                    ------------------------------

These files are behind the papers:

  "Mechanising Hankin and Barendregt using the Gordon-Melham axioms"
  Michael Norrish
  Proceedings of the Merlin 2003 Workshop

and

  "Mechanising \lambda-calculus using a classical first order theory
   of terms with permutations"
  Michael Norrish
  In "Higher Order and Symbolic Computation", 19:169-195, 2006.

solvableScript.sml :
      solvability of lambda-terms; Wadsworth's theorem (solvable iff has_hnf)
    
boehmScript.sml :
      Effective Boehm trees

lameta_completeScript.sml :
      Hilbert-Post Completeness of Lambda-Eta-Calculus

takahashiS3Script.sml :
      Section 3 of Takahashi's paper (has_benf iff has_bnf)

These files are new work.

# Coverage of [Barendregt 1984] (and other materials)

| Chapter/Section | Theory                     |
|---------------- | -------------------------- |
| 2               | term, chap2                |
| 3               | horeduction, chap3         |
| 4               | chap4                      |
| 8.3             | `head_reduction`, solvable |
| 10.1,10.3       | boehm                      |
| 10.4            | `lameta_complete`          |
| 11.1            | `chap11_1`                 |
| 11.2            | `finite_developments`      |
| 11.4            | standardisation            |
| 15.1            | takahashiS3 [*]            |

[*] The proofs of Chapter 15.1 are done by Takahashi's new methods.
