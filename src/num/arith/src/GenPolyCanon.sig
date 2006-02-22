signature GenPolyCanon =
sig

include Abbrev
datatype assoc_mode = L | R | L_Cflipped

datatype gci =
         GCI of {dest : term -> term * term,
                 is_literal : term -> bool,
                 assoc_mode : assoc_mode,
                 assoc : thm,
                 symassoc : thm ,
                 comm : thm,
                 l_asscomm : thm ,
                 r_asscomm : thm ,
                 non_coeff : term -> term,
                 merge : term -> thm,
                 postnorm : term -> thm,
                 left_id : thm,
                 right_id : thm ,
                 reducer : term -> thm}

val update_mode : assoc_mode -> gci -> gci
val gencanon : gci -> term -> thm

val derive_l_asscomm : thm -> thm -> thm
val derive_r_asscomm : thm -> thm -> thm

end;

(*

  The gci type stores sufficient information about a type and operators over
  it to allow normalisation of "polynomials" over that type, collecting up
  coefficients etc.

  The required fields of the record are
    dest         : pulls apart a term (e.g., x + y  ->  (x,y))
    is_literal   : returns true iff a term is a numeric literal - in L & R
                   modes literals are shunted to the right end of the term.
                   In L_Cflipped they appear on the front.
    assoc_mode   : how the term should be associated when built.
                     L & R are obvious.  L_Cflipped has non-literals
                     left-associated, but possibly prepended by a literal to
                     the left.  This is appropriate for multiplication, e.g.,
                        c((xy)z)
    assoc        : associativity theorem (e.g., |- x + (y + z) = (x + y) + z)
    symassoc     : associativity theorem with equality flipped
    comm         : commutativity theorem (e.g., |- x + y = y + x)
    l_asscomm    : right-commutativity theorem  (letter 'l' indicates that
                   terms are left-associated)
                      (e.g., |- (x + y) + z = (x + z) + y)
    r_asscomm    : left-commutativity theorem (terms are right-associated)
                      (e.g., |- x + (y + z) = y + (x + z))
    non_coeff    : returns the "base" of a term, ignoring the coefficient.
                      (e.g., x  ->  x,  2 * x  ->  x,  ~y  ->  y,  3  ->  1)
    merge        : takes a term of the form t1 op t2, where t1 and t2 have
                   equal base, and merges them into one by summing
                   coefficients.  The result will be subjected to
                   post-normalisation (see below)
    postnorm     : conversion to normalise certain coeff-term pairs.  Must
                   include the analogue of
                            0 * x  ->  |- 0 * x = 0
                   and might reasonably include
                            x ** 1  ->  |- x ** 1 = x
                            ~1 * x  ->  |- ~1 * x = ~x
                             3 * 1  ->  |- 3 * 1 = 3
    left_id      : theorem stating left-identity for the base operator
                       (e.g.,  |- 0 + x = x  and  |- 1 * x = x)
    right_id     : theorem stating right-identity for the base operator
    reducer      : conversion for doing ground arithmetic on coefficients

  To handle literals, get non_coeff to return a base of 1 for them, and then
  handle their merging separately in the merge function.

  [update_mode m g] returns a g' that is identical to g except that
  the assoc_mode field of the record has been updated to have value m.

  [gencanon g t] returns a theorem of the form |- t = t', where t' is a normal
  form.  The polynomial will be right-associated (for backwards compatibility
  reasons).

  [derive_l_asscomm ass comm] derives an l_asscomm theorem from assoc and comm
  theorems.

  [derive_r_asscomm ass comm] derives an r_asscomm theorem from assoc and comm
  theorems.

*)


