structure Type_dtype =
struct

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness (an interactive session may
    create more than one such pair, and they need to be distinguished).
 ---------------------------------------------------------------------------*)

type id = KernelSig.kernelid

(*---------------------------------------------------------------------------*
 * HOL types are somewhat akin to terms in first order logic.                *
 *---------------------------------------------------------------------------*)

type tyconst = id * int

datatype hol_type = Tyv of string
                  | Tyapp of tyconst * hol_type list;

(*---------------------------------------------------------------------------*
 * The "holty" wrapper on tmconst tells whether the constant is polymorphic  *
 * or not.  Currently, this is only an approximation: if it is GRND, then    *
 * the constant has no type variables.  If POLY, the constant may or may     *
 * not have type variables.                                                  *
 *---------------------------------------------------------------------------*)

datatype holty = GRND of hol_type
               | POLY of hol_type

fun to_hol_type (GRND ty) = ty
  | to_hol_type (POLY ty) = ty;

end
