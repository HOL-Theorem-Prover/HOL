signature KernelTypes =
sig

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness: an interactive session may
    create more than one such pair, and they need to be distinguished.
 ---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 *                  HOL types                                                *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Type constants are a three-tuple, containing the following components:    *
 *    1) kernel identifier                                                   *
 *    2) kind                                                                *
 *    3) rank                                                                *
 * Type variables are a three-tuple, containing the following components:    *
 *    1) string (identifier)                                                 *
 *    2) kind                                                                *
 *    3) rank                                                                *
 * Ranks are actually natural numbers >= 0.                                  *
 * Universal types (TyAll) quantify over types of a given rank or lower.     *
 * Bound type variables are represented internally using deBruijn indices    *
 * and explicit substitution. Externally, as always, the interface is to a   *
 * name-carrying syntax.                                                     *
 *---------------------------------------------------------------------------*)

datatype kind = Type
              | Oper of kind * kind

type id = KernelSig.kernelid
type tyconst  =      id * kind * int (* rank *)
type tyvar    =  string * kind * int (* rank *)

datatype hol_type = TyFv of tyvar
                  | TyBv of int
                  | TyCon of tyconst
                  | TyApp of hol_type * hol_type
                  | TyAll of tyvar * hol_type
                  | TyAbs of tyvar * hol_type;


(*---------------------------------------------------------------------------*
 * HOL terms are represented internally using deBruijn indices and explicit  *
 * substitutions. Externally, as always, the interface is to a               *
 * name-carrying syntax.                                                     *
 *---------------------------------------------------------------------------*)

datatype holty = GRND of hol_type
               | POLY of hol_type

val to_hol_type : holty -> hol_type

type tmconst = id * holty

datatype term = Fv of string * hol_type
              | Bv of int
              | Const of tmconst
              | Comb  of term * term
              | TComb of term * hol_type
              | Abs   of term * term
              | TAbs  of tyvar * term
              | Clos  of term Subst.subs * term;


(*---------------------------------------------------------------------------
     The representation of theorems, and their tags
 ---------------------------------------------------------------------------*)

datatype thm = THM of Tag.tag * term HOLset.set * term


(*---------------------------------------------------------------------------
     The type of witnesses, used by the definition principles.
 ---------------------------------------------------------------------------*)

  datatype witness
       = TERM of term
       | THEOREM of thm
end
