structure KernelTypes :> KernelTypes =
struct

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness (an interactive session may
    create more than one such pair, and they need to be distinguished).
 ---------------------------------------------------------------------------*)

type id = KernelSig.kernelid

(*---------------------------------------------------------------------------*
 *                  HOL ranks                                                *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Ranks are actually the (single) rank variable plus a natural number >= 0. *
 *---------------------------------------------------------------------------*)

type rank = int (* >= 0 *)

(*---------------------------------------------------------------------------*
 *                  HOL kinds                                                *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Kinds contain their rank within each base kind and kind variable.         *
 *---------------------------------------------------------------------------*)

datatype kind = Type of rank
              | KdVar of string * rank
              | Oper of kind * kind

(*---------------------------------------------------------------------------*
 *                  HOL types                                                *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Type constants are a two-tuple, containing the following components:      *
 *    1) kernel identifier                                                   *
 *    2) kind                                                                *
 * Type variables are a two-tuple, containing the following components:      *
 *    1) string (identifier)                                                 *
 *    2) kind                                                                *
 * Universal types (TyAll) quantify over types of a given rank or lower.     *
 * Bound type variables are represented internally using deBruijn indices    *
 * and explicit substitution. Externally, as always, the interface is to a   *
 * name-carrying syntax.                                                     *
 *---------------------------------------------------------------------------*)

type id = KernelSig.kernelid
type tyconst  =  id * kind
type tyvar = string * kind

datatype hol_type = TyFv of tyvar
                  | TyBv of int
                  | TyCon of tyconst
                  | TyApp of hol_type * hol_type
                  | TyAbs of tyvar * hol_type
                  | TyAll of tyvar * hol_type
                  | TyExi of tyvar * hol_type;


(*---------------------------------------------------------------------------*
 * HOL terms are represented internally using deBruijn indices and explicit  *
 * substitutions. Externally, as always, the interface is to a               *
 * name-carrying syntax. The "holty" field in tmconst tells whether the      *
 * constant is polymorphic or not. Currently, this is only an approximation: *
 * if it is GRND, then the constant has no type variables. If POLY, the      *
 * constant may or may not have type variables.                              *
 *---------------------------------------------------------------------------*)

datatype holty = GRND of hol_type
               | POLY of hol_type

fun to_hol_type (GRND ty) = ty
  | to_hol_type (POLY ty) = ty;

type tmconst = id * holty

datatype term = Fv of string * hol_type
              | Bv of int
              | Const of tmconst
              | Comb  of term * term
              | TComb of term * hol_type
              | Abs   of term * term
              | TAbs  of tyvar * term
              | Clos  of term Subst.subs * term
           (* | HackHack of bool -> bool *)
           (* Because of the hol_type fields, that need to compared using eq_ty for
              alpha-, beta-, and eta-equivalence between types, terms should *not*
              be compared with the built-in equality,
              but should use "eq" defined in Term.sml.
              To check this has been done everywhere, uncomment this constructor. *)
              ;

(*---------------------------------------------------------------------------
      The representation of theorems. A "tag" is a pair of the oracles
      used and the axioms used. Oracles are represented as ordered lists
      of strings, and axioms are lists of string refs.
 ---------------------------------------------------------------------------*)

datatype thm = THM of Tag.tag * term HOLset.set * term

(*---------------------------------------------------------------------------
     The type of witnesses for definitions, used in Theory.
 ---------------------------------------------------------------------------*)

datatype witness = TERM of term | THEOREM of thm

end
