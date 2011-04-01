signature KernelTypes =
sig

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness: an interactive session may
    create more than one such pair, and they need to be distinguished.
 ---------------------------------------------------------------------------*)

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
type tyconst  =      id * kind
type tyvar    =  string * kind

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
              | Clos  of term Subst.subs * term
           (* | HackHack of bool -> bool *)
           (* Because of the hol_type fields, that need to compared using abconv_ty for
              alpha- and beta-equivalence between types, terms should *not* be compared
              with the built-in equality, but should use "eq" defined in Term.sml.
              To check this has been done everywhere, uncomment this constructor. *)
              ;


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
