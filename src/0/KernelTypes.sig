signature KernelTypes =
sig

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness: an interactive session may
    create more than one such pair, and they need to be distinguished.
 ---------------------------------------------------------------------------*)

type name    = string
type segment = string

eqtype id

  val mk_id    : name * segment -> id
  val dest_id  : id -> name * segment
  val name_of  : id -> name
  val seg_of   : id  -> segment
  val compare  : id * id -> order
  val same_id  : id * id -> bool
  val retire   : id -> unit
  val fullname : name * segment -> string
  val id_to_string : id -> string


(*---------------------------------------------------------------------------*
 *                  HOL types                                                *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * The first int in type constants and variables is the arity.               *
 * The second int in type constants and variables is the rank.               *
 * Both ints are actually natural numbers >= 0.                              *
 * Universal types (TyAll) quantify over types of a given rank or lower.     *
 * Bound type variables are represented internally using deBruijn indices    *
 * and explicit substitution. Externally, as always, the interface is to a   *
 * name-carrying syntax.                                                     *
 *---------------------------------------------------------------------------*)

datatype kind = Type
              | Oper of kind * kind

type tyconst  =  id * kind * int (* rank *)
type tyvar = string * kind * int (* rank *)

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
