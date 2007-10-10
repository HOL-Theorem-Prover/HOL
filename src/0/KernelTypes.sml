structure KernelTypes :> KernelTypes =
struct

(*---------------------------------------------------------------------------
    Elements in signatures are determined by a (name,theory) pair.
    The reference cell is for uniqueness (an interactive session may
    create more than one such pair, and they need to be distinguished).
 ---------------------------------------------------------------------------*)

type name   = string
type segment = string

type id = (name * segment) ref

fun mk_id p = ref p
fun dest_id ((ref p):id) = p
fun name_of id = #1(dest_id id)
fun seg_of id  = #2(dest_id id)
fun retire r = let val (n,t) = dest_id r in r := (Globals.old n, t) end
val same_id = (op=);
fun compare (id1,id2) =
  case String.compare (name_of id1, name_of id2)
   of EQUAL => String.compare (seg_of id1, seg_of id2)
    |   x   => x;

fun fullname (name,thy) = Lib.quote(String.concat[thy,"$",name]);
fun id_to_string (ref p) = fullname p;

(*---------------------------------------------------------------------------*
 * HOL types are somewhat akin to terms in first order logic.                *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * The kind in type constants and variables regulates the formation of types.*
 * The int in type constants and variables is the rank.                      *
 * The rank is actually a natural number >= 0.                               *
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
              | Clos  of term Subst.subs * term;

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
