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
fun retire r = let val (n,t) = dest_id r in r := (!Globals.old n, t) end
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

type tyconst = id * int

datatype hol_type = Tyv of string
                  | Tyapp of tyconst * hol_type list;


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
              | Abs   of term * term
              | Clos  of term Subst.subs * term;

(*---------------------------------------------------------------------------
      The representation of theorems. A "tag" is a pair of the oracles
      used and the axioms used. Oracles are represented as ordered lists
      of strings, and axioms are lists of string refs.
 ---------------------------------------------------------------------------*)

datatype tag = TAG of string list * string ref list

datatype thm = THM of tag * term HOLset.set * term

(*---------------------------------------------------------------------------
     The type of witnesses for definitions, used in Theory.
 ---------------------------------------------------------------------------*)

datatype witness = TERM of term | THEOREM of thm

end
