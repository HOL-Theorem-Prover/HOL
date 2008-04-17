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

  val mk_id        : name * segment -> id
  val dest_id      : id -> name * segment
  val uptodate_id  : id -> bool
  val name_of      : id -> name
  val seg_of       : id  -> segment
  val compare      : id * id -> order
  val same_id      : id * id -> bool
  val retire       : id -> unit
  val fullname     : name * segment -> string
  val id_to_string : id -> string


(*---------------------------------------------------------------------------*
 *                  HOL types                                                *
 *---------------------------------------------------------------------------*)

type tyconst = id * int

datatype hol_type = Tyv of string
                  | Tyapp of tyconst * hol_type list;


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
              | Abs   of term * term
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
