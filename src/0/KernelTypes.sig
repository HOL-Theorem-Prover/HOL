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
  val retire   : id -> unit
  val fullname : name * segment -> string
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

datatype term = Fv of {Name:string, Ty:hol_type}
              | Bv of int
              | Const of tmconst
              | Comb  of {Rator:term, Rand:term}
              | Abs   of {Bvar:term,  Body:term}
              | Clos  of {Env:term Subst.subs, Body:term};


(*---------------------------------------------------------------------------
     The representation of theorems, and their tags
 ---------------------------------------------------------------------------*)

datatype tag = TAG of string list * string ref list

datatype thm = THM of tag * term list * term


(*---------------------------------------------------------------------------
     The type of witnesses, used by the definition principles.
 ---------------------------------------------------------------------------*)

  datatype witness 
       = TERM of term
       | THEOREM of thm 
end
