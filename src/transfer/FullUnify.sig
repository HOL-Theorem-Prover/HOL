signature FullUnify =
sig


  include Abbrev
  structure Env : sig
     type t
     type 'a EM = (t,'a) optmonad.optmonad
     val empty : t
     val add_tybind : string * hol_type -> unit EM
     val add_tmbind : term * term -> unit EM
     val lookup_ty : t -> hol_type -> hol_type
     val lookup_tm : t -> term -> term
     val instE : t -> term -> term
     val triTM : t -> (term,term)Binarymap.dict
     val triTY : t -> (string,hol_type)Binarymap.dict
  end

  val unify_types : hol_type list -> hol_type * hol_type -> unit Env.EM
  val unify : hol_type list -> term list -> term * term -> unit Env.EM

end
