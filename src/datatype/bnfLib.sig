signature bnfLib =
sig

include Abbrev
type info = thm bnfBase_dtype.info

val specToFunctor : bnfBase.bnftor -> hol_type

(* the composite functor's map and set terms, along with the BNFs that
   the composite is built from.  The map term has a free variable f of
   type α → β in it. *)
val functorToMapAndSet : bnfBase.t -> hol_type -> term * term * info HOLset.set

(* Everything that makes a type expression built over already-registered
   BNFs a BNF in its own right.  The type's α argument is taken to be the
   functor's argument; all other type variables are constants. *)
type derived_bnf = {
  bnd : term,        (* infinite set bounding the composite's set fn *)
  bndINFINITE : thm, (* |- INFINITE bnd *)
  bndthm : thm,      (* |- !x. set x <<= bnd *)
  components : info HOLset.set,  (* the BNFs the composite is built from *)
  mapCONG : thm,     (* |- (!a. a IN set x ==> f a = g a) ==>
                            map f x = map g x *)
  mapID : thm,       (* |- map I = I *)
  mapIMAGE : thm,    (* |- set o map f = IMAGE f o set *)
  mapO : thm,        (* |- map f o map g = map (f o g) *)
  mkmap : term -> term, (* mkmap f is the composite's map at f : α → β *)
  nontrivial : (term * thm) option, (* (t, |- set t <> {}), if the
                                       composite isn't constant *)
  set : term,
  wit : (term * thm) option (* (w, |- set w = {}), if an element can be
                               built without an α *)
}

(* The same, for a functor with several arguments: one map taking a
   function per argument, and a set function, naturality theorem and
   bound per argument.  The laws relating *different* arguments — that
   setᵢ ignores mapⱼ, and that mapᵢ and mapⱼ commute — are instances of
   these rather than extra obligations: put I in the other positions of
   mapIMAGE and of mapO. *)
type derived_bnfn = {
  bnd : term,
  bndINFINITE : thm,
  bndthms : thm list,       (* |- !x. setᵢ x <<= bnd, one per argument *)
  components : info HOLset.set,
  inhabits : (term * thm) option list,
                            (* (inhᵢ, |- !v. v IN setᵢ (inhᵢ v)), NONE if
                               argument i doesn't occur *)
  lives : hol_type list,    (* the arguments, in the order map takes them *)
  mapCONG : thm,            (* hypotheses conjoined, one per argument *)
  mapID : thm,              (* |- map I .. I = I *)
  mapIMAGE : thm list,      (* |- setᵢ o map f₁..fₙ = IMAGE fᵢ o setᵢ *)
  mapO : thm,
  mkmap : term list -> term,
  sets : term list,
  wits : (term * thm) list  (* (w, |- !a⃗. set₁ (w a⃗) SUBSET W₁ /\ ...),
                               each Wᵢ either {aᵢ} or {}: the witnesses,
                               in the form the database stores them, and
                               pruned to those whose demands are
                               subset-minimal *)
}

(* |- P ((\xs. t) xs), from |- P t and the position cnv aims at.  A
   witness is stored as a function of its arguments, so its theorem has to
   be about the application rather than about the body. *)
val unbeta_at : (conv -> conv) -> term list -> term -> thm -> thm

val deriveBNFn : bnfBase.t -> hol_type list -> hol_type -> derived_bnfn

val deriveBNF : bnfBase.t -> hol_type -> derived_bnf

(* ground elements, as the fixed-point construction wants them: an
   element whose i-th set is empty — which is what makes a datatype
   specification legal, since it is its base case — and one whose i-th
   set is not.  Both come from the witnesses above by supplying ARB. *)
val groundEmpty : derived_bnfn -> int -> (term * thm) option
val groundNonempty : derived_bnfn -> int -> (term * thm) option

end
