signature DefnBaseCore =
sig
  type term = Term.term
  type thm  = Thm.thm
  type kname = KernelSig.kernelname

  (* record various flavours of definition, keyed by constant and a
     "tag", which is a user-choosable string. Assume that "user" and
     "compute" exist for example.

     Another might be "PMATCH", which would be the definition with
     case constants translated into PMATCH versions.

     For the moment, as per all the names that talk of "userdefs", the
     only useful tag is "user".
  *)
  datatype defn_thm = STDEQNS of thm | OTHER of thm
  type defn_presentation = {const: term, thmname: kname, thm : defn_thm}
  exception nonstdform
  val constants_of_defn : thm -> kname list                (* EXN: nonstdform *)
  val defn_eqns : thm -> (kname * thm) list                (* EXN: nonstdform *)
  val register_defn : {tag: string, thmname:string} -> unit
  val lookup_userdef : term -> defn_presentation option
  val current_userdefs : unit -> defn_presentation list
  val thy_userdefs : {thyname:string} -> defn_presentation list

  val register_indn : thm * kname list -> unit
  val lookup_indn : term -> (thm * kname list) option

  (* register_defn is given a tag and a theorem which is a conjunction of
     possibly universally quantified equations.  The machinery here
     will create a sub-conjunction of the clauses per constant (and this is
     what is returned by lookup_defn).

     Induction theorems have some number of induction variables (P1,
     P2, ..) where each corresponds to a defined constant. This list
     of constants is what is passed into register_indn alongside the
     induction theorem. When a term is looked up, if lookup_indn t
     returns SOME (th, ts), then t will be among the ts.
   *)

end
