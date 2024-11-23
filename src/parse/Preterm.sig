signature Preterm =
sig
  type pretype = Pretype.pretype
  type hol_type = Type.hol_type
  type term = Term.term

  datatype tcheck_error = datatype typecheck_error.tcheck_error
  type error = typecheck_error.error
  val mkExn : error -> exn

  datatype preterm = datatype Preterm_dtype.preterm

  type 'a in_env = 'a Pretype.in_env
  type 'a errM = (Pretype.Env.t,'a,error) errormonad.t
  type 'a seqM = (Pretype.Env.t,'a) seqmonad.seqmonad
  val smash : ('s,'a,error) errormonad.t -> 's -> 'a

  val locn : preterm -> locn.locn
  val term_to_preterm : string list -> term -> preterm in_env

  val eq : preterm -> preterm -> bool
  val pdest_eq : preterm -> preterm * preterm
  val lhs : preterm -> preterm
  val head_var : preterm -> preterm
  val ptype_of : preterm -> pretype in_env
  val dest_ptvar : preterm -> (string * pretype * locn.locn)
  val plist_mk_rbinop : preterm -> preterm list -> preterm
  val strip_pcomb : preterm -> preterm * preterm list
  val strip_pforall : preterm -> preterm list * preterm
  val ptfvs : preterm -> preterm list
   (* ptfvs ignores free variables that might be hiding in Pattern, Overload
      or Antiq constructors because these are all of fixed type that can't
      vary; ptfvs is designed to find free variables that might have
      unifiable type variables in their types *)


  (* Performs the first phase of type-checking, altering the types
     attached to the various components of the preterm, but without
     resolving overloading.  The two printing functions are used to
     report errors. *)

  val typecheck_phase1 :
    ((term -> string) * (hol_type -> string)) option -> preterm -> unit errM

  (* performs overloading resolution, possibly guessing overloads if
     this is both allowed by Globals.guessing_overloads and required by
     ambiguity in the term *)

  val overloading_resolution : preterm -> (preterm * bool) errM
  val overloading_resolutionS : preterm -> preterm seqM
  val report_ovl_ambiguity : bool -> unit errM


  (* converts a preterm into a term.  Will guess type variables for
     unassigned pretypes if Globals.guessing_tyvars is true.
     Will fail if the preterm contains any Overloaded constructors, or
     if the types attached to the leaves aren't valid for the kernel.  *)
  val to_term : preterm -> term in_env


  (* deals with case expressions, which need to be properly typed and
     analysed before they can be converted into type-specific case-
     constants *)
  val remove_case_magic : term -> term

  val post_process_term : (term -> term) ref

  (* essentially the composition of all four of the above *)
  val typecheck:
    ((term -> string) * (hol_type -> string)) option -> preterm -> term errM
  val typecheckS : preterm -> term seqM

  val typecheck_listener : (preterm -> Pretype.Env.t -> unit) ref
  val last_tcerror : (tcheck_error * locn.locn) option ref

end
