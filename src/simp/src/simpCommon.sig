(* The representation-independent parts of simpLib, shared with simpExtLib.
   Functions taking a record of operations are the generic versions of the
   simpLib functions of the same name. *)
signature simpCommon =
sig
  include Abbrev
  type thname = KernelSig.kernelname
  type control = BoundedRewrites.control
  type controlled_thm = BoundedRewrites.controlled_thm

  val option_cases : ('a -> 'b) -> 'b -> 'a option -> 'b
  val oo : ('b -> 'c list) * ('a -> 'b list) -> 'a -> 'c list

  type convdata = {name  : string,
                   key   : (term list * term) option,
                   trace : int,
                   conv  : (term list -> term -> thm) -> term list -> conv}
  type stdconvdata = {name: string, pats: term list, conv: conv}
  type relsimpdata = {refl: thm, trans:thm, weakenings:thm list,
                      subsets : thm list, rewrs : thm list}
  val opttheory : string option -> string -> string

  (* Name a rewrite, compute its key and let [build] make its conversion
     data; NONE (traced) where that fails *)
  val mk_rewr_convdata :
      ({thypart : string option, name : string,
        key : (term list * term) option, nmopt : thname option, th : thm,
        tag : control} -> 'a) ->
      thname option * controlled_thm -> 'a option

  val normCong : thm -> thm

  (* Named-fragment databases *)
  val new_fragDB : string -> 'a Symtab.table Context.Data.slot
  val register_frag :
      'a Symtab.table Context.Data.slot -> ('a -> string option) -> 'a -> 'a
  val lookup_named_frag :
      'a Symtab.table Context.Data.slot -> string -> 'a option
  val all_named_frags : 'a Symtab.table Context.Data.slot -> string list

  val merge_names : string option list -> string option
  val merge_filters : ('a -> 'a list) option list -> ('a -> 'a list) option
  val merge_names_by : ('f -> string option) -> 'f list -> string option
  val merge_filters_by :
      ('f -> ('a -> 'a list) option) -> 'f list -> ('a -> 'a list) option
  val std_conv_ss :
      {conv_ss : convdata -> 'f, merge_ss : 'f list -> 'f} ->
      stdconvdata -> 'f
  val partition_ssfrags :
      ('f -> string option) -> string list -> 'f list -> 'f list * 'f list
  val same_frag : ('f -> string option) -> 'f -> 'f -> bool

  (* Fragment-name sets, where "" stands for the anonymous fragments *)
  val name_set_member : string Binaryset.set -> string option -> bool
  val names_member : string list -> string option -> bool
  (* Is a fragment of this name excluded (never when anonymous)? *)
  val is_excluded : string Binaryset.set -> string option -> bool
  (* Remove a fragment's name from an exclusion set *)
  val include_name :
      string Binaryset.set -> string option -> string Binaryset.set

  val entry_name_match :
      string option * string -> (string option * string) list -> bool
  val prepare_entry_name_match :
      (string option * string) list -> string option -> string -> bool
  val munge_simpset_name : string -> string option * string

  val user_conv_tracing :
      {name : string, trace : int} ->
      {enter : term -> unit, leave : term * thm -> thm, failed : exn -> thm}
  val any : term
  val mk_ac : thm * thm -> (thname option * controlled_thm) list ->
              (thname option * controlled_thm) list
  val ac_rewrites : (thm * thm) list -> (thname option * controlled_thm) list
  val wk_mk_travrules :
      Travrules.preorder list * thm list -> Travrules.travrules

  val equality_po : Travrules.preorder
  val rsd_travrules : relsimpdata -> Travrules.travrules
  val rsd_reducer : relsimpdata -> Traverse.reducer
  val relsimp_weakener :
      relsimpdata -> Travrules.preorder list * thm list * Traverse.reducer
  val mk_named_rewrs :
      ('a -> 'b list) -> thname option * 'a -> (thname option * 'b) list

  val frag_of : (string -> 'f option) -> string -> 'f
  val SF : {frag_name : 'f -> string option,
            lookup_named_frag : string -> 'f option,
            register_frag : 'f -> 'f} -> 'f -> thm
  val tactic_only : string -> 'a
  val SIMP_CONV : {process_tags : 's -> thm list -> 's * thm list,
                   qconv : 's -> thm list -> conv} -> 's -> thm list -> conv
  val SIMP_PROVE : {process_tags : 's -> thm list -> 's * thm list,
                    qconv : 's -> thm list -> conv} ->
                   's -> thm list -> term -> thm
  val add_rewrites : {process_tags : 's -> thm list -> 's * thm list,
                      add : 's * 'f -> 's, rewrites : thm list -> 'f} ->
                     's * thm list -> 's
  val ASM_SIMP_RULE :
      ('s -> thm list -> thm -> thm) -> 's -> thm list -> thm -> thm

  type simptac_config =
       {strip : bool, elimvars : bool, droptrues : bool, oldestfirst : bool}
  val BF_ASSUME_TAC : bool -> thm -> tactic
  val caa_tac0 : bool -> simptac_config -> thm -> tactic
  val stdcon : simptac_config -> thm -> tactic
  val full_simp_tacs :
      {simp_rule : 's -> thm list -> thm -> thm,
       asm_simp_tac : 's -> thm list -> tactic} ->
      {FULL_SIMP_TAC : 's -> thm list -> tactic,
       REV_FULL_SIMP_TAC : 's -> thm list -> tactic,
       NO_STRIP_FULL_SIMP_TAC : 's -> thm list -> tactic,
       NO_STRIP_REV_FULL_SIMP_TAC : 's -> thm list -> tactic}
  val global_simp_tac :
      {prepare : 's -> thm list -> 's,
       allasms : unit -> simptac_config -> 's -> tactic,
       asm_simp_tac : 's -> thm list -> tactic} ->
      simptac_config -> 's -> thm list -> tactic

  val tyi_frag_parts :
      TypeBasePure.tyinfo ->
      {name : string, thy : string,
       convs : convdata list, rewrs : (thname option * thm) list}

  val type_ssfrag : (TypeBasePure.tyinfo -> 'f) -> hol_type -> 'f

  val pp_ssfrag :
      {name : string option,
       convs : (string option * string * term option) list,
       dprocs : string option list,
       thm_blocks : (string * thm list) list,
       ac : (thm * thm) list,
       named_blocks : (string * (thname option * thm) list) list} ->
      HOLPP.pretty
  val pp_simpset :
      {net_names : string list, frag_names : string option list,
       extra_sections : (string * string list) list} -> HOLPP.pretty
end
