signature LazyThm =
sig
   datatype proof_mode = Lazy | Eager | Draft;
   val set_proof_mode : proof_mode -> proof_mode
   val get_proof_mode : unit -> proof_mode

   type 'a lazy_thm

   type term = Term.term
   type thm = Thm.thm

   val mk_lazy_thm : 'a * (unit -> thm) -> 'a lazy_thm
   val mk_proved_lazy_thm : 'a * thm -> 'a lazy_thm
   val dest_lazy_thm : 'a lazy_thm -> 'a
   val prove_lazy_thm : (term list * term -> ''a) -> ''a lazy_thm -> thm
   val restructure_lazy_thm : ('a -> 'b) -> 'a lazy_thm -> 'b lazy_thm
   val apply_rule1 : ('a -> 'b) * (thm -> thm) -> 'a lazy_thm -> 'b lazy_thm
   val apply_rule2 : ('a -> 'b -> 'c) * (thm -> thm -> thm) ->
                     'a lazy_thm -> 'b lazy_thm -> 'c lazy_thm
   val apply_rule3 : ('a -> 'b -> 'c -> 'd) * (thm -> thm -> thm -> thm) ->
                     'a lazy_thm -> 'b lazy_thm -> 'c lazy_thm -> 'd lazy_thm
   val apply_rulen : ('a list -> 'b) * (thm list -> thm) ->
                     'a lazy_thm list -> 'b lazy_thm
   val apply_rule1_multi_result : ('a -> 'b list) * (thm -> thm list) ->
                                  'a lazy_thm -> 'b lazy_thm list

   type pre_thm = (term list * term) lazy_thm;
   val mk_pre_thm : (term list * term) * (unit -> thm) -> pre_thm
   val mk_proved_pre_thm : thm -> pre_thm
   val dest_pre_thm : pre_thm -> term list * term
   val prove_pre_thm : pre_thm -> thm
   val hyp : pre_thm -> term list
   val concl : pre_thm -> term
   val apply_to_concl : (term -> term) -> term list * term -> term list * term
end;
