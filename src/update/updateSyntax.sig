signature updateSyntax =
sig

   include Abbrev

   val find_tm: term
   val list_update_tm: term
   val override_tm: term

   val dest_find: term -> term * term
   val dest_list_update: term -> term
   val dest_override: term -> term

   val is_find: term -> bool
   val is_list_update: term -> bool
   val is_override: term -> bool

   val mk_find: term * term -> term
   val mk_list_update: term -> term
   val mk_override: term -> term

   val strip_list_update: term -> (term * term) list
end
