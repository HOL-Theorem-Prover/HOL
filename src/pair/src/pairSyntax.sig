signature pairSyntax =
sig
 include Abbrev

 val mk_prod            : hol_type * hol_type -> hol_type
 val dest_prod          : hol_type -> hol_type * hol_type
 val list_mk_prod       : hol_type list -> hol_type
 val strip_prod         : hol_type -> hol_type list
 val strip_prod_list    : hol_type list -> hol_type list -> hol_type list

 val comma              : term
 val Fst                : term
 val Snd                : term 
 val Uncurry            : term
 val Curry              : term
 val pair_fun           : term

 val mk_pair            : term * term -> term
 val dest_pair          : term -> term * term
 val list_mk_pair       : term list -> term
 val strip_pairs        : term list -> term list -> term list
 val strip_pair         : term -> term list
 val mk_fst             : term -> term
 val mk_snd             : term -> term

 val mk_abs             : term * term -> term
 val mk_forall          : term * term -> term
 val mk_exists          : term * term -> term
 val mk_exists1         : term * term -> term
 val mk_select          : term * term -> term
 val dest_abs           : term -> term * term
 val bvar               : term -> term
 val body               : term -> term
 val dest_forall        : term -> term * term
 val dest_exists        : term -> term * term
 val dest_exists1       : term -> term * term
 val dest_select        : term -> term * term
 val dest_paired_binder : term -> exn -> term -> term * term

 val strip_abs          : term -> term list * term
 val strip_forall       : term -> term list * term
 val strip_exists       : term -> term list * term
 val list_mk_abs        : term list * term -> term
 val list_mk_forall     : term list * term -> term
 val list_mk_exists     : term list * term -> term

 val is_pair            : term -> bool
 val is_abs             : term -> bool
 val is_forall          : term -> bool
 val is_exists          : term -> bool
 val is_exists1         : term -> bool
 val is_select          : term -> bool
 val is_vstruct         : term -> bool

 val genvstruct         : hol_type -> term

 val PAIRED_BETA_CONV   : conv 
 val PAIRED_ETA_CONV    : conv 
 val GEN_BETA_CONV      : conv 
 val let_CONV           : conv 
end
