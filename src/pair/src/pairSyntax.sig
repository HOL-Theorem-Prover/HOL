signature pairSyntax =
sig
 include Abbrev

 val mk_prod         : hol_type * hol_type -> hol_type
 val dest_prod       : hol_type -> hol_type * hol_type
 val list_mk_prod    : hol_type list -> hol_type
 val strip_prod      : hol_type -> hol_type list
 val spine_prod      : hol_type -> hol_type list

 val comma_tm        : term
 val fst_tm          : term
 val snd_tm          : term 
 val uncurry_tm      : term
 val curry_tm        : term
 val pair_map_tm     : term
 val lex_tm          : term

 val mk_pair         : term * term -> term
 val mk_fst          : term -> term
 val mk_snd          : term -> term
 val mk_curry        : term * term * term -> term
 val mk_uncurry      : term * term -> term
 val mk_pair_map     : term * term -> term
 val mk_lex          : term * term -> term
 val mk_pabs         : term * term -> term
 val mk_pforall      : term * term -> term
 val mk_pexists      : term * term -> term
 val mk_pexists1     : term * term -> term
 val mk_pselect      : term * term -> term
 val mk_plet         : term * term * term -> term
 val mk_anylet       : (term * term) list * term -> term

 val dest_pair       : term -> term * term
 val dest_fst        : term -> term
 val dest_snd        : term -> term
 val dest_curry      : term -> term * term * term
 val dest_uncurry    : term -> term * term
 val dest_pair_map   : term -> term * term
 val dest_lex        : term -> term * term
 val dest_pabs       : term -> term * term
 val pbvar           : term -> term
 val pbody           : term -> term
 val dest_plet       : term -> term * term * term
 val dest_anylet     : term -> (term * term) list * term 
 val dest_pforall    : term -> term * term
 val dest_pexists    : term -> term * term
 val dest_pexists1   : term -> term * term
 val dest_pselect    : term -> term * term
 val dest_pbinder    : term -> exn -> term -> term * term

 val list_mk_pair    : term list -> term
 val list_mk_pabs    : term list * term -> term
 val list_mk_anylet  : (term * term) list list * term -> term
 val list_mk_pforall : term list * term -> term
 val list_mk_pexists : term list * term -> term
 val strip_pair      : term -> term list
 val spine_pair      : term -> term list
 val unstrip_pair    : hol_type -> term list -> term * term list
 val strip_pabs      : term -> term list * term
 val strip_anylet    : term -> (term * term) list list * term 
 val strip_pforall   : term -> term list * term
 val strip_pexists   : term -> term list * term


 val is_pair         : term -> bool
 val is_fst          : term -> bool
 val is_snd          : term -> bool
 val is_curry        : term -> bool
 val is_uncurry      : term -> bool
 val is_pair_map     : term -> bool
 val is_lex          : term -> bool
 val is_pabs         : term -> bool
 val is_plet         : term -> bool
 val is_pforall      : term -> bool
 val is_pexists      : term -> bool
 val is_pexists1     : term -> bool
 val is_pselect      : term -> bool
 val is_vstruct      : term -> bool

 val genvarstruct    : hol_type -> term

 val  lift_prod      : hol_type -> ('a -> term ) -> ('b -> term) 
                                -> 'a * 'b -> term
end
