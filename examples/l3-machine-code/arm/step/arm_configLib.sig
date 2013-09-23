signature arm_configLib =
sig
   include Abbrev
   val mk_arm_const: string -> term
   val mk_arm_type: string -> hol_type
   val mk_config_terms: string -> term list
   val st: term
end
