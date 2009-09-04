signature optionLib =
sig
  (*  include optionSyntax   ... defeats dependency analyzer *)
  include Abbrev

  val mk_option        : hol_type -> hol_type
  val dest_option      : hol_type -> hol_type
  val is_option        : hol_type -> bool

  val none_tm          : term
  val some_tm          : term
  val the_tm           : term
  val option_map_tm    : term
  val option_join_tm   : term
  val is_some_tm       : term
  val is_none_tm       : term
  val option_case_tm   : term

  val mk_none          : hol_type -> term
  val mk_some          : term -> term
  val mk_the           : term -> term
  val mk_option_map    : term * term -> term
  val mk_option_join   : term -> term
  val mk_is_some       : term -> term
  val mk_is_none       : term -> term
  val mk_option_case   : term * term * term -> term

  val dest_none        : term -> hol_type
  val dest_some        : term -> term
  val dest_the         : term -> term
  val dest_option_map  : term -> term * term
  val dest_option_join : term -> term
  val dest_is_some     : term -> term
  val dest_is_none     : term -> term
  val dest_option_case : term -> term * term * term

  val is_none          : term -> bool
  val is_some          : term -> bool
  val is_the           : term -> bool
  val is_option_map    : term -> bool
  val is_option_join   : term -> bool
  val is_is_some       : term -> bool
  val is_is_none       : term -> bool
  val is_option_case   : term -> bool

   val option_rws : thm
   val OPTION_rws : computeLib.compset -> unit
end;
