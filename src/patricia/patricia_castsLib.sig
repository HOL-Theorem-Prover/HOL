signature patricia_castsLib =
sig

  include Abbrev

  type term_ptree = patriciaLib.term_ptree
  type num = Arbnum.num

  val dest_word_ptree : term -> num * term_ptree
  val mk_word_ptree   : num * term_ptree -> term

  val add_cast_ptree_compset : computeLib.compset -> unit
  val cast_ptree_compset     : unit -> computeLib.compset
  val CAST_PTREE_CONV        : conv

  val Define_word_ptree     : string * string -> term -> thm * thm
  val Define_mk_word_ptree  : string * string -> num -> term_ptree -> thm * thm
  val iDefine_mk_word_ptree : string * string -> int -> term_ptree -> thm * thm

  val Define_string_ptree   : string -> term -> thm

end
