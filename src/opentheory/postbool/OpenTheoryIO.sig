signature OpenTheoryIO = sig
  val thm_to_article : TextIO.outstream -> (unit -> Thm.thm) -> unit
  val term_to_article : TextIO.outstream -> Term.term -> unit
  val article_to_thm : TextIO.instream -> Thm.thm
  val article_to_term : TextIO.instream -> Term.term
  val url_conv : string -> Conv.conv
end
