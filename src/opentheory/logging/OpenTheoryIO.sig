signature OpenTheoryIO = sig
  val thm_to_article : TextIO.outstream -> (unit -> thm) -> unit
  val term_to_article : TextIO.outstream -> term -> unit
  val article_to_thm : TextIO.instream -> thm
  val article_to_term : TextIO.instream -> term
end
