signature OpenTheoryIO = sig
  val term_to_article : TextIO.outstream -> term -> unit
  val article_to_thm : TextIO.instream -> thm
end
