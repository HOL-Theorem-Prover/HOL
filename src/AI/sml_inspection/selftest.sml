local open smlExecute smlInfix smlLexer smlOpen smlParser smlPrettify
  smlRedirect smlTimeout smlParallel in end

open smlParallel;
val l1 = List.tabulate (100,I);
val _ = parmap_queue_extern 2 idspec () l1;
