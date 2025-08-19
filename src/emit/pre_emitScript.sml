Theory pre_emit
Ancestors
  words

val word_index_def = Define `word_index (w:'a word) n = w ' n`;
val w2w_itself_def = Define `w2w_itself (:'a) w = (w2w w): 'a word`;
val sw2sw_itself_def = Define `sw2sw_itself (:'a) w = (sw2sw w): 'a word`;
val word_eq_def = Define `word_eq (v: 'a word) w = (v = w)`;

val word_extract_itself_def = Define`
  word_extract_itself (:'a) h l w = (word_extract h l w): bool ** 'a`;

val word_concat_itself_def = Define`
  word_concat_itself (:'a) v w = (word_concat v w): bool ** 'a`;

val fromNum_def = Define`
  fromNum (n, (:'a)) = n2w_itself (n MOD dimword (:'a),(:'a))`;
