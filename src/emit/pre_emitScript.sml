Theory pre_emit
Ancestors
  words

Definition word_index_def:   word_index (w:'a word) n = w ' n
End
Definition w2w_itself_def:   w2w_itself (:'a) w = (w2w w): 'a word
End
Definition sw2sw_itself_def:   sw2sw_itself (:'a) w = (sw2sw w): 'a word
End
Definition word_eq_def:   word_eq (v: 'a word) w = (v = w)
End

Definition word_extract_itself_def:
  word_extract_itself (:'a) h l w = (word_extract h l w): bool ** 'a
End

Definition word_concat_itself_def:
  word_concat_itself (:'a) v w = (word_concat v w): bool ** 'a
End

Definition fromNum_def:
  fromNum (n, (:'a)) = n2w_itself (n MOD dimword (:'a),(:'a))
End
