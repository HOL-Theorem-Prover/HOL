signature Subst =
sig
  eqtype 'a subs;

  val id      : 'a subs;
  val cons    : 'a subs * 'a -> 'a subs;
  val shift   : int * 'a subs -> 'a subs;
  val lift    : int * 'a subs -> 'a subs;
  val is_id   : 'a subs -> bool;
  val exp_rel : 'a subs * int -> int * 'a option;
  val comp    : ('a subs * 'a -> 'a) -> 'a subs * 'a subs -> 'a subs;

end;



