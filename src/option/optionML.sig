signature optionML =
sig

  val the         : 'a option -> 'a
  val option_map  : ('a -> 'b) -> 'a option -> 'b option
  val is_none     : 'a option -> bool
  val is_some     : 'a option -> bool
  val option_join : 'a option option -> 'a option

end
