type 'a foo = int
and 'b bar = 'b option
and ('c, 'd) baz = 'c * 'd -> int list


type 'a foo = unit -> int bar
and 'a bar = unit -> (string, int array) baz
and ('a, 'b) baz = unit -> int list foo
