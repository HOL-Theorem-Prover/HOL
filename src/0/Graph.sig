signature Graph =
sig
 type 'a graph
                   (* node equality*)
   val empty     : ('a -> 'a -> bool) -> 'a graph
   val map       : ('a -> 'a) -> 'a graph -> 'a graph
   val add       : 'a * 'a list -> 'a graph -> 'a graph
   val del       : 'a -> 'a graph -> 'a graph
   val first     : ('a -> bool) -> 'a graph -> 'a * 'a list 
   val assoc     : 'a -> 'a graph -> 'a * 'a list 
   val isin      : 'a -> 'a graph -> bool
   val add_parent: 'a * 'a -> 'a graph -> 'a graph
   val ancestryl : 'a graph -> 'a list -> 'a list
   val fringe    : 'a graph -> 'a list
end;
