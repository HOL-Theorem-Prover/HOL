structure Stack :> Stack = 
struct
   
   exception EmptyStack

   datatype 'item stack =
       Empty |
       Node of 'item * 'item stack

   fun isEmpty( Node( _ , S)) = false
    |  isEmpty _          = true

   fun empty() = Empty

   fun push( x, S ) = Node( x, S )

   fun pop( Empty ) = raise EmptyStack
   |   pop( Node( x, S) ) = S

   fun top( Empty ) = raise EmptyStack
   |   top( Node( x, S ) ) = x

   fun stack2set (Empty, st) = st
   |   stack2set (Node(x,S),st) = stack2set(S, Binaryset.add(st,x))

end
