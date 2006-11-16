signature Stack = sig

    type 'item stack
    val empty : unit -> 'item stack
    val isEmpty : 'item stack -> bool
    val pop : 'item stack -> 'item stack
    val push : 'item * 'item stack -> 'item stack
    val top : 'item stack -> 'item
    val stack2set : 'item stack * 'item Binaryset.set -> 'item Binaryset.set
  end
