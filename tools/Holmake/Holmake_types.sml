type rule = {target : string, dependencies : string list,
             commands : string list list}

type doc = {rules : rule list, includes : string list,
            pre_includes : string list, options : string list}

type preliminary = {includes : string list, pre_includes : string list,
                    options : string list}

fun remove_sorted_dups [] = []
  | remove_sorted_dups [x] = [x]
  | remove_sorted_dups (x::y::xs) = if x = y then x :: remove_sorted_dups xs
                                    else x :: remove_sorted_dups (y :: xs)

fun remove_dups list =
  remove_sorted_dups (Listsort.sort String.compare list)

fun merge_prelims {includes = i1, pre_includes = pi1, options = o1 }
                  {includes = i2, pre_includes = pi2, options = o2 } =
  {includes = remove_dups (i1 @ i2),
   pre_includes = remove_dups (pi1 @ pi2),
   options = remove_dups (o1 @ o2)}

val empty_doc = {rules = [], pre_includes = [], includes = [], options = []}