type rule = {target : string, dependencies : string list,
             commands : string list list}

type preliminary = {includes : string list, pre_includes : string list,
                    options : string list, extra_cleans : string list}

type doc = {rules : rule list,
            preliminaries : preliminary }

fun remove x [] = []
  | remove x (h::t) = if h = x then t else h :: remove x t

fun remove_dups [] = []
  | remove_dups (h::t) = h :: remove_dups (remove h t)
(* Carefully don't sort the list to remove duplicates; for includes and
   pre_includes the order can be significant *)

fun merge_prelims
      {includes = i1, pre_includes = pi1, options = o1, extra_cleans = c1 }
      {includes = i2, pre_includes = pi2, options = o2, extra_cleans = c2 } =
  {includes = remove_dups (i1 @ i2),
   pre_includes = remove_dups (pi1 @ pi2),
   options = remove_dups (o1 @ o2),
   extra_cleans = remove_dups (c1 @ c2)}

val empty_preliminary =  {pre_includes = [], includes = [],
                          options = [], extra_cleans = []}
val empty_doc = {rules = [], preliminaries = empty_preliminary}
