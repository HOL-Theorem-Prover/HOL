type id = (string -> string) -> string
type rule = {target : id, dependencies : id list,
             commands : id list list}

type preliminary = {includes : id list, pre_includes : id list,
                    options : id list, extra_cleans : id list}

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
  {includes = i1 @ i2,
   pre_includes = pi1 @ pi2,
   options = o1 @ o2,
   extra_cleans = c1 @ c2}

val empty_preliminary =  {pre_includes = [], includes = [],
                          options = [], extra_cleans = []}
val empty_doc = {rules = [], preliminaries = empty_preliminary}
