type id = (string -> string) -> string

type rule = {target : id, dependencies : id list,
             commands : id list list}

type preliminary = {includes : id list, pre_includes : id list,
                    options : id list, extra_cleans : id list}

type doc = {rules : rule list,
            preliminaries : preliminary }


val empty_doc : doc
val empty_preliminary : preliminary

val merge_prelims : preliminary -> preliminary -> preliminary
