type rule = {target : string, dependencies : string list,
             commands : string list list}

type preliminary = {includes : string list, pre_includes : string list,
                    options : string list, extra_cleans : string list}

type doc = {rules : rule list,
            preliminaries : preliminary }

val empty_doc : doc
val empty_preliminary : preliminary

val merge_prelims : preliminary -> preliminary -> preliminary
