type rule = {target : string, dependencies : string list,
             commands : string list list}

type doc = {rules : rule list, includes : string list,
            pre_includes : string list, options : string list}

type preliminary = {includes : string list, pre_includes : string list,
                    options : string list}

val empty_doc : doc

val merge_prelims : preliminary -> preliminary -> preliminary
