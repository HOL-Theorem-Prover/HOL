signature GraphExtra =
sig


type t = unit
val extra_deps : t -> Holmake_tools.dep list
val get_extra : {master_dir : Holmake_tools.hmdir.t,
                 master_cline : HM_Cline.t,
                 envlist: string -> string list} -> t
val toString : t -> string
val canIgnore : Holmake_tools.dep -> t -> bool

end
