signature Refute_ModelFinder_Kodkod = sig
  type nut = Refute_ModelFinder_Nut.nut
  type problem_metadata =
    {free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     unsound : bool,
     unknown_value : bool,
     scope : Refute_ModelFinder_Scope.scope}
  type rich_problem = Refute_Forl.problem * problem_metadata
  type assembly_params =
    {debug : bool,
     peephole_optim : bool,
     total_consts : bool,
     datatype_sym_break : int,
     kodkod_sym_break : int,
     comment : string,
     solver : string list,
     unsound_delay : int,
     free_names : nut list,
     nonsel_names : nut list,
     nondef_us : nut list,
     def_us : nut list,
     need_us : nut list}
  val assemble_problem :
    assembly_params -> bool -> Refute_ModelFinder_Scope.scope ->
    rich_problem option
end
