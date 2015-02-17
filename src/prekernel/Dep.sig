signature Dep =
sig
     
     (* Tracking dependencies *)
     type depid       = string * int
     datatype depchoice = DEP_LEFT | DEP_RIGHT
     type depaddress  = depchoice list
     datatype depsort = DEP_NAMED of depid
                      | DEP_CONJ of depid * depaddress
                      | DEP_INTER
     datatype deptree = DEP_NODE of deptree * deptree 
                      | DEP_LEAF of depsort list
     type dep         = depsort * deptree
     type depdisk     =  
       (string * int) * 
       (string * (string * int list * (int * string) list) list) list
     val empty_deptree    : deptree
     val empty_dep        : dep

     val depthy_of        : depid -> string
     val depnumber_of     : depid -> int
     val depid_of         : depsort -> depid     
     val address_of       : depsort -> depaddress
     val deptree_of       : dep -> deptree
     val depsort_of       : dep -> depsort

     val depchoice_compare  : (depchoice * depchoice) -> order
     val depid_compare      : (depid * depid) -> order
     val depaddress_compare : (depaddress * depaddress) -> order
     val depsort_compare    : (depsort * depsort) -> order
 
     val mk_deptree       : deptree * deptree -> deptree
     val dest_deptree     : deptree -> deptree * deptree
     val mk_depleaf       : depsort list -> deptree
     val dest_depleaf     : deptree -> depsort list     

     val merge_deptree    : deptree -> deptree
     val passed_deptree   : dep -> deptree
     val self_dep         : depsort -> dep

     val number_address   : depaddress -> string
     val pp_dep           : Portable.ppstream -> dep -> unit
     
     val read_address     : string -> depaddress
     val read_dep         : depdisk -> dep

end
