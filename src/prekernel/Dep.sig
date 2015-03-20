signature Dep =
sig

    type depid       = string * int
    datatype depchoice = DEP_LEFT | DEP_RIGHT
    type depaddress  = depchoice list
    type depconj     = depid * depaddress
    datatype deptree = DEP_NODE of deptree * deptree
                     | DEP_LEAF of depconj list
    datatype dep     = DEP_SAVED of depid * deptree * deptree
                     | DEP_UNSAVED of deptree
    type depdisk     =
      (string * int) *
      (string * (string * int list * (int * string) list) list) list

     val empty_deptree    : deptree
     val empty_dep        : dep

     (* Dependency accessors *)
     val depthy_of       : depid -> string
     val depnumber_of    : depid -> int
     val depid_of        : depconj -> depid
     val depaddress_of   : depconj -> depaddress
     val deptree_of      : dep -> deptree
     val depid_of_dep    : dep -> depid
     val saveddeptree_of : dep -> deptree

     (* Comparison functions *)
     val depchoice_compare  : (depchoice * depchoice) -> order
     val depid_compare      : (depid * depid) -> order
     val depaddress_compare : (depaddress * depaddress) -> order
     val depconj_compare    : (depconj * depconj) -> order

     (* Tree accessors and destructors *)
     val mk_deptree       : deptree * deptree -> deptree
     val dest_deptree     : deptree -> deptree * deptree
     val mk_depleaf       : depconj list -> deptree
     val dest_depleaf     : deptree -> depconj list

     (* Tracking dependencies in inference rules *)
     val collapse_deptree : deptree -> deptree
     (* When saving a theorem *)
     val starting_deptree : depid * deptree -> deptree

     (* Printing and reading *)
     val number_depaddress : depaddress -> string
     val pp_dep            : Portable.ppstream -> dep -> unit

     val read_depaddress   : string -> depaddress
     val read_dep          : depdisk -> dep

end
