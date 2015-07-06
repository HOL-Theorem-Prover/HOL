signature Dep =
sig

     type depid       = string * int
     datatype dep     = DEP_SAVED of depid * depid list
                      | DEP_UNSAVED of deplist
     type depdisk     = (string * int) * ((string * int list) list) 

     val empty_deptree     : deptree
     val empty_dep         : dep

     (* Dependency accessors *)
     val depthy_of         : depid -> string
     val depnumber_of      : depid -> int
     val depid_of          : dep -> depid
     val depidlist_of      : dep -> depid list
     
     (* Comparison functions *)
     val depid_compare     : (depid * depid) -> order

     (* Tracking dependencies in inference rules *)
     val merge_dep         : dep -> dep -> dep

     (* Printing and reading *)
     val pp_dep            : Portable.ppstream -> dep -> unit
     val read_dep          : depdisk -> dep

end
