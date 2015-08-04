signature Dep =
sig

     type depid       = string * int
     datatype dep     = DEP_SAVED of depid * (string * int list) list
                      | DEP_UNSAVED of (string * int list) list
     type depdisk     = (string * int) * ((string * int list) list)

     val empty_dep         : dep

     (* Dependency accessors *)
     val depthy_of         : depid -> string
     val depnumber_of      : depid -> int
     val depid_of          : dep -> depid
     val depidl_of         : dep -> depid list
     val thydepl_of        : dep -> (string * int list) list

     (* Comparison functions *)
     val depid_compare     : (depid * depid) -> order

     (* Tracking dependencies in inference rules *)
     val transfer_thydepl  : dep -> (string * int list) list
     val merge_dep         : dep -> dep -> dep

     (* I/O *)
     val pp_dep            : Portable.ppstream -> dep -> unit
     val read_dep          : depdisk -> dep

end
