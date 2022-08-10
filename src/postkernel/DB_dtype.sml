structure DB_dtype =
struct

 datatype class = Thm | Axm | Def
 datatype theory =
          THEORY of string *
                {types       : (string * int) list,
                 consts      : (string * Type.hol_type) list,
                 parents     : string list,
                 axioms      : (string * Thm.thm) list,
                 definitions : (string * Thm.thm) list,
                 theorems    : (string * Thm.thm) list}

 datatype selector = SelTM of Term.term | SelNM of string | SelTHY of string

 type data_value = (Thm.thm * class * {private:bool})
 type public_data_value = Thm.thm * class
 fun dvdrop_private ((th,c,_) : data_value) : public_data_value = (th,c)
 type 'a named = (string * string) * 'a
 type data = data_value named
 type public_data = public_data_value named
 fun drop_private (nms, dv) = (nms, dvdrop_private dv)



 datatype location = Local of string | Stored of KernelSig.kernelname


end
