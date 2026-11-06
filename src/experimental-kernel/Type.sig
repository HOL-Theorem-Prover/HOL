signature Type =
sig

  include FinalType where type hol_type = Type_dtype.hol_type
                      and type bflag = HOLFlags.bflag

end
