signature DiskFilesHeader =
sig

type id = {Thy:string,Name:string}

datatype pretype = ptv of string | ptop of int * int list
datatype pre_vc = ptm_v of string * int | ptm_c of int * int
datatype preterm = app of preterm * preterm | abs of int * preterm
                 | atom of int
type prethm = preterm list * preterm
type parse_result =
     string vector * id vector * pretype vector * pre_vc vector *
     (string * prethm) list

val convert_prethms : parse_result -> (string * HolKernel.thm) list

end
