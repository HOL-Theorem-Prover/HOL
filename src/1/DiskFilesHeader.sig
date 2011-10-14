signature DiskFilesHeader =
sig

type id = {Thy:string,Name:string}

datatype prekind = pkv of string * int | pkty of int | pkarr of int * int
datatype pretype = ptv of string * int | ptc of int * int
                 | ptapp of int * int | ptabs of int * int
                 | ptuni of int * int | ptexi of int * int
datatype pre_vc = ptm_v of string * int | ptm_c of int * int
datatype preterm = app of preterm * preterm | abs of int * preterm
                 | tyapp of preterm * int | tyabs of int * preterm
                 | atom of int
type prethm = preterm list * preterm
type 'a array = (int,'a)Binarymap.dict
type parse_result =
     id array * prekind array * pretype array * pre_vc array * (string * prethm) list

val convert_prethms : parse_result -> (string * HolKernel.thm) list

end
