structure combinSimps :> combinSimps =
struct

open combinTheory boolLib
val COMBIN_ss =
    simpLib.named_rewrites "COMBIN"
      [I_THM,I_o_ID,K_THM,S_THM,GSYM o_ASSOC,o_THM,W_THM,C_THM,K_o_THM]

end (* struct *)
