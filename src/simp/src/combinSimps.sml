structure combinSimps :> combinSimps =
struct

local open combinTheory
in
  val COMBIN_ss = simpLib.rewrites [I_THM,I_o_ID,K_THM,S_THM,o_ASSOC,o_THM]
end

end (* struct *)
