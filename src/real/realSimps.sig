signature realSimps =
sig

  (* Useful rewrites for basic real arithmetic *)
  val real_SS : simpLib.ssdata
    
  (* Incorporates simpsets for bool, pair, and arithmetic *)
  val real_ss : simpLib.simpset
    
  (* AC rewrites for + and *: occasionally useful *)
  val real_ac_SS : simpLib.ssdata
    
  (* Incorporates the real simpset *)
  val real_ac_ss : simpLib.simpset

end
