structure hol90Lib =
struct
  local open Define_type HOLTheory basicHol90Lib
             Let_conv ConstrProofs Num_conv Num_induct
             goalstackLib
  in 
    val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;
  end;

end;
