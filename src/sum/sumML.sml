structure sumML :> sumML =
struct

  datatype ('a,'b)sum = INL of 'a | INR of 'b
 
 fun isl (INL _) = true | isl (INR _) = false;
 fun isr (INL _) = false | isr (INR _) = true;
 fun outl (INL x) = x
 fun outr (INR x) = x;

val _ = app ConstMapML.insert
           [(sumSyntax.inl_tm, ("sumML","INL")),
            (sumSyntax.inr_tm, ("sumML","INR")),
            (sumSyntax.isl_tm, ("sumML","isl")),
            (sumSyntax.isr_tm, ("sumML","isr")),
            (sumSyntax.outl_tm, ("sumML","outl")),
            (sumSyntax.outr_tm, ("sumML","outr"))];
end
