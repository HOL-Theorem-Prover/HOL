structure Uref :> Uref =
struct

   datatype t = datatype ref
   val uref = ref   
   val op := = op :=;
   val ! = !;

end;
