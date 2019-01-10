structure Uref :> Uref =
struct

   datatype t = datatype ref
   val new = ref   
   val op := = op :=;
   val ! = !;

end;
