structure ConstMapML :> ConstMapML = 
struct 

open HolKernel ;

val ERR = mk_HOL_ERR "ConstMapML";

fun LEX c1 c2 ((x1,x2),(y1,y2)) =
  case c1 (x1,y1)
   of EQUAL => c2 (x2,y2)
    | other => other;

local open Redblackmap 
in
type constmap = (string*string, string*string)dict
val initConstMap : constmap = mkDict (LEX String.compare String.compare)
end;

(*---------------------------------------------------------------------------*)
(* The initial constant map has only equality in it                          *)
(*---------------------------------------------------------------------------*)

val ConstMapRef = ref(Redblackmap.insert(initConstMap,("min","="),("","=")));
fun theConstMap () = !ConstMapRef;

fun insert (c,p) = 
 let val {Name,Thy,...} = dest_thy_const c
 in ConstMapRef := Redblackmap.insert(theConstMap(),(Thy,Name),p)
 end;

fun apply c =
 let val {Name,Thy,...} = dest_thy_const c
 in case Redblackmap.peek(theConstMap(),(Thy,Name))
   of SOME (str,name) => (str,name)
    | NONE => if Thy=current_theory() then ("",Name) 
                 else raise ERR "apply" 
                       ("no binding found for "^Lib.quote(Thy^"$"^Name))
 end

end
