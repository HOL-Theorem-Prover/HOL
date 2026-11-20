(* Deliberately ill-typed clients of the two engines.  Each file is
   elaborated with PolyML.use, so this suite is Poly/ML-only; it is not
   built under Moscow ML.  Only the exact static-error exception counts as
   rejection: accepted code, missing files and other exceptions fail.
   The compiler's type-error diagnostics are normal output. *)
open HolKernel testutils
local open boolTheory pureSimps simpLib congLib Traverse TraverseExt
           simpExtLib congExtLib in end

val clients =
  ["traverse-ordinary-to-extension","traverse-extension-to-ordinary",
   "ordinary-reducer-to-extension","extension-reducer-to-ordinary",
   "ordinary-set-to-extension","extension-set-to-ordinary",
   "ordinary-fragment-to-extension","extension-fragment-to-ordinary",
   "ordinary-congset-to-extension","extension-congset-to-ordinary",
   "ordinary-source-handles","ordinary-source-inventory",
   "ordinary-bundle-preparation"]

fun rejected name =
  (PolyML.use (name ^ ".ML"); false)
  handle Fail "Static Errors" => true

val _ = List.app (fn name =>
  (tprint ("static type rejection: " ^ name);
   if rejected name then OK () else die name)) clients
