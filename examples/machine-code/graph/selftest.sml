open HolKernel Parse boolLib bossLib;
open decompileLib testutils


local
   open Char String
   fun hash_string s =
     let
        fun hsh (i, A) s =
           hsh (i + 1, (A * 263 + ord (sub (s, i))) mod 792606555396977) s
           handle Subscript => A
     in
        hsh (0,0) s
     end
   fun s_term tm =
       if is_var tm then fst (dest_var tm)
       else if is_const tm then fst (dest_const tm)
       else if is_comb tm then
         "(" ^ s_term (rand tm) ^ " " ^ s_term (rator tm) ^ ")"
       else if is_abs tm then
         let val (v,t) = dest_abs tm in
           "[" ^ s_term v ^ " " ^ s_term t ^ "]"
         end
       else raise mk_HOL_ERR "selftest" "s_term" ""
in
fun hash_term t = hash_string (s_term t)
end


val hash_thm = hash_term o Thm.concl
val hash_dfn = hash_thm o DB.definition

val thm = decompileLib.decomp "loop/example" false ""

(*
val _ =
  if hash_thm thm = 373949126571192 andalso
     hash_dfn "main_funcs" = 729825789649344 andalso
     hash_dfn "f_funcs" = 95180147214897 andalso
     hash_dfn "g_funcs" = 774608748961224
  then
     OK()
  else
    die "Decompilation of loop/example produced unexpected result"
*)

(* Currently failing
val thm = decompileLib.decomp "loop-m0/example" false ""
*)

val _ = OS.Process.exit OS.Process.success
