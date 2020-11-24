(* ========================================================================= *)
(* FILE          : mlPytorchTNN.sml                                             *)
(* DESCRIPTION   : Interface to the Pytorch implementation of tree neural    *)
(* networks                                                                  *)
(* AUTHOR        : Thibault Gauthier, Czech Technical University             *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structure mlPytorchTNN :> mlPytorchTNN =
struct

open HolKernel boolLib Abbrev aiLib mlMatrix mlNeuralNetwork mlTreeNeuralNetwork 
smlParallel smlParser mlTacticData 

val ERR = mk_HOL_ERR "mlPytorchTNN"

(* -------------------------------------------------------------------------
   Examples I/O
   ------------------------------------------------------------------------- *)

fun sexp_term t = 
  if is_comb t then 
    let val (oper,argl) = strip_comb t in 
      "(" ^ String.concatWith " " (map sexp_term (oper :: argl)) ^ ")"
    end
  else if is_var t then escape (snd (dest_var t))
  else if is_const t then 
    let val {Thy,Name,Ty} = dest_thy_const t in
      escape (Thy ^ "." ^ Name)
    end
  else raise ERR "sexp_term" "abstraction"

fun sexp_exl file exl =
  let fun f (t,rl) = sexp_term t ^ "\n" ^ (String.concatWith " " (map rts rl)) in
    writel file (map f exl)
  end

fun train_model

fun infer_model

end (* struct *)
