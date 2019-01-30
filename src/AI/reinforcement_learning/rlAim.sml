(* ========================================================================= *)
(* FILE          : rlAim.sml                                                 *)
(* DESCRIPTION   : Problems from the AIM conjecture                          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlAim :> rlAim =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork smlLexer

val ERR = mk_HOL_ERR "rlAim"

fun extract_top l = case l of 
    [Lterm (Lstring "TOP" :: _ :: Lstring ns :: t :: m)] => 
    (term_of_lisp t, string_to_int ns)
  | [Lterm (Lstring "INTERM" :: _ :: _ :: Lstring ns :: t :: m)] => 
    (term_of_lisp t, string_to_int ns)
  | _ => raise ERR "extract_info" ""

fun tread_example line = (extract_top o lisp_of o partial_sml_lexer) line
fun tread_file file = map tread_example (readl file)

fun replace_cvar tm =
  let 
    val dref = ref (dempty Term.compare)
    fun replace_cvar_aux tm = case dest_term tm of
      VAR(Name,Ty) => 
      if String.sub (Name,0) = #"C" then 
        if dmem tm (!dref) 
        then dfind tm (!dref)
        else let val newvar = mk_var ("C" ^ its (dlength (!dref)), Ty) in 
               dref := dadd tm newvar (!dref); newvar
             end
      else tm
    | CONST{Name,Thy,Ty} => raise ERR "replace_cvar" ""
    | COMB(Rator,Rand)   => 
      mk_comb (replace_cvar_aux Rator, replace_cvar_aux Rand)
    | LAMB(Var,Bod)      => raise ERR "replace_cvar" ""
  in
    replace_cvar_aux tm
  end

fun transform_ex (t,v) = (replace_cvar t, Real.fromInt v / 11.0);

(*
app load ["rlAim", "aiLib", "rlLib", "smlLexer", "rlTrain", "mlTreeNeuralNetwork"]; 
open rlAim aiLib rlLib smlLexer rlTrain mlTreeNeuralNetwork;

val dir = "/home/thibault/big/aimleapinfoJan292019";
val filel = 
  let fun f i = dir ^ "/trainingdatapart" ^ its i ^ ".lisp" in
    List.tabulate (10,f)
  end;

val setl0 = map tread_file filel;
val setl1 = map (map transform_ex) setl0;
val operl = 
  mk_fast_set (cpl_compare Term.compare Int.compare) 
  (List.concat (map (operl_of_term o fst) (List.concat setl1)));

val trainset = List.concat (butlast setl1);
val testset = last setl1;

val dim = 15;
val randtnn = random_treenn (dim,1) operl;

load "smlRedirect";
val tnn = train_tnn_eval dim randtnn (trainset,testset);

*)

end (* struct *)

