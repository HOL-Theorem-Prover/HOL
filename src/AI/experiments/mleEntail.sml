(* ========================================================================= *)
(* FILE          : mleEntail.sml                                             *)
(* DESCRIPTION   : Experiments on satisfiability of boolean formulas         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mleEntail :> mleEntail =
struct

open HolKernel Abbrev boolLib aiLib psTermGen mlTreeNeuralNetwork

val ERR = mk_HOL_ERR "mleEntail"

(* -------------------------------------------------------------------------
   Building blocks for term generation and term evaluation
   ------------------------------------------------------------------------- *)

fun mk_boolvar i = (mk_var ("V" ^ its i,bool), 0);

fun operl_gen nvar = map fst 
  ([(``$/\``,2),(``$\/``,2),(``$~``,1)] @ 
  map mk_boolvar (List.tabulate (nvar, I)))

fun operl_nn nvar = [(``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2)] @ 
   map mk_boolvar (List.tabulate (nvar, I));

(* -------------------------------------------------------------------------
   Read examples from file
   ------------------------------------------------------------------------- *)

fun read_ex s =
  let 
    fun is_comma c = c = #","
    val (s1,s2,s3) = triple_of_list (first_n 3 (String.tokens is_comma s))
    fun translate_token c = case c of
        #">" => " ==> " 
      | #"|" => " \\/ "
      | #"&" => " /\\ "
      | #"~" => "~ "
      | #"(" => "("
      | #")" => ")"
      | _ => if Char.isLower c then "V" ^ Char.toString c else raise ERR "translate_token" ""
    fun dm_to_hol s = 
       let val s' = String.translate translate_token s in
         (Term [QUOTE s'] handle HOL_ERR _ => raise ERR "read_ex" s')
       end
  in
    (mk_eq (dm_to_hol s1, dm_to_hol s2), [Real.fromInt (string_to_int s3)]) 
  end;

val prime_tag = mk_var ("prime_tag", ``:bool -> bool``);
fun prime_term n tm = if n <= 0 then tm else mk_comb (prime_tag, prime_term (n - 1) tm);

fun mk_boolvar i = mk_var ("V" ^ its i,bool)

fun prime_boolvar_sub m = 
  List.tabulate 
    (m, fn n => {redex = mk_boolvar n, residue = prime_term n ``x:bool``})

(*
load "mlTreeNeuralNetwork"; open mlTreeNeuralNetwork;
load "mleEntail"; open mleEntail;
open aiLib;

val file = HOLDIR ^ "/src/AI/experiments/entail_train";
fun read_exl file = map read_ex (readl file);
val exl = read_exl file;
val trainex = map_fst rename_allvar exl;
val trainex_primed = 
  let val sub = prime_boolvar_sub 10 in 
    map_fst (subst sub) trainex 
  end;

val vl = mk_term_set (List.concat (map (free_vars_lr o fst) trainex_primed));

val operl =
  [(``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2),
   (``$= :bool -> bool -> bool``,2)] @ 
  [(``x:bool``,0),(prime_tag,1)];

val entail_dir = HOLDIR ^ "/src/AI/experiments/entail_results";
mkDir_err entail_dir;

val randtnn = random_tnn (12,1) operl;
val bsize = 16;
val schedule = [(100, 0.02 / (Real.fromInt bsize))];
val ncore = 4;
val _ = nlayers_glob := 2;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex_primed,first_n 100 trainex_primed) schedule;

write_tnn tnn "tnn_run2_sure";
val r1 = accuracy_set tnn trainex_primed;
*)

end (* struct *)
