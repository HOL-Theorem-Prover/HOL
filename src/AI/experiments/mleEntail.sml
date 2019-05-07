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
   Testing satisfiability by brute force
   ------------------------------------------------------------------------- *)

fun eval_tm tm l = 
  let val (oper,argl) = strip_comb tm in
    if is_var oper then 
      let val is = (implode o tl o explode o fst o dest_var) oper in
        List.nth (l, string_to_int is)
      end
    else if term_eq oper ``$~`` then not (eval_tm (hd argl) l)
    else if term_eq oper ``$/\`` 
      then eval_tm (List.nth (argl,0)) l andalso
          eval_tm (List.nth (argl,1)) l
    else if term_eq oper ``$\/``
      then eval_tm (List.nth (argl,0)) l orelse
          eval_tm (List.nth (argl,1)) l
    else if term_eq oper ``$==>``
      then not (eval_tm (List.nth (argl,0)) l) orelse
          eval_tm (List.nth (argl,1)) l
    else raise ERR "eval_tm" ""
  end

fun is_tautology tm = 
  let 
    val n = length (free_vars_lr tm)
    val l = cartesian_productl (List.tabulate (n,fn _ => [true,false]));
  in
    all (eval_tm tm) l 
  end

(* -------------------------------------------------------------------------
   Term generation (to be moved to Term gen and make it more generic)
   ------------------------------------------------------------------------- *)

fun gen_tml operl level ntarget = 
  let 
    val range = List.tabulate (level, fn x => x + 1)
    fun gen () = random_term_uni operl (range,bool)
    val d = ref (dempty Term.compare)
    fun loop n = 
      if n > 10 * ntarget then raise ERR "not enough different terms" "" else
      if dlength (!d) >= ntarget then () else
      let val tm = gen () in
        if dmem tm (!d) then () else d := dadd tm () (!d);
        loop (n + 1)
      end
  in
    loop 0; dkeys (!d)
  end

(* -------------------------------------------------------------------------
   Example generation (make it faster and fairer)
   ------------------------------------------------------------------------- *)

fun gen_ex tml ntarget =
  let
    val dpos = ref (dempty Term.compare)
    val dneg = ref (dempty Term.compare)
    fun loop () =
      if dlength (!dpos) > ntarget andalso dlength (!dneg) > ntarget 
      then ()
      else let 
        val tm = rename_allvar (mk_imp (random_elem tml, random_elem tml))
        val b = is_tautology tm
      in
        if b 
        then 
           (
           if (dlength (!dpos) mod 100) = 0 
           then print_endline (its (dlength (!dpos))) 
           else ();
           dpos := dadd tm (if b then [1.0] else [0.0]) (!dpos)
           )
        else 
           dneg := dadd tm (if b then [1.0] else [0.0]) (!dneg)
        ;
        loop ()
      end
  in   
    loop ();
    (first_n ntarget (dlist (!dpos)) @ first_n ntarget (dlist (!dneg)))
  end
 

(*
load "mleEntail"; load "smlParallel";
open aiLib smlParallel mlTreeNeuralNetwork mleEntail;

val level = 10;
val tml = gen_tml (operl_gen 5) level 4000;

val testex = List.concat (parmap_queue 4 (gen_ex tml) [200,200,200,200]);
val trainex = List.concat (parmap_queue 4 (gen_ex tml) [2000,2000,2000,2000]);

val randtnn = random_tnn (12,1) (operl_nn 5);
val bsize = 128;
fun f x = (100, x / (Real.fromInt bsize));
val schedule = map f [0.1];
val ncore = 4;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex,testex) schedule;

val r1 = accuracy_set tnn trainex;
*)

end (* struct *)
