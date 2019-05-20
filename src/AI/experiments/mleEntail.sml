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
 
(* -------------------------------------------------------------------------
   Read examples from file
   ------------------------------------------------------------------------- *)

(*  *)

load "aiLib"; open aiLib;

val ERR = mk_HOL_ERR "test";
val entail_var = mk_var ("entail_var", ``:bool -> bool -> bool``);

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

val file = HOLDIR ^ "/src/AI/experiments/entail_train";
fun read_exl file = map read_ex (first_n 10000 (readl file));
val exl = read_exl file;
val trainex = map_fst rename_allvar exl;
val testex = first_n 1000 trainex;

val prime_tag = mk_var ("prime_tag", ``:bool -> bool``);
fun prime_term n tm = if n <= 0 then tm else mk_comb (prime_tag, prime_term (n - 1) tm);


fun mk_substn m = 
  List.tabulate (m, fn n => {redex = mk_boolvar n, residue = prime_term n ``x:bool``})

val trainex2 = 
  let val sub = mk_substn 10 in map_fst (subst sub) trainex end
(*
load "mlTreeNeuralNetwork";
open mlTreeNeuralNetwork;

fun mk_boolvar i = mk_var ("V" ^ its i,bool);
val vl = mk_term_set (List.concat (map (free_vars_lr o fst) trainex));
val operl = 
  [(``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2),(``$= :bool -> bool -> bool``,2)] @ 
  map (fn x => (x,0)) vl;

val operl = 
  [(``$/\``,2),(``$\/``,2),(``$~``,1),(``$==>``,2),(``$= :bool -> bool -> bool``,2)] @ 
  [(``x:bool``,0),(prime_tag,1)];


val randtnn = random_tnn (16,1) operl;
val bsize = 128;
fun f x = (100, x / (Real.fromInt bsize));
val schedule = map f [0.1];
val ncore = 2;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex2,first_n 1000 trainex2) schedule;

val r1 = accuracy_set tnn trainex;

*)

(*
load "mleEntail"; load "smlParallel";
open aiLib smlParallel mlTreeNeuralNetwork mleEntail;

val level = 10;
val tml = gen_tml (operl_gen 4) level 4000;

val testex = List.concat (parmap_queue 4 (gen_ex tml) [200,200,200,200]);
val trainex = List.concat (parmap_queue 4 (gen_ex tml) [2000,2000,2000,2000]);

val randtnn = random_tnn (12,1) (operl_nn 4);
val bsize = 128;
fun f x = (100, x / (Real.fromInt bsize));
val schedule = map f [0.1];
val ncore = 4;
val tnn = prepare_train_tnn (ncore,bsize) randtnn (trainex,testex) schedule;

val r1 = accuracy_set tnn trainex;
*)

end (* struct *)
