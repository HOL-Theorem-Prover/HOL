structure cpsSyntax :> cpsSyntax =
struct

open Feedback Lib HolKernel boolLib cpsTheory;

val ERR = mk_HOL_ERR "cpsSyntax";

val seq_tm = prim_mk_const {Name="Seq", Thy="cps"};
val par_tm = prim_mk_const {Name="Par", Thy="cps"};
val ite_tm = prim_mk_const {Name="Ite", Thy="cps"};
val rec_tm = prim_mk_const {Name="Rec", Thy="cps"};

fun mk_seq(f1,f2) =
 let val (d1,r1) = dom_rng (type_of f1)
     val (d2,r2) = dom_rng (type_of f2)
 in
   list_mk_comb(inst[alpha|->d1,beta|->r1,gamma |-> r2]seq_tm,[f1,f2])
 end
 handle e => raise wrap_exn "cpsSyntax" "mk_seq" e;

fun mk_par(f1,f2) =
 let val (d1,r1) = dom_rng (type_of f1)
     val (d2,r2) = dom_rng (type_of f2)
 in
   list_mk_comb(inst[alpha|->d1,beta|->r1,gamma |-> r2]par_tm,[f1,f2])
 end
 handle e => raise wrap_exn "cpsSyntax" "mk_par" e;

fun mk_ite(f1,f2,f3) =
 let val (d1,_) = dom_rng (type_of f1)
     val (_,r2) = dom_rng (type_of f2)
 in
   list_mk_comb(inst[alpha|->d1,beta|->r2]ite_tm,[f1,f2,f3])
 end
 handle e => raise wrap_exn "cpsSyntax" "mk_ite" e;

fun mk_rec(f1,f2,f3) =
 let val (d1,_) = dom_rng (type_of f1)
     val (_,r2) = dom_rng (type_of f2)
 in
   list_mk_comb(inst[alpha|->d1,beta|->r2]rec_tm,[f1,f2,f3])
 end
 handle e => raise wrap_exn "cpsSyntax" "mk_rec" e;


val dest_seq = dest_binop seq_tm (ERR "dest_seq" "");
val dest_par = dest_binop par_tm (ERR "dest_par" "");
val dest_ite = dest_triop ite_tm (ERR "dest_ite" "");
val dest_rec = dest_triop rec_tm (ERR "dest_rec" "");

(* Possibly useful: pinched from mjcg's examples/dev/compile.sml

(*****************************************************************************)
(* Check if term tm is a well-formed expression built out of Seq, Par, Ite,  *)
(* and Rec and if so return a pair (constructor, args), else return (tm,[])  *)
(*****************************************************************************)

fun dest_exp tm =
 if not(fst(dest_type(type_of tm)) = "fun")
  then (print_term tm;print "\n";
        print "is not a function";
        raise ERR "dest_exp" "dest_exp failure")
  else if is_comb tm
          andalso is_const(fst(strip_comb tm))
          andalso mem
                   (fst(dest_const(fst(strip_comb tm))))
                   ["Seq","Par","Ite","Rec"]
  then
   let val (opr,args) = strip_comb tm
   in
   case fst(dest_const opr) of
      "Seq" => if length args = 2
                then (opr, args)
                else raise ERR "dest_exp" "bad Seq"
    | "Par" => if length args = 2
                then (opr, args)
                else raise ERR "dest_exp" "bad Par"
    | "Ite" => if length args = 3
                then (opr, args)
                else raise ERR "dest_exp" "bad Ite"
    | "Rec" => if length args = 3
                then (opr, args)
                else raise ERR "dest_exp" "bad Rec"
    | _     => raise ERR "dest_exp" "this shouldn't happen"
   end
  else (tm,[]);
*)


val is_seq = Lib.can dest_seq
val is_par = Lib.can dest_par
val is_ite = Lib.can dest_ite
val is_rec = Lib.can dest_rec

end
