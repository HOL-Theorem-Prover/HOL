(*****************************************************************************)
(* FILE          : arith_cons.sml                                            *)
(* DESCRIPTION   : Constructor, destructor and discriminator functions for   *)
(*                 arithmetic terms.                                         *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th November 1995                                        *)
(*****************************************************************************)

structure Arith_cons :> Arith_cons =
struct

open HolKernel boolLib Rsyntax Arbint Abbrev;
infixr -->;

val << = String.<

local open arithmeticTheory in end;

fun failwith function = raise
 Feedback.HOL_ERR{origin_structure = "Arith_cons",
                   origin_function = function,
                           message = ""};

(*===========================================================================*)
(* Constructors, destructors and discriminators for +,-,*                    *)
(*===========================================================================*)

val num_ty = numSyntax.num_ty
val num2num = num_ty --> num_ty;
val num_op_ty = num_ty --> num_ty --> num_ty;
val num_rel_ty = num_ty --> num_ty --> bool

(*---------------------------------------------------------------------------*)
(* mk_plus, mk_minus, mk_mult                                                *)
(*---------------------------------------------------------------------------*)

fun mk_arith_op tok ftok =
 fn (t1,t2) => 
    (mk_comb{Rator=
        mk_comb{Rator=mk_thy_const{Name=tok, Thy="arithmetic", Ty=num_op_ty},
                Rand = t1}, Rand = t2} handle _ => failwith ftok);

val mk_plus  = mk_arith_op "+" "mk_plus"
and mk_minus = mk_arith_op "-" "mk_minus"
and mk_mult  = mk_arith_op "*" "mk_mult";

(*---------------------------------------------------------------------------*)
(* dest_plus, dest_minus, dest_mult                                          *)
(*---------------------------------------------------------------------------*)

fun dest_arith_op tok ftok =
 let val check = Lib.assert (fn c => dest_const c = {Name=tok,Ty=num_op_ty})
 in  fn tm => ((let val {Rator,Rand = c2} = dest_comb tm
                    val {Rator,Rand = c1} = dest_comb Rator
                    val _ = check Rator
                in  (c1,c2)
                end)
               handle _ => failwith ftok)
 end;

val dest_plus  = dest_arith_op "+" "dest_plus"
and dest_minus = dest_arith_op "-" "dest_minus"
and dest_mult  = dest_arith_op "*" "dest_mult";

(*---------------------------------------------------------------------------*)
(* is_plus, is_minus, is_mult, is_arith_op                                   *)
(*---------------------------------------------------------------------------*)

val is_plus  = can dest_plus
and is_minus = can dest_minus
and is_mult  = can dest_mult;

val is_arith_op =
 fn tm => (type_of (rator (rator tm)) = num_op_ty handle _ => false)

(*===========================================================================*)
(* Constructors, destructors and discriminators for <,<=,>,>=                *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* mk_less, mk_leq, mk_great, mk_geq                                         *)
(*---------------------------------------------------------------------------*)


fun mk_num_reln tok ftok =
 fn (t1,t2) => 
  (mk_comb
     {Rator=mk_comb {Rator=mk_const{Name=tok, Ty = num_rel_ty}, Rand=t1},
      Rand = t2} handle _ => failwith ftok)

val mk_less  = mk_num_reln "<" "mk_less"
and mk_leq   = mk_num_reln "<=" "mk_leq"
and mk_great = mk_num_reln ">" "mk_great"
and mk_geq   = mk_num_reln ">=" "mk_geq";

(*---------------------------------------------------------------------------*)
(* dest_less, dest_leq, dest_great, dest_geq                                 *)
(*---------------------------------------------------------------------------*)

fun dest_num_reln tok ftok =
 let val check = Lib.assert (fn c => dest_const c = {Name=tok,Ty=num_rel_ty})
 in  fn tm => ((let val {Rator,Rand = c2} = dest_comb tm
                    val {Rator,Rand = c1} = dest_comb Rator
                    val _ = check Rator
                in  (c1,c2)
                end)
               handle _ => failwith ftok)
 end;

val dest_less  = dest_num_reln "<" "dest_less"
and dest_leq   = dest_num_reln "<=" "dest_leq"
and dest_great = dest_num_reln ">" "dest_great"
and dest_geq   = dest_num_reln ">=" "dest_geq";

(*---------------------------------------------------------------------------*)
(* is_less, is_leq, is_great, is_geq, is_num_reln                            *)
(*---------------------------------------------------------------------------*)

val is_less  = can dest_less
and is_leq   = can dest_leq
and is_great = can dest_great
and is_geq   = can dest_geq;

val is_num_reln =
 fn tm => (type_of (rator (rator tm)) = num_rel_ty handle _ => false)

(*===========================================================================*)
(* Constructor, destructor and discriminator for SUC                         *)
(*===========================================================================*)

val mk_suc =
 fn t => (mk_comb{Rator = mk_const{Name = "SUC",Ty = num2num}, Rand = t}
              handle _ => failwith "mk_suc")

val dest_suc =
 let val check = Lib.assert (fn c => dest_const c = {Name="SUC",Ty=num2num})
 in  fn tm => ((let val {Rator,Rand = c} = dest_comb tm
                    val _ = check Rator
                in  c
                end)
               handle _ => failwith "dest_suc")
 end;

val is_suc = can dest_suc;

(*===========================================================================*)
(* Constructor, destructor and discriminator for PRE                         *)
(*===========================================================================*)

val mk_pre =
 fn t => (mk_comb{Rator=mk_const{Name="PRE",Ty = num2num},Rand = t}
              handle _ => failwith "mk_pre")

val dest_pre =
 let val check = assert (fn c => dest_const c = {Name = "PRE",Ty = num2num})
 in  fn tm => ((let val {Rator,Rand = c} = dest_comb tm
                    val _ = check Rator
                in  c
                end)
               handle _ => failwith "dest_pre")
 end;

val is_pre = can dest_pre;

(*===========================================================================*)
(* Discriminators for numbers                                                *)
(*===========================================================================*)

val is_num_const = numSyntax.is_numeral
val zero = numSyntax.zero_t
fun is_zero tm = tm = zero


(*===========================================================================*)
(* Conversions between ML integers and numeric constant terms                *)
(*===========================================================================*)

val int_of_term = fromNat o numSyntax.dest_numeral
val term_of_int = numSyntax.mk_numeral o toNat

(*===========================================================================*)
(* Generation of a numeric variable from a name                              *)
(*===========================================================================*)

val mk_num_var =
 fn s => (mk_var{Name=s,Ty = num_ty} handle _ => failwith "mk_num_var")

(*===========================================================================*)
(* Functions to extract the arguments from an application of a binary op.    *)
(*===========================================================================*)

val arg1 = rand o rator
and arg2 = rand;

end
