(****************************************************************************)
(* FILE          : NumArithCons.sml                                         *)
(* DESCRIPTION   : Constructor, destructor and discriminator functions for  *)
(*                 arithmetic terms.                                        *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton, University of Cambridge                     *)
(* DATE          : 4th March 1991                                           *)
(*                                                                          *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 4th February 1993                                        *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton, University of Edinburgh                     *)
(* DATE          : 28th January 1998                                        *)
(****************************************************************************)

structure NumArithCons :> NumArithCons =
struct

open Exception

fun failwith function = raise HOL_ERR{origin_structure = "NumArithCons",
                                      origin_function = function,
                                      message = ""};


local
   open Lib Term Psyntax NumHOLType Parse

   val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
   fun -- q x = Term q
   fun == q x = Type q

in
type term = Term.term
(*==========================================================================*)
(* Constructors, destructors and discriminators for +,-,*                   *)
(*==========================================================================*)

val fun_ty = mk_type ("fun",[num_ty,mk_type ("fun",[num_ty,num_ty])]);

(*--------------------------------------------------------------------------*)
(* mk_plus, mk_minus, mk_mult                                               *)
(*--------------------------------------------------------------------------*)

fun mk_arith_op tok ftok (t1,t2) =
   mk_comb (mk_comb (mk_const (tok,fun_ty),t1),t2)
   handle HOL_ERR _ => failwith ftok;

val mk_plus  = mk_arith_op plus  "mk_plus"
and mk_minus = mk_arith_op minus "mk_minus"
and mk_mult  = mk_arith_op mult  "mk_mult";

(*--------------------------------------------------------------------------*)
(* dest_plus, dest_minus, dest_mult                                         *)
(*--------------------------------------------------------------------------*)

fun dest_arith_op tok ftok =
   let val check = Lib.assert (fn c => dest_const c = (tok,fun_ty))
   in  fn tm => ((let val (Rator,c2) = dest_comb tm
                      val (Rator,c1) = dest_comb Rator
                      val _ = check Rator
                  in  (c1,c2)
                  end)
                 handle HOL_ERR _ => failwith ftok)
   end;

val dest_plus  = dest_arith_op plus  "dest_plus"
and dest_minus = dest_arith_op minus "dest_minus"
and dest_mult  = dest_arith_op mult  "dest_mult";

(*--------------------------------------------------------------------------*)
(* is_plus, is_minus, is_mult, is_arith_op                                  *)
(*--------------------------------------------------------------------------*)

val is_plus  = can dest_plus
and is_minus = can dest_minus
and is_mult  = can dest_mult;

fun is_arith_op tm = type_of (rator (rator tm)) = fun_ty
                     handle HOL_ERR _ => false;

(*==========================================================================*)
(* Constructors, destructors and discriminators for <,<=,>,>=               *)
(*==========================================================================*)

val bool_ty = Type.bool;

val fun_ty = mk_type ("fun",[num_ty,mk_type ("fun",[num_ty,bool_ty])]);

(*--------------------------------------------------------------------------*)
(* mk_less, mk_leq, mk_great, mk_geq                                        *)
(*--------------------------------------------------------------------------*)

fun mk_num_reln tok ftok (t1,t2) =
   mk_comb (mk_comb (mk_const (tok,fun_ty),t1),t2)
   handle HOL_ERR _ => failwith ftok;

val mk_less  = mk_num_reln less  "mk_less"
and mk_leq   = mk_num_reln leq   "mk_leq"
and mk_great = mk_num_reln great "mk_great"
and mk_geq   = mk_num_reln geq   "mk_geq";

(*--------------------------------------------------------------------------*)
(* dest_less, dest_leq, dest_great, dest_geq                                *)
(*--------------------------------------------------------------------------*)

fun dest_num_reln tok ftok =
   let val check = Lib.assert (fn c => dest_const c = (tok,fun_ty))
   in  fn tm => ((let val (Rator,c2) = dest_comb tm
                      val (Rator,c1) = dest_comb Rator
                      val _ = check Rator
                  in  (c1,c2)
                  end)
                 handle HOL_ERR _ => failwith ftok)
   end;

val dest_less  = dest_num_reln less  "dest_less"
and dest_leq   = dest_num_reln leq   "dest_leq"
and dest_great = dest_num_reln great "dest_great"
and dest_geq   = dest_num_reln geq   "dest_geq";

(*--------------------------------------------------------------------------*)
(* is_less, is_leq, is_great, is_geq, is_num_reln                           *)
(*--------------------------------------------------------------------------*)

val is_less  = can dest_less
and is_leq   = can dest_leq
and is_great = can dest_great
and is_geq   = can dest_geq;

fun is_num_reln tm = (type_of (rator (rator tm)) = fun_ty
                     handle HOL_ERR _ => false);

(*==========================================================================*)
(* Constructor, destructor and discriminator for SUC                        *)
(*==========================================================================*)

val fun_ty = mk_type ("fun",[num_ty,num_ty]);

fun mk_suc t = mk_comb (mk_const (suc,fun_ty),t)
               handle HOL_ERR _ => failwith "mk_suc";

val dest_suc =
   let val check = Lib.assert (fn c => dest_const c = (suc,fun_ty))
   in  fn tm => ((let val (Rator,c) = dest_comb tm
                      val _ = check Rator
                  in  c
                  end)
                 handle HOL_ERR _ => failwith "dest_suc")
   end;

val is_suc = can dest_suc;

(*==========================================================================*)
(* Constructor, destructor and discriminator for PRE                        *)
(*==========================================================================*)

fun mk_pre t = mk_comb (mk_const (pre,fun_ty),t)
               handle HOL_ERR _ => failwith "mk_pre";

val dest_pre =
   let val check = Lib.assert (fn c => dest_const c = (pre,fun_ty))
   in  fn tm => ((let val (Rator,c) = dest_comb tm
                      val _ = check Rator
                  in  c
                  end)
                 handle HOL_ERR _ => failwith "dest_pre")
   end;

val is_pre = can dest_pre;

(*==========================================================================*)
(* Discriminators for numbers and numeric variables                         *)
(*==========================================================================*)

val is_num_const = Term.is_numeral

local
  val zero_tm = Term`0`
in
  fun is_zero tm = tm = zero_tm
end

fun is_num_var tm =
   #Ty (Rsyntax.dest_var tm) = num_ty handle HOL_ERR _ => false;

(*==========================================================================*)
(* Generation of a numeric variable from a name                             *)
(*==========================================================================*)

fun mk_num_var s = mk_var (s,num_ty) handle HOL_ERR _ => failwith "mk_num_var";

end;

end; (* NumArithCons *)
