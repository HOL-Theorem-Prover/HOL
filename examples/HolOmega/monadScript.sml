(*---------------------------------------------------------------------------
                         Monads in HOL-Omega
                       (Peter Vincent Homeier)
 ---------------------------------------------------------------------------*)

(* Interactive use:
   app load ["bossLib", "Q", "pred_setTheory", "stringTheory"];
*)

structure monadScript =
struct

open HolKernel Parse boolLib
     bossLib numLib IndDefLib
     pred_setTheory arithmeticTheory


val _ = new_theory "monad";


(*---------------------------------------------------------------------------
            Tests of new kinds, types, and terms.
 ---------------------------------------------------------------------------*)

val _ = show_types := true;

val _ = set_trace "kinds" 1;


val ty1 = ``:bool (\'a:<=3.'a)``;
val kd1 = kind_of ty1;
val rk1 = rank_of ty1;
val (ty2,ty3) = dest_app_type ty1;
val kd2 = kind_of ty2;
val rk2 = rank_of ty2;
val kd3 = kind_of ty3;
val rk3 = rank_of ty3;
val (ty4,ty5) = dest_abs_type ty2;
(**)
val _ = if ty4 = ty5 then print "ty4 = ty5\n" else print "ty4 ~= ty5\n";
val _ = if aconv_ty ty4 ty5 then print "aconv_ty ty4 ty5\n" else print "~aconv_ty ty4 ty5\n";
(**)
val kd4 = kind_of ty4;
val rk4 = rank_of ty4;

val tm1 = ``x:bool (\'a:<=3.'a)``;
val _ = ty1 = type_of tm1
fun ck f s ty1 ty2 = (print_type ty1; print " "; print (s^" "); print_type ty2; print " = ";
                      print (if f ty1 ty2 then "true" else "false"); print "\n")
val _ = ck aconv_ty "aconv_ty" ty1 (type_of tm1)
val _ = ck abconv_ty "abconv_ty" ty1 (type_of tm1)
val ty1 = type_of tm1;
val kd1 = kind_of ty1;
val rk1 = rank_of ty1;
val _ = ``:\'a 'b 'c. ('a 'b) ('b 'c) 'c``;
val _ = ``:\'a 'b:ar 1 'c:ar 1 => ar 1.
            (('b:ar 1) ('c:ar 1 => ar 1), 'a ('b:ar 1)) ('c:ar 1 => ar 1)``;
val ty7 = ``:\'a:ty=>ty 'b 'c. ('a 'b) ('b 'c) 'c``;
val ty8 = ``:list ^ty7``;
val ty9 = beta_conv_ty ty8;

(* Now a couple of examples that throw exceptions, properly: *)
(*
``:\'a. 'a 'a``;
``:\'a 'b. ('a 'b) ('b 'a)``;
``:\'a 'b. ('a :<= 2) ((\'c. 'a) :<= 1) 'b`` handle e => Raise e;
val ty10 = ``:\'a 'b. ('a :<= 2) (((!'c :<= 1. 'a) :<= 2) 'b)`` handle e => Raise e;
val ty10 = ``:\'a 'b. ('a :<= 1) (((!'c :<= 1. 'a) :<= 2) 'b)`` handle e => Raise e;
val ty10 = ``:\'a 'b. ('a :<= 1) (((!'c :<= 0. 'a) :<= 2) 'b)`` handle e => Raise e;
val ty10 = ``:\'a 'b. ('a :<= 1) (((!'c :<= 0. 'a) :<= 1) 'b)`` handle e => Raise e;
val ty10 = ``:\'a 'b. ('a :<= 1) (((!'c :<= 0. 'a) :<= 0) 'b)`` handle e => Raise e;
val ty10 = ``:\'a :<= 1 'b. ((!'c :<= 3. 'a) :<= 0) 'b`` handle e => Raise e;
*)
(* More good examples: *)

val ty10 = ``:\'a 'b. ('a :<= 2) ((\'c. 'a) :<= 2) 'b`` handle e => Raise e;

val ty11 = ``:('a:<=2) : ar 5 :<= 2``;
val ty12 = ``:('a) :<= 1``;

val ty13 = ``:bool 'a prod``;
val ty14 = ``:bool ('a) prod``;
val ty15 = ``:bool ('a prod)``;

val ty16 = ``:\'a :<= 1 'b. ((!'c. 'a) :<= 2) 'b`` handle e => Raise e;
val ty17 = ``:\'a 'b. ((!'c. 'a) :<= 2) 'b`` handle e => Raise e;
val ty18 = ``:\'a 'b. (!'c. (!'d. 'c) -> 'a) :<= 2 'b`` handle e => Raise e;

val tm2 = mk_tyabs(``:'a:<=3``, ``\x:('a:<=3) (\'b. 'b). x``);
val tm3 = mk_tycomb(tm2, ``:'c``);
val tm4 = ty_beta_conv tm3;

(* Should fail:
val tm2 = mk_tyabs(``:'a:<=3``, ``\x:('a:<=3) (\'b. 'b). x``);
val tm3 = mk_tycomb(tm2, ``:'c:<=4``) handle e => Raise e;
The above should fail, with message:

Exception raised at Term.mk_tycomb:
universal type variable has insufficient rank
! Uncaught exception: 
! HOL_ERR
*)

(* ----------------------------------------------------------------- *
 * The next examples use alpha-equivalence during typechecking.      *
 * ----------------------------------------------------------------- *)

val tm0 = ``\x. (x : !'a. 'a 'M, x : !'b. 'b 'M)``;

val tm1 = ``\x. (x : 'c (\'a. 'a 'M), x : 'c (\'b. 'b 'M))``;

val tm2 = ``\x. (x : !'a 'b. ('a,'b)'M,
                 x : !'b 'a. ('b,'a)'M)``;

val tm3 = ``\x. (x : ('c,'d) (\'a 'b. ('a,'b)'M),
                 x : ('c,'d) (\'b 'a. ('b,'a)'M))``;

val tm4 = ``\x. (x : ('c,'d) (\'a 'b:ar 2. ('a,'b)'M),
                 x : ('c,'d) (\'b:ar 1 'a. ('b,'a)'M))``;

val ty1 =
 ``:('c:ar 1, 'd:ar 2)
    (\('a:ar 1) ('b:ar 2). ('a:ar 1, 'b:ar 2) ('M:ar 1 => ar 2 => ty))``
and ty2 =
 ``:('c:ar 1, 'd:ar 2)
    (\('b:ar 1) ('a:ar 2). ('b:ar 1, 'a:ar 2) ('M:ar 1 => ar 2 => ty))``;

(*
trace ("debug_pretype",1)
      Term `\x. (x : ('c,'d) (\'a 'b:ar 2. ('a,'b)'M),
                 x : ('c,'d) (\'b:ar 1 'a. ('b,'a)'M))`;
traces();
aconv_ty ty1 ty2;
abconv_ty ty1 ty2;
*)


(* ----------------------------------------------------------------- *
 * The next examples fail to type-check if type checking does not    *
 * include type beta-reduction of type beta-redexes during checking. *
 * ----------------------------------------------------------------- *)


val tm1 = ``\x. (x : 'a (\'b. 'b), x : 'a)`` handle e => Raise e;
val tm2 = ``\x. (x : 'a I, x : 'a)`` handle e => Raise e;


val _ = set_trace "kinds" 2;
val _ = set_trace "kinds" 1;
val _ = set_trace "kinds" 0;

(*---------------------------------------------------------------------------
            Identity Monad
 ---------------------------------------------------------------------------*)

val tha = REWRITE_CONV[combinTheory.I_THM] ``\:'b. !x:'b. I x = x`` handle e => Raise e;
val thb = TY_COMB alpha tha;
val thc = CONV_RULE (DEPTH_CONV TY_BETA_CONV) thb;

(* Tests of failure; all these should fail:
TY_COMB alpha (REFL ``!x:'b. I x = x``) handle e => Raise e;
TY_COMB alpha TRUTH handle e => Raise e;
TY_COMB ``:'a:<=1`` (REFL ``\:'b. !x:'b. I x = x``) handle e => Raise e;
*)

val TY_ABS_TAC :tactic = fn (asl,gl) =>
  let val (lhs,rhs) = dest_eq gl
      val (lv,lbody) = dest_tyabs lhs
      val (rv,rbody) = dest_tyabs rhs
      val rbody' = inst [rv |-> lv] rbody
  in ([(asl,mk_eq(lbody,rbody'))],
      fn ths => TRANS (TY_ABS lv (hd ths))
                      (ALPHA (mk_tyabs(lv,rbody')) rhs))
  end
  handle HOL_ERR e => raise HOL_ERR{message= #message e,
                      origin_function="TY_ABS_TAC", origin_structure="monad"};

val TY_COMB_TAC :tactic = fn (asl,gl) =>
  let val (lhs,rhs) = dest_eq gl
      val (op1,arg1) = dest_tycomb lhs
      val (op2,arg2) = dest_tycomb rhs
      val _ = assert (aconv_ty arg1) arg2
  in ([(asl,mk_eq(op1,op2))],
      fn ths => TRANS (TY_COMB arg1 (hd ths))
                      (ALPHA (mk_tycomb(op2,arg1)) rhs))
  end
  handle HOL_ERR e => raise HOL_ERR{message= #message e,
                      origin_function="TY_COMB_TAC", origin_structure="monad"};

(*
g `(\:'a. P:'c) = (\:'a. P:'c)`;
e TY_ABS_TAC;
e REFL_TAC;

g `(\:'a. P:'c) = (\:'b. P:'c)`;
e TY_ABS_TAC;
e REFL_TAC;

g `(\:'a. T) = (\:'b. T)`;
e TY_ABS_TAC;
e REFL_TAC;

g `!P:bool. (\:'a. P) = (\:'b. (P:bool))`;
e TY_ABS_TAC;
e REFL_TAC;

g `(\:'a. P[:'a:]) = (\:'b. P[:'b:])`;
e TY_ABS_TAC;
e REFL_TAC;

g `P[: (\'a.'a->'a) :] = P[: (\'b.'b->'b) :]`;
e TY_COMB_TAC;
e REFL_TAC;
*)


(* Universal and existential type quantification is done in boolScript:

val TYFORALL_DEF =
 Definition.new_definition
   ("TYFORALL_DEF",     Term `$!: = \P. ((\:'a. P [:'a:]) = (\:'a. T))`);

val _ = (add_type_binder("!:", std_binder_precedence); add_const "!:");

val TYEXISTS_DEF =
 Definition.new_definition
   ("TYEXISTS_DEF",     Term `$?: = \P. ~((\:'a. P [:'a:]) = (\:'a. F))`);

val _ = (add_type_binder("?:", std_binder_precedence); add_const "?:");
*)


val q = `test1 (z:'a) = ?(id: !'a. 'a -> 'a). !x:'a. id [:'a:] x = x`;

(* val test1a_def = new_definition("test1a_def", Term q) handle e => Raise e; *)

val test1_def = Define q handle e => Raise e;


(*---------------------------------------------------------------------------
            Monad type operator, with unit and bind term operators
 ---------------------------------------------------------------------------*)


val monad_def = new_definition("monad_def", Term
   `monad (unit: !'a. 'a -> 'a 'M,
           bind: !'a 'b. 'a 'M -> ('a -> 'b 'M) -> 'b 'M) =
      (* Left unit *)
          (!:'a 'b. !(a:'a) (k:'a -> 'b 'M).
                bind[:'a,'b:] (unit[:'a:] a) k = k a) /\
      (* Right unit *)
          (!:'a. !(m:'a 'M).
                bind[:'a,'a:] m (unit[:'a:]) = m) /\
      (* Associative *)
          (!:'a 'b 'c. !(m:'a 'M) (k:'a -> 'b 'M) (h:'b -> 'c 'M).
                bind[:'a,'c:] m (\a. bind[:'b,'c:] (k a) (\b. h b))
              = bind[:'b,'c:] (bind[:'a,'b:] m (\a. k a)) (\b. h b))
     `) handle e => Raise e;

val _ = ``I : 'a -> 'a I``;

val _ = ``\:'a. I : 'a -> 'a I``;

(*
g `monad ((\:'a. I) : !'a.'a -> 'a I, (\:'a 'b. \(x:'a I) (f:'a -> 'b I). f x))`;
*)


val _ = export_theory();

end; (* structure monadScript *)

