(****************************************************************************)
(* FILE          : struct_equal.sml                                         *)
(* DESCRIPTION   : Proof procedure for simplifying an equation between two  *)
(*                 data-structures of the same type.                        *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton & T.F.Melham                                 *)
(* DATE          : 4th June 1992                                            *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 2nd October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 2nd October 1995                                         *)
(****************************************************************************)

structure BoyerMooreStructEqual =
struct

local

open HolKernel Parse basicHol90Lib Psyntax;
infix THEN ORELSEC THENC THENL ##;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreStructEqual",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* VAR_NOT_EQ_STRUCT_OF_VAR_CONV : (thm * thm list * thm list) -> conv      *)
(*                                                                          *)
(* Proof method developed through discussion between                        *)
(* R. Boulton, T. Melham and A. Pitts.                                      *)
(*                                                                          *)
(* This conversion can be used to prove that a variable is not equal to a   *)
(* structure containing that variable as a proper subterm. The structures   *)
(* are restricted to applications of constructors from a single recursive   *)
(* type. The leaf nodes must be either variables or 0-ary constructors of   *)
(* the type.                                                                *)
(*                                                                          *)
(* The theorems taken as arguments are the induction, distinctness and      *)
(* injectivity theorems for the recursive type, as proved by the functions: *)
(*                                                                          *)
(*    prove_induction_thm                                                   *)
(*    prove_constructors_distinct                                           *)
(*    prove_constructors_one_one                                            *)
(*                                                                          *)
(* Since the latter two functions may fail, the distinctness and            *)
(* injectivity theorems are passed around as lists of conjuncts, so that a  *)
(* failure results in an empty list.                                        *)
(*                                                                          *)
(* Examples of input terms:                                                 *)
(*                                                                          *)
(*    ~(l = CONS h l)                                                       *)
(*    ~(CONS h1 (CONS h2 l) = l)                                            *)
(*    ~(n = SUC(SUC(SUC n)))                                                *)
(*    ~(t = TWO (ONE u) (THREE v (ONE t) (TWO u (ONE t))))                  *)
(*                                                                          *)
(* where the last example is for the type defined by:                       *)
(*                                                                          *)
(*    test = ZERO | ONE test | TWO test test | THREE test test test         *)
(*                                                                          *)
(* The procedure works by first generalising the structure to eliminate any *)
(* irrelevant substructures. If the variable occurs more than once in the   *)
(* structure the more deeply nested occurrences are replaced by new         *)
(* variables because multiple occurrences of the variable prevent the       *)
(* induction from working. The generalised term for the last example is:    *)
(*                                                                          *)
(*    TWO a (THREE v (ONE t) b)                                             *)
(*                                                                          *)
(* The procedure then forms a conjunction of the inequalities for this term *)
(* and all of its "rotations':                                              *)
(*                                                                          *)
(*    !t. (!a v b. ~(t = TWO a (THREE v (ONE t) b))) /\                     *)
(*        (!a v b. ~(t = THREE v (ONE (TWO a t)) b)) /\                     *)
(*        (!a v b. ~(t = ONE (TWO a (THREE v t b))))                        *)
(*                                                                          *)
(* This can be proved by a straightforward structural induction. The reason *)
(* for including the rotations is that the induction hypothesis required    *)
(* for the proof of the original generalised term is the rotation of it.    *)
(*                                                                          *)
(* The procedure could be optimised by detecting duplicated rotations. For  *)
(* example it is not necessary to prove:                                    *)
(*                                                                          *)
(*    !n. ~(n = SUC(SUC(SUC n))) /\                                         *)
(*        ~(n = SUC(SUC(SUC n))) /\                                         *)
(*        ~(n = SUC(SUC(SUC n)))                                            *)
(*                                                                          *)
(* in order to prove (--`~(n = SUC(SUC(SUC n)))`--) because the structure   *)
(* is its own rotations. It is sufficient to prove:                         *)
(*                                                                          *)
(*    !n. ~(n = SUC(SUC(SUC n)))                                            *)
(*                                                                          *)
(* The procedure currently uses backwards proof. It would probably be more  *)
(* efficient to use forwards proof.                                         *)
(*--------------------------------------------------------------------------*)

val VAR_NOT_EQ_STRUCT_OF_VAR_CONV =
   let fun number_list l =
          let fun number_list' n [] = []
                | number_list' n (x::xs) = (x,n)::(number_list' (n + 1) xs)
          in  number_list' 1 l
          end
       val name = #Name o Rsyntax.dest_const
       fun occurrences constrs v st =
          let fun occurrences' v st path =
                 if not (type_of st = type_of v) then []
                 else if (st = v) then [rev path]
                 else if (is_var st) then []
                 else let val (f,args) =
                             (assert ((can (C assoc constrs)) o name) ## I)
                                (strip_comb st)
                      in  flatten
                             (map (fn (arg,n) => occurrences' v arg (n::path))
                                 (number_list args))
                      end
          in  occurrences' v st []
          end
       fun min_length [] = failwith "min_length"
         | min_length (x::xs) =
          let fun min_length' (x,n) [] = x
                | min_length' (x,n) (y::ys) =
                 if (length y < n)
                 then min_length' (y,length y) ys
                 else min_length' (x,n) ys
          in  min_length' (x,length x) xs
          end
       fun generalise (st,[]) = (st,[])
         | generalise (st,n::occ) =
          let fun replace_side_structs (n,argn',binding) m [] = ([],[])
                | replace_side_structs (n,argn',binding) m (arg::args) =
                 let val m' = m + 1
                     val (rest,bind) =
                        replace_side_structs (n,argn',binding) m' args
                 in  if (m' = n) then ((argn'::rest),(binding @ bind))
                     else if (is_var arg) then ((arg::rest),((arg,arg)::bind))
                     else let val var = genvar (type_of arg)
                          in  ((var::rest),((var,arg)::bind))
                          end
                 end
              val (f,args) = strip_comb st
              val (argn',binding) = generalise (el n args,occ)
              val (args',bind) = replace_side_structs (n,argn',binding) 0 args
          in  (list_mk_comb (f,args'),bind)
          end
       fun constr_apps v (st,[]) = []
         | constr_apps v (st,n::occ) =
          let fun replace_argn (n,argn') m [] = []
                | replace_argn (n,argn') m (arg::args) =
                 let val m' = m + 1
                 in  if (m' = n)
                     then argn'::args
                     else arg::(replace_argn (n,argn') m' args)
                 end
              val (f,args) = strip_comb st
              val args' = replace_argn (n,v) 0 args
          in  (list_mk_comb (f,args'))::(constr_apps v (el n args,occ))
          end
       fun rotations l =
          let fun rotations' l n =
                 if (n < 1)
                 then []
                 else l::(rotations' (tl l @ [hd l]) (n - 1))
          in  rotations' l (length l)
          end
       val two_constrs = ((#1 o strip_comb) ## (#1 o strip_comb)) o
                         dest_eq o dest_neg o #2 o strip_forall o concl
       fun flip (x,y) = (y,x)
       val DEPTH_SYM = GEN_ALL o NOT_EQ_SYM o SPEC_ALL
       fun arg_types ty =
          (case (Rsyntax.dest_type ty)
           of {Tyop = "fun",Args = [argty,rest]} => argty::(arg_types rest)
            | _ => [])
          handle HOL_ERR _ => []
       val name_and_args = (I ## arg_types) o dest_const
   in
   fn (Induction,Distincts,OneOnes) =>
      let val half_distincts =
             map (fn th => ((name ## name) (two_constrs th),th)) Distincts
          val distincts =
             half_distincts @ (map (flip ## DEPTH_SYM) half_distincts)
          val ind_goals =
             (strip_conj o #1 o dest_imp o #2 o dest_forall o concl) Induction
          val constrs =
             map (name_and_args o #1 o strip_comb o rand o #2 o strip_forall o
                  #2 o strip_imp o #2 o strip_forall) ind_goals
      in
      fn tm =>
         let val (l,r) = dest_eq (dest_neg tm)
             val (flipped,v,st) =
                if (is_var l)
                then if (is_var r) then failwith "" else (false,l,r)
                else if (is_var r)
                     then (true,r,l)
                     else failwith ""
             val occ = min_length (occurrences constrs v st)
             val (st',bind) = generalise (st,occ)
             val (vars,subterms) = split bind
             val apps = constr_apps v (st',occ)
             val rotats =
                map (end_itlist (fn t1 => fn t2 => subst [(t2,v)] t1))
                   (rotations apps)
             val uneqs = map (mk_neg o curry mk_eq v) rotats
             val conj =
                mk_forall
                   (v,list_mk_conj (map (curry list_mk_forall vars) uneqs))
             val th1 =
                prove (conj,INDUCT_THEN Induction ASSUME_TAC THEN
                            ASM_REWRITE_TAC (OneOnes @ map #2 distincts))
             val th2 = (hd o CONJUNCTS o SPEC v) th1
             val th3 = SPECL subterms th2
             val th4 = if flipped then (NOT_EQ_SYM th3) else th3
         in  EQT_INTRO (CONV_RULE (C ALPHA tm) th4)
         end
         handle HOL_ERR _ => failwith "VAR_NOT_EQ_STRUCT_OF_VAR_CONV"
      end
   end;

(*--------------------------------------------------------------------------*)
(* CONJS_CONV : conv -> conv                                                *)
(*                                                                          *)
(* Written by T.F.Melham.                                                   *)
(* Modified by R.J.Boulton.                                                 *)
(*                                                                          *)
(* Apply a given conversion to a sequence of conjuncts.                     *)
(*                                                                          *)
(* * need to check T case                                                   *)
(* * need to flatten conjuncts on RHS                                       *)
(*--------------------------------------------------------------------------*)

val CONJS_CONV =
   let fun is st th = #Name (Rsyntax.dest_const (rand (concl th))) = st
                      handle HOL_ERR _ => false
       val v1 = genvar (==`:bool`==) and v2 = genvar (==`:bool`==)
       val Fthm1 =
          let val th1 = ASSUME (mk_eq (v1,(--`F`--)))
              val cnj = mk_conj (v1,v2)
              val th1 = DISCH cnj (EQ_MP th1 (CONJUNCT1 (ASSUME cnj)))
              val th2 = DISCH (--`F`--) (CONTR cnj (ASSUME (--`F`--)))
          in  DISCH (mk_eq (v1,(--`F`--))) (IMP_ANTISYM_RULE th1 th2)
          end
       val Fthm2 = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV CONJ_SYM)) Fthm1
       fun Fandr th tm = MP (INST [(lhs (concl th),v1),(tm,v2)] Fthm1) th
       fun Fandl th tm = MP (INST [(lhs (concl th),v1),(tm,v2)] Fthm2) th
       val Tthm1 =
          let val th1 = ASSUME (mk_eq (v1,(--`T`--)))
              val th2 = SUBS_OCCS [([2],th1)] (REFL (mk_conj (v1,v2)))
          in  DISCH (mk_eq (v1,(--`T`--))) (ONCE_REWRITE_RULE [] th2)
          end
       val Tthm2 = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV CONJ_SYM)) Tthm1
       fun Tandr th tm = MP (INST [(lhs (concl th),v1),(tm,v2)] Tthm1) th
       fun Tandl th tm = MP (INST [(lhs (concl th),v1),(tm,v2)] Tthm2) th
       fun cconv conv tm =
          let val (c,cs) = dest_conj tm
              val cth = conv c
          in  if (is "F" cth)
              then Fandr cth cs
              else let val csth = cconv conv cs
                   in  if (is "F" csth) then Fandl csth c
                       else if (is "T" cth) then TRANS (Tandr cth cs) csth
                       else if (is "T" csth) then TRANS (Tandl csth c) cth
                       else MK_COMB (AP_TERM (--`$/\`--) cth,csth)
                   end
          end
          handle HOL_ERR _ => conv tm
   in  fn conv => fn tm =>
                     (cconv conv tm handle HOL_ERR _ => failwith "CONJS_CONV")
   end;

(*--------------------------------------------------------------------------*)
(* ONE_STEP_RECTY_EQ_CONV : (thm * thm list * thm list) -> conv -> conv     *)
(*                                                                          *)
(* Single step conversion for equality between structures of a single       *)
(* recursive type.                                                          *)
(*                                                                          *)
(* Based on code written by T.F.Melham.                                     *)
(*                                                                          *)
(* The theorems taken as arguments are the induction, distinctness and      *)
(* injectivity theorems for the recursive type, as proved by the functions: *)
(*                                                                          *)
(*    prove_induction_thm                                                   *)
(*    prove_constructors_distinct                                           *)
(*    prove_constructors_one_one                                            *)
(*                                                                          *)
(* Since the latter two functions may fail, the distinctness and            *)
(* injectivity theorems are passed around as lists of conjuncts.            *)
(*                                                                          *)
(* If one side of the equation is a variable and that variable appears in   *)
(* the other side (nested in a structure) the equation is proved false.     *)
(*                                                                          *)
(* If the top-level constructors on the two sides of the equation are       *)
(* distinct the equation is proved false.                                   *)
(*                                                                          *)
(* If the top-level constructors on the two sides of the equation are the   *)
(* same a conjunction of equations is generated, one equation for each      *)
(* argument of the constructor. The conversion given as argument is then    *)
(* applied to each conjunct. If any of the applications of this conversion  *)
(* fail, so will the entire call.                                           *)
(*                                                                          *)
(* In other conditions the function fails.                                  *)
(*--------------------------------------------------------------------------*)

fun ONE_STEP_RECTY_EQ_CONV (Induction,Distincts,OneOnes) =
   let val NOT_EQ_CONV =
          EQF_INTRO o EQT_ELIM o
          (VAR_NOT_EQ_STRUCT_OF_VAR_CONV (Induction,Distincts,OneOnes)) o
          mk_neg
       val INJ_REW = GEN_REWRITE_CONV I empty_rewrites OneOnes
       val ths1 = map SPEC_ALL Distincts
       val ths2 = map (GEN_ALL o EQF_INTRO o NOT_EQ_SYM) ths1
       val dths = ths2 @ (map (GEN_ALL o EQF_INTRO) ths1)
       val DIST_REW = GEN_REWRITE_CONV I empty_rewrites dths
   in  fn conv => NOT_EQ_CONV ORELSEC
                  DIST_REW ORELSEC
                  (INJ_REW THENC (CONJS_CONV conv)) ORELSEC
                  (fn tm => failwith "ONE_STEP_RECTY_EQ_CONV")
   end;

(*--------------------------------------------------------------------------*)
(* RECTY_EQ_CONV : (thm * thm list * thm list) -> conv                      *)
(*                                                                          *)
(* Function to simplify as far as possible an equation between two          *)
(* structures of some type, the type being specified by the triple of       *)
(* theorems. The structures may involve variables. The result may be a      *)
(* conjunction of equations simpler than the original.                      *)
(*--------------------------------------------------------------------------*)

fun RECTY_EQ_CONV (Induction,Distincts,OneOnes) =
   let val one_step_conv = ONE_STEP_RECTY_EQ_CONV (Induction,Distincts,OneOnes)
       fun REFL_CONV tm =
          let val (l,r) = dest_eq tm
          in  if (l = r)
              then EQT_INTRO (REFL l)
              else failwith "REFL_CONV"
          end
       fun conv tm = (one_step_conv conv ORELSEC REFL_CONV ORELSEC ALL_CONV) tm
   in  fn tm => (conv tm handle HOL_ERR _ => failwith "RECTY_EQ_CONV")
   end;

end;

end; (* BoyerMooreStructEqual *)
