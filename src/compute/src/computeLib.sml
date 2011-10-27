structure computeLib :> computeLib =
struct

open HolKernel boolSyntax boolTheory Abbrev clauses compute_rules equations;

val auto_import_definitions = ref true;

(* re-exporting types from clauses *)

type compset = comp_rws;

type db_fterm = db fterm
type db_dterm = db dterm

val new_compset = from_list;

type cbv_stack =
  ((thm->thm->thm) * (thm * db fterm),
   (thm->thm->thm) * bool * (thm * db fterm),
   (thm->thm),
   (thm->thm) * hol_type,
   (thm->thm)
  ) stack;

fun pp_thm_fterm pps (th:thm, ftm:db fterm) =
  let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_thm = Parse.pp_thm pps
     val pp_fterm = pp_fterm pps
 in
   add_string "(";
   begin_block INCONSISTENT 0;
   pp_thm th;
   add_string ","; add_break(1,0);
   pp_fterm ftm;
   end_block();
   add_string ")"
 end

fun pp_b_thm_fterm pps (b:bool, th_ftm:thm * db fterm) =
  let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_thm_fterm = pp_thm_fterm pps
 in
   add_string "(";
   begin_block INCONSISTENT 0;
   if b then add_string "true" else add_string "false";
   add_string ","; add_break(1,0);
   pp_thm_fterm th_ftm;
   end_block();
   add_string ")"
 end

val pp_cbv_stack : ppstream -> cbv_stack -> unit
  = pp_stack ( (fn pps => fn (_,th_ftm) => pp_thm_fterm pps th_ftm),
               (fn pps => fn (_,b,th_ftm) => pp_b_thm_fterm pps (b,th_ftm)),
               (fn pps => fn (_) => ()),
               (fn pps => fn (_,ty) => Parse.pp_type pps ty),
               (fn pps => fn (_) => ()) )

fun pp_cfg pps ((th,v),stk:cbv_stack) =
  let open Portable
     val {add_string,add_break,begin_block,end_block,...} = with_ppstream pps
     val pp_thm = Parse.pp_thm pps
     val pp_dterm = pp_dterm pps
     val pp_fterm = pp_fterm pps
     val pp_cbv_stack = pp_cbv_stack pps
  in
    begin_block CONSISTENT 0;
    add_string "Thm ="; add_break(1,2);
    begin_block INCONSISTENT 0;
      pp_thm th;
    end_block();
    add_string "\n";
    add_string "Ftm ="; add_break(1,2);
    begin_block INCONSISTENT 0;
      pp_fterm v;
    end_block();
    add_string "\n";
    add_string "Ctx ="; add_break(1,2);
    begin_block INCONSISTENT 0;
      pp_cbv_stack stk;
    end_block();
    end_block();
    add_string "\n\n"
  end;

fun make_to_backend_string ppf x = Portable.pp_to_string (!Globals.linewidth) ppf x
fun lazy_make_to_string ppf = Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal) (fn x => make_to_backend_string (ppf()) x)
fun make_to_string ppf = lazy_make_to_string (fn()=>ppf)
fun make_print to_string t = Portable.output(Portable.std_out, to_string t)

val type_to_string = Parse.type_to_string
val term_to_string = Parse.term_to_string
val  thm_to_string = Parse.thm_to_string

val cfg_to_string = make_to_string (pp_cfg : ppstream -> (thm * db fterm) * cbv_stack -> unit);
val print_cfg = make_print cfg_to_string;

fun stack_out(th, Ztop) = th
  | stack_out(th, Zrator{Rand=(mka,(thb,_)), Ctx}) = stack_out(mka th thb,Ctx)
  | stack_out(th,Zrand{Rator=(mka,_,(tha,_)),Ctx}) = stack_out(mka tha th, Ctx)
  | stack_out(th, Zabs{Bvar=mkl, Ctx})             = stack_out(mkl th, Ctx)
  | stack_out(th, Ztyrator{Rand=(mk1,_), Ctx})     = stack_out(mk1 th, Ctx)
  | stack_out(th, Ztyabs{Bvar=mkl, Ctx})           = stack_out(mkl th, Ctx)
;


fun initial_state rws t =
  ((refl_thm t, mk_clos([],from_term (rws,[],t))), Ztop : cbv_stack);


val trace_steps = ref true;

datatype direction = wk | up | done;

fun cbv (wk, ((th,CLOS{Env, Term=App(a,args)}), stk)) =
      let val (tha,stka) =
            foldl (push_in_stk (curry mk_clos Env)) (th,stk) args
      in
      if !trace_steps
        then print "Push term arguments on stack, and focus on operator.\n\n"
        else ();
      (wk, ((tha, mk_clos(Env,a)), stka))
      end
  | cbv (wk, ((th,CLOS{Env, Term=Abs body}),
	    Zrator{Rand=(mka,(thb,cl)), Ctx=s'})) =
     (if !trace_steps
        then print ("Beta reduce this abs with the first term argument above,\n" ^
                    (term_to_string (rhs_concl thb)) ^
                    ", on the theorem\n" ^
                    (thm_to_string (mka th thb)) ^ ".\n\n")
        else ();
      (wk, ((beta_thm(mka th thb), mk_clos(cl :: Env, body)), s')))
  | cbv (wk, ((th,CLOS{Env, Term=TyApp(a,args)}), stk)) =
      let val (tha,stka) =
            foldl push_tycomb_in_stk (th,stk) args in
      if !trace_steps
        then print "Push type arguments on stack, and focus on operator.\n\n"
        else ();
      (wk, ((tha, mk_clos(Env,a)), stka))
      end
  | cbv (wk, ((th,CLOS{Env, Term=TyAbs(tyv,body)}),
	    Ztyrator{Rand=(mkl,ty), Ctx=s'})) =
      let val body' = inst_type_dterm([tyv |-> ty], body) in
      if !trace_steps
        then print ("Type-beta reduce this tyabs with the first type argument above, " ^
                    (type_to_string ty) ^
                    ", on the theorem\n" ^
                    (thm_to_string (mkl th)) ^ ".\n\n")
        else ();
      (wk, ((tybeta_thm(mkl th), mk_clos(Env, body')), s'))
      end
  | cbv (wk, ((th,CST cargs), stk)) =
      let val (reduced,clos) = reduce_cst (th,cargs) in
      if !trace_steps
        then print ((if reduced then "Successfully" else "Failed to")
                      ^ " reduce (replace) this constant.\n\n")
        else ();
      if reduced then (wk, (clos,stk)) else (up, (clos,stk))
      end
  | cbv (wk, (clos, stk)) =
     (if !trace_steps
        then print "Can't go down any more, start going up.\n\n"
        else ();
      (up, (clos,stk)))

  | cbv (up, (hcl, Zrator{Rand=(mka,clos), Ctx}))  =
      let val new_state = (clos, Zrand{Rator=(mka,false,hcl), Ctx=Ctx}) in
      if !trace_steps
        then print ("Store " ^ term_to_string (rhs_concl (fst hcl)) ^
                    " on stack, and shift to " ^ term_to_string (rhs_concl (fst clos)) ^
                    "; going " ^
                    (if is_skip hcl then "up " else "down")
                      ^ ".\n\n")
        else ();
      if is_skip hcl then (up, new_state) else (wk, new_state)
      end
  | cbv (up, ((thb,v), Zrand{Rator=(mka,false,(th,CST cargs)), Ctx=stk})) =
     (if !trace_steps
        then print ("Finished " ^ term_to_string (rhs_concl thb) ^
                    "; combining with constant Rator and going down on\n" ^
                    (term_to_string (rhs_concl (mka th thb)))
                      ^ " .\n\n")
        else ();
      (wk, ((mka th thb, comb_ct cargs (inR(rhs_concl thb, v))), stk)))
  | cbv (up, ((thb,NEUTR), Zrand{Rator=(mka,false,(th,NEUTR)), Ctx=stk})) =
     (if !trace_steps
        then print ("Finished " ^ term_to_string (rhs_concl thb) ^
                    "; combining with neutral Rator and going up on\n" ^
                    (term_to_string (rhs_concl (mka th thb)))
                      ^ " .\n\n")
        else ();
      (up, ((mka th thb, NEUTR), stk)))
  | cbv (up, ((th,CST cargs), Ztyrator{Rand=(mkl,ty), Ctx=stk})) =
     (if !trace_steps
        then print ("Finished " ^ term_to_string (rhs_concl th) ^ " as tyrator" ^
                    "; combining with constant Rator (type) and going down on\n" ^
                    (term_to_string (rhs_concl (mkl th)))
                      ^ " .\n\n")
        else ();
      (wk, ((mkl th, comb_ct cargs (inL ty)), stk)))
  | cbv (up, ((th,v), Ztyrator{Rand=(mkl,ty), Ctx=stk})) =
     (if !trace_steps
        then print ("Finished " ^ term_to_string (rhs_concl th) ^ " as tyrator" ^
                    "; combining with non-constant Rator and going down on\n" ^
                    (term_to_string (rhs_concl (mkl th)))
                      ^ " .\n\n")
        else ();
      (wk, ((mkl th, v), stk)))
  | cbv (up, (clos, stk)) = (done, (clos,stk))

  | cbv (done, (clos, stk)) = raise DEAD_CODE "cbv(done)"
;

fun print_trace s (dir,cfg) =
  if !trace_steps then (if s=0 then print "\n" else ();
                        print ("Step " ^ Int.toString s ^ ", going ");
                        print (case dir of wk => "down" | _ => "up");
                        print (":\n");
                        print_cfg cfg) else ();

fun steps m (x as (dir,_)) = 
       if dir=done
       then (print ("Done! (Took " ^ Int.toString m ^ " steps)\n"); x)
       else let val z = cbv x
            in
              print "Weak ";
              print_trace (m+1) z;
              steps (m+1) z
            end;

(*---------------------------------------------------------------------------
 * [cbv_wk (rws,(th,cl),stk)] puts the closure cl (useful information about
 * the rhs of th) in head normal form (weak reduction). It returns either
 * a closure which term is an abstraction, in a context other than Zappl,
 * a variable applied to strongly reduced arguments, or a constant
 * applied to weakly reduced arguments which does not match any rewriting
 * rule.
 *
 * - substitution is propagated through applications.
 * - if the rhs is an abstraction and there is one arg on the stack,
 *   this means we found a beta redex. mka rebuilds the application of
 *   the function to its argument, and Beta does the actual beta step.
 * - for an applied constant, we look for a rewrite matching it.
 *   If we found one, then we apply the instantiated rule, and go on.
 *   Otherwise, we try to rebuild the thm.
 * - for an already strongly normalized term or an unapplied abstraction,
 *   we try to rebuild the thm.
 *---------------------------------------------------------------------------*)

fun cbv_wk ((th,CLOS{Env, Term=App(a,args)}), stk) =
      let val (tha,stka) =
            foldl (push_in_stk (curry mk_clos Env)) (th,stk) args in
      cbv_wk ((tha, mk_clos(Env,a)), stka)
      end
  | cbv_wk ((th,CLOS{Env, Term=Abs body}),
	    Zrator{Rand=(mka,(thb,cl)), Ctx=s'}) =
      cbv_wk ((beta_thm(mka th thb), mk_clos(cl :: Env, body)), s')
  | cbv_wk ((th,CLOS{Env, Term=TyApp(a,args)}), stk) =
      let val (tha,stka) =
            foldl push_tycomb_in_stk (th,stk) args in
      cbv_wk ((tha, mk_clos(Env,a)), stka)
      end
  | cbv_wk ((th,CLOS{Env, Term=TyAbs(tyv,body)}),
	    Ztyrator{Rand=(mkl,ty), Ctx=s'}) =
      let val body' = inst_type_dterm([tyv |-> ty], body) in
      cbv_wk ((tybeta_thm(mkl th), mk_clos(Env, body')), s')
      end
  | cbv_wk ((th,CST cargs), stk) =
      let val (reduced,clos) = reduce_cst (th,cargs) in
      if reduced then cbv_wk (clos,stk) else cbv_up (clos,stk)
      end
  | cbv_wk (clos, stk) = cbv_up (clos,stk)


(*---------------------------------------------------------------------------
 * Tries to rebuild the thm, knowing that the closure has been weakly
 * normalized, until it finds term still to reduce, or if a strong reduction
 * may be required.
 *  - if we are done with a Rator, we start reducing the Rand
 *  - if we are done with the Rand of a const, we rebuild the application
 *    and look if it created a redex
 *  - an application to a NEUTR can be rebuilt only if the argument has been
 *    strongly reduced, which we now for sure only if itself is a NEUTR.
 *---------------------------------------------------------------------------*)

and cbv_up (hcl, Zrator{Rand=(mka,clos), Ctx})  =
      let val new_state = (clos, Zrand{Rator=(mka,false,hcl), Ctx=Ctx}) in
      if is_skip hcl then cbv_up new_state else cbv_wk new_state
      end
  | cbv_up ((thb,v), Zrand{Rator=(mka,false,(th,CST cargs)), Ctx=stk}) =
      cbv_wk ((mka th thb, comb_ct cargs (inR(rhs_concl thb, v))), stk)
  | cbv_up ((thb,NEUTR), Zrand{Rator=(mka,false,(th,NEUTR)), Ctx=stk}) =
      cbv_up ((mka th thb, NEUTR), stk)
  | cbv_up ((th,CST cargs), Ztyrator{Rand=(mkl,ty), Ctx=stk}) =
      cbv_wk ((mkl th, comb_ct cargs (inL ty)), stk)
  | cbv_up ((th,v), Ztyrator{Rand=(mkl,ty), Ctx=stk}) =
      cbv_wk ((mkl th, v), stk)
  | cbv_up (clos, stk) = (clos,stk)
;

local
val cbv_wk = fn cfg =>
  (print "Beginning weak reduction.\n";
   print_trace 0 (wk,cfg);
   let val (dir,res) = steps 0 (wk,cfg)
   in print "\nEnding weak reduction.\n\n";
      res
   end)
in
fun str (wk, ((th, CLOS{Env,Term=Abs t}), stk)) =
      let val (thb,stk') = push_lam_in_stk(th,stk) in
      (wk, (cbv_wk((thb, mk_clos(NEUTR :: Env, t)), stk')))
      end
  | str (wk, ((th, CLOS{Env,Term=TyAbs(tyv,body)}), stk)) =
      let val (thb,stk') = push_tylam_in_stk(th,stk) in
      (wk, (cbv_wk((thb, mk_clos(Env, body)), stk')))
      end
  | str (wk, (clos as (_,CLOS _), stk)) = raise DEAD_CODE "str"
  | str (wk, (hcl as (th,CST {Args,...}), stk)) =
      let val (th',stk') =
 	if is_skip hcl then (th,stk)
 	else foldl push_arg_in_stk (th,stk) Args in
      (up, ((th',NEUTR),stk'))
      end
  | str (wk, ((th, NEUTR), stk)) = (up, ((th,NEUTR),stk))

  | str (up, ((th,_), Ztop)) = (done, ((th,NEUTR), Ztop))
  | str (up, ((th,_), Zrand{Rator=(mka,false,(tha,NEUTR)), Ctx})) =
      (wk, (cbv_wk((mka tha th,NEUTR), Ctx)))
  | str (up, ((th,_), Zrand{Rator=(mka,false,clos), Ctx})) =
      raise DEAD_CODE "str (up)"
  | str (up, ((th,_), Zrator{Rand=(mka,clos), Ctx})) =
      (wk, (cbv_wk(clos, Zrand{Rator=(mka,true,(th,NEUTR)), Ctx=Ctx})))
  | str (up, ((th,_), Zrand{Rator=(mka,true,(tha,_)), Ctx})) =
      (up, ((mka tha th,NEUTR), Ctx))
  | str (up, ((th,_), Zabs{Bvar=mkl, Ctx})) = (up, ((mkl th,NEUTR), Ctx))
  | str (up, ((th,_), Ztyrator{Rand=(mk1,ty), Ctx})) = (up, ((mk1 th,NEUTR), Ctx))
  | str (up, ((th,_), Ztyabs{Bvar=mkl, Ctx})) = (up, ((mkl th,NEUTR), Ctx))

  | str (done, (th,_)) = raise DEAD_CODE "str done"
end;

fun steps_str m (x as (dir,_)) = 
       if dir=done
       then (print ("Done! (Took " ^ Int.toString m ^ " steps)\n"); x)
       else let val z = str x
            in
              print "Strong ";
              print_trace (m+1) z;
              steps_str (m+1) z
            end;

(*---------------------------------------------------------------------------
 * [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 * precondition: the closure should be the output of cbv_wk
 *---------------------------------------------------------------------------*)

fun strong ((th, CLOS{Env,Term=Abs t}), stk) =
      let val (thb,stk') = push_lam_in_stk(th,stk) in
      strong (cbv_wk((thb, mk_clos(NEUTR :: Env, t)), stk'))
      end
  | strong ((th, CLOS{Env,Term=TyAbs(tyv,body)}), stk) =
      let val (thb,stk') = push_tylam_in_stk(th,stk) in
      strong (cbv_wk((thb, mk_clos(Env, body)), stk'))
      end
  | strong (clos as (_,CLOS _), stk) = raise DEAD_CODE "strong"
  | strong (hcl as (th,CST {Args,...}), stk) =
      let val (th',stk') =
 	if is_skip hcl then (th,stk)
 	else foldl push_arg_in_stk (th,stk) Args in
      strong_up (th',stk')
      end
  | strong ((th, NEUTR), stk) = strong_up (th,stk)

and strong_up (th, Ztop) = th
  | strong_up (th, Zrand{Rator=(mka,false,(tha,NEUTR)), Ctx}) =
      strong (cbv_wk((mka tha th,NEUTR), Ctx))
  | strong_up (th, Zrand{Rator=(mka,false,clos), Ctx}) =
      raise DEAD_CODE "strong_up"
  | strong_up (th, Zrator{Rand=(mka,clos), Ctx}) =
      strong (cbv_wk(clos, Zrand{Rator=(mka,true,(th,NEUTR)), Ctx=Ctx}))
  | strong_up (th, Zrand{Rator=(mka,true,(tha,_)), Ctx}) =
      strong_up (mka tha th, Ctx)
  | strong_up (th, Zabs{Bvar=mkl, Ctx}) = strong_up (mkl th, Ctx)
  | strong_up (th, Ztyrator{Rand=(mk1,ty), Ctx}) = strong_up (mk1 th, Ctx)
  | strong_up (th, Ztyabs{Bvar=mkl, Ctx}) = strong_up (mkl th, Ctx)
;


(*---------------------------------------------------------------------------
 * [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *---------------------------------------------------------------------------*)

fun CBV_CONV rws = evaluate o strong o cbv_wk o initial_state rws;

(*---------------------------------------------------------------------------
 * WEAK_CBV_CONV is the same as CBV_CONV except that it does not reduce
 * under abstractions, and reduce weakly the arguments of constants.
 * Reduction whenever we reach a state where a strong reduction is needed.
 *---------------------------------------------------------------------------*)

fun WEAK_CBV_CONV rws =
      evaluate
    o (fn ((th,_),stk) => stack_out(th,stk))
    o cbv_wk
    o initial_state rws;

(*---------------------------------------------------------------------------
 * Adding an arbitrary conv
 *---------------------------------------------------------------------------*)

fun extern_of_conv rws conv tm =
  let val thm = conv tm in
  (thm, mk_clos([],from_term(rws,[],rhs(concl thm))))
  end;

fun add_conv (cst,arity,conv) rws =
  add_extern (cst,arity,extern_of_conv rws conv) rws;

fun set_skip compset c opt =
 let val {Name,Thy,...} = dest_thy_const c
 in clauses.set_skip compset (Name,Thy) opt
 end
 handle HOL_ERR _ => raise ERR "set_skip" "";


(*---------------------------------------------------------------------------
       Support for a global compset.
 ---------------------------------------------------------------------------*)

val bool_redns =
 strictify_thm LET_DEF
 :: strictify_thm literal_case_DEF
 :: List.map lazyfy_thm
      [COND_CLAUSES, COND_ID, NOT_CLAUSES, bool_case_DEF,
       AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES];

fun bool_compset() = let
  val base = from_list bool_redns
  val _ = set_skip base boolSyntax.conditional NONE
          (* change last parameter to SOME 1 to stop CBV_CONV looking at
             conditionals' branches before the guard is fully true or false *)
in
  base
end

val the_compset = bool_compset();

fun trace_weak tm =
  let val x = initial_state the_compset tm
  in
    print_trace 0 (wk, x);
    fst (fst (snd (steps 0 (wk, x))))
  end;

fun trace_strong tm =
  let val x = initial_state the_compset tm
      val _ = print_trace 0 (wk, x)
      val (_,y) = steps 0 (wk, x)
  in
    print_trace 0 (wk, y);
    fst (fst (snd (steps_str 0 (wk, y))))
  end;

val add_funs = Lib.C add_thms the_compset;
val add_convs = List.app (Lib.C add_conv the_compset);

val del_consts = List.app (scrub_const the_compset);
val del_funs = Lib.C scrub_thms the_compset;

val EVAL_CONV = CBV_CONV the_compset;
val EVAL_RULE = Conv.CONV_RULE EVAL_CONV;
val EVAL_TAC  = Tactic.CONV_TAC EVAL_CONV;

infix Orelse;
fun (p Orelse q) x = p x orelse q x;

fun OR [] = K false
  | OR [x] = same_const x
  | OR (h::t) = same_const h Orelse OR t;

fun RESTR_EVAL_CONV clist =
  Lib.with_flag (stoppers,SOME (OR clist)) EVAL_CONV;

val RESTR_EVAL_TAC  = Tactic.CONV_TAC o RESTR_EVAL_CONV;
val RESTR_EVAL_RULE = Conv.CONV_RULE o RESTR_EVAL_CONV;

(*---------------------------------------------------------------------------
      Support for persistence of the_compset
 ---------------------------------------------------------------------------*)

fun write_datatype_info tyinfo =
 let open TypeBasePure Drule
     val size_opt =
       case size_of0 tyinfo
        of SOME (_, ORIG def) => SOME def
         | otherwise => NONE
     val boolify_opt =
	       case encode_of0 tyinfo
        of SOME (_, ORIG def) => SOME def
         | otherwise => NONE
     val compset_addns = [size_opt, boolify_opt]
     val simpls = #rewrs (simpls_of tyinfo)
 in
    add_funs (mapfilter Option.valOf compset_addns @ simpls)
 end

(*---------------------------------------------------------------------------*)
(* Usage note: call this before export_theory().                             *)
(*---------------------------------------------------------------------------*)

fun add_persistent_funs [] = ()
  | add_persistent_funs alist =
     let open Portable
         val (names,thms) = unzip alist
     in
       add_funs thms
       ; Theory.adjoin_to_theory
          {sig_ps = NONE,
           struct_ps = SOME(fn ppstrm =>
             (PP.begin_block ppstrm CONSISTENT 0;
              PP.add_string ppstrm "val _ = computeLib.add_funs [";
              PP.begin_block ppstrm INCONSISTENT 0;
              pr_list_to_ppstream ppstrm
                 PP.add_string (C PP.add_string ",")
                 (C PP.add_break (0,0)) names;
              PP.end_block ppstrm;
              PP.add_string ppstrm "];";
              PP.add_break ppstrm (2,0);
              PP.end_block ppstrm))}
     end

(*---------------------------------------------------------------------------*)
(* Once we delete a constant from a compset, we will probably want to make   *)
(* sure that the constant doesn't get re-added when the theory is exported   *)
(*---------------------------------------------------------------------------*)

fun del_persistent_consts [] = ()
  | del_persistent_consts clist =
     let open Portable
         val plist = map (fn c => let val {Name,Thy,Ty} = dest_thy_const c
                                  in (Name,Thy) end) clist
         val plist' = map (Lib.mlquote##Lib.mlquote) plist
         fun prec (s1,s2) = "Term.prim_mk_const{Name = "^s1^", Thy = "^s2^"}"
         val plist'' = map prec plist'
     in
       del_consts clist
       ; Theory.adjoin_to_theory
          {sig_ps = NONE,
           struct_ps = SOME(fn ppstrm =>
             (PP.begin_block ppstrm CONSISTENT 0;
              PP.add_string ppstrm "val _ = computeLib.del_consts [";
              PP.begin_block ppstrm INCONSISTENT 0;
              pr_list_to_ppstream ppstrm
                 PP.add_string (C PP.add_string ",")
                 (C PP.add_break (0,0)) plist'';
              PP.end_block ppstrm;
              PP.add_string ppstrm "];";
              PP.add_break ppstrm (2,0);
              PP.end_block ppstrm))}
     end

(* ----------------------------------------------------------------------
    compset pretty-printer
   ---------------------------------------------------------------------- *)

fun pp_compset pps c = PP.add_string pps "<compset>"

end
