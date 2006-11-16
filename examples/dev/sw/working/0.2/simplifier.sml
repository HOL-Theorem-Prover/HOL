open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory finite_mapTheory simplifierTheory;

(*------------------------------------------------------------------------------------------------------*)
(* Additional theorems for finite maps                                                                  *)
(*------------------------------------------------------------------------------------------------------*)


val fupdate_normalizer =
 let val thm = SPEC_ALL FUPDATE_LT_COMMUTES
     val pat = lhs(snd(dest_imp(concl thm)))
 in
   {name = "Finite map normalization",
    trace = 2,
    key = SOME([],pat),
    conv = let fun reducer tm =
                 let val (theta,ty_theta) = match_term pat tm
                     val thm' = INST theta (INST_TYPE ty_theta thm)
                     val constraint = fst(dest_imp(concl thm'))
                     val cthm = EQT_ELIM(reduceLib.REDUCE_CONV constraint)
                 in MP thm' cthm
                 end
           in
               K (K reducer)
           end}
 end;

val finmap_conv_frag =
 simpLib.SSFRAG
     {convs = [fupdate_normalizer],
      rewrs = [], ac=[],filter=NONE,dprocs=[],congs=[]};

val finmap_ss = bossLib.std_ss ++ finmap_conv_frag
                               ++ rewrites [FUPDATE_EQ, FAPPLY_FUPDATE_THM];

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

