

               |> addrule fUNION_UNION
               |> addrule fIN_IN
               |> addrule fINSERT_INSERT
               |> addrule fupdate_correct
               |> addrule fEMPTY_EMPTY
               |> addsafe (UNDISCH total_FSET)
               |> addsafe (UNDISCH left_unique_FSET)
               |> addsafe (UNDISCH right_unique_FSET)
               |> addsafe (UNDISCH_ALL
                             (REWRITE_RULE [GSYM AND_IMP_INTRO] bi_unique_FSET))
               |> addbad “bitotal (FSET AB)”
               |> addbad “surj (FSET AB)”
               |> add_domrng RRANGE_FSET_EQ
               |> add_domrng RDOM_FSET_EQ

val notsing_empty = transfer_thm 4 false ruledb NOT_SING_EMPTY
val funion_comm1 = transfer_thm 4 false ruledb UNION_COMM
val funion_comm2 =
    transfer_tm 4 true ruledb “!f1 f2. fUNION f1 f2 = fUNION f2 f1”

(*
val IN_INTER_eq = let
  val ct = concl IN_INTER
  val th0 = prove_relation_thm false ct (build_skeleton ct)
                               |> eliminate_booleans_and_equalities false
in
  seqrpt (resolve_relhyps false ruledb) th0 ~>
  seqrptUntil (List.all (is_var o rand) o hyp)
              (check{cleftp=false,forceprogress=true} ruledb) |> seq.hd
end *)

val induct =
    transfer_tm 4 true ruledb
                “!P. P FEMPTY /\ (!s e. ~fIN e s ==> P (fINSERT e s)) ==>
                     !s. P s”

(* doesn't get as far as you might like because you have no way of knowing
   that the set asserted to exist in the second disjunct should be finite *)
val cases1 = let
  val ct = concl SET_CASES
in
  ct |> build_skeleton |> prove_relation_thm false ct
     |> eliminate_booleans_and_equalities false
     |> seqrpt (resolve_relhyps false ruledb)
     |> seq.hd
end

val cases2 =
    transfer_tm 4 true ruledb
                “!fs. fs = FEMPTY \/ ?e fs0. ~(fIN e fs0) /\ fs = fINSERT e fs0”

Definition o2n_def:
  o2n s = FUN_FMAP (K ()) s
End

Definition n2o_def:
  n2o fm = FDOM fm
End

Theorem tydef:
  (!s. FINITE s <=> (n2o (o2n s) = s)) /\
  (!fm. o2n (n2o fm) = fm)
Proof
  simp[n2o_def, o2n_def] >> conj_tac
  >- (qx_gen_tac ‘s’ >> Cases_on ‘FINITE s’ >> simp[] >> strip_tac >>
      metis_tac[finite_mapTheory.FDOM_FINITE]) >>
  simp[finite_mapTheory.fmap_EXT]
QED

Theorem o2n_thm:
  FSET $= b a ==> o2n a = b
Proof
  simp[FSET_def, o2n_def, finite_mapTheory.fmap_EXT] >> strip_tac >>
  rename [‘fIN _ fm <=> _ IN s’] >>
  ‘FINITE s’ suffices_by simp[pred_setTheory.EXTENSION] >>
  ‘s = FDOM fm’ suffices_by simp[] >> simp[pred_setTheory.EXTENSION]
QED

Theorem n2o_thm:
  FSET $= fm (n2o fm)
Proof
  simp[FSET_def, n2o_def]
QED

Theorem FSETR_eq:
  FSET $= O inv (FSET $=) = (\s1 s2. FINITE s1 /\ s1 = s2)
Proof
  simp[Ntimes FUN_EQ_THM 2, FSET_def, relationTheory.O_DEF,
       relationTheory.inv_DEF] >> rw[Once EQ_IMP_THM]
  >- (rename [‘FINITE s’, ‘fIN _ fm <=> _ IN s’] >>
      ‘s = FDOM fm’ suffices_by simp[] >>
      simp[pred_setTheory.EXTENSION] >> metis_tac[])
  >- (simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  rename [‘FINITE s’]>> qexists_tac ‘FUN_FMAP (K ()) s’ >>
  simp[]
QED


Definition fmi_def:
  fmi fs1 fs2 = o2n (n2o fs1 INTER n2o fs2)
End

Theorem fmi_correct:
  (FSET $= ===> FSET $= ===> FSET $=) fmi $INTER
Proof
  simp[FUN_REL_def, fmi_def]
