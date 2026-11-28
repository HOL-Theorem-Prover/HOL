(* Executable documentation: all declarations use sealed production types.
   The launcher imports this compiled module ONLY after its absence checks. *)
structure Documentation =
struct
  open HolKernel Parse boolLib testutils
  structure S = simpExtLib
  val ext_pure_ss = S.lift_simpset pureSimps.pure_ss

  (* Ordinary fragments, lifted *)
  val tracked : S.simpset = S.mk_simpset
    (map S.lift_ssfrag
       [pureSimps.PURE_ss,boolSimps.BOOL_ss,boolSimps.NOT_ss])
  fun default_data (ss : S.simpset) : TraverseExt.traverse_data =
    S.traversedata_for_ss ss
  fun configured_data (ss : S.simpset) : TraverseExt.xtraverse_data =
    S.xtraversedata_for_ss ss
  fun add_opaque (ss : S.simpset) (r : Traverse.reducer) : S.simpset =
    S.++ (ss,S.dproc_ss (TraverseExt.lift r))
  fun lift_congruence (frag : congLib.congsetfrag) :
      congExtLib.congsetfrag = congExtLib.lift_fragment frag
  fun congruence (ss : S.simpset) (frag : congLib.congsetfrag) facts =
    congExtLib.CONGRUENCE_EQ_SIMP_CONV
      (congExtLib.mk_congset [lift_congruence frag]) ss facts

  (* A bundle is compiled once; its source handles and attached views use
     the actual installed counters. Inspection is not reconstruction. *)
  fun bind (base : S.simpset) rules = let
    val (base,args) = S.prepare_rewrite_arguments base rules
    val bundle : S.rewrite_bundle = S.prepare_rewrite_bundle base args
    val inventory : (thm * S.rewrite_source list) list =
      S.rewrite_bundle_rules bundle
    val installed : S.simpset = S.install_rewrite_bundle bundle [] base
  in (installed,bundle,inventory) end
  fun attach (ss : S.simpset) (source : S.rewrite_source) view : S.simpset =
    S.++ (ss,S.rewrite_views [(source,view)])

  fun check name ok = (tprint name; if ok then OK () else die name)
  fun converted name cv input output = let
    val th = QCONV (TRY_CONV cv) input
  in check name (null (hyp th) andalso
       aconv (concl th) (boolSyntax.mk_eq (input,output))) end

  fun run () = let
    val _ = converted "documented tracked construction"
      (S.SIMP_CONV tracked []) ``T /\ audit_p`` ``audit_p:bool``
    (* Closed Boolean identities provide different heads, without exporting
       definitions, adding theories or depending on arithmetic catalogs. *)
    val original = SPEC_ALL boolTheory.AND_CLAUSES
    (* Select exactly the first conjunct: T /\ t = t. *)
    val original = CONJUNCT1 original
    val view = List.nth (CONJUNCTS (SPEC_ALL boolTheory.OR_CLAUSES),2)
    val calls = ref 0
    val opaque = Traverse.REDUCER
      {name=SOME "documented ordinary reducer",initial=Fail "private",
       addcontext=fn (context,_) => context,
       apply=fn _ => fn tm =>
         (calls := !calls + 1; Conv.REWR_CONV original tm)}
    val lifted = add_opaque S.empty_ss opaque
    val _ = check "documented one-way reducer lift is inert" (!calls = 0)
    val _ = converted "documented lifted ordinary reducer proof"
      (S.SIMP_CONV lifted []) ``T /\ audit_p`` ``audit_p:bool``
    val _ = check "documented lift invokes original closure" (!calls > 0)
    val public_fragment = congLib.CSFRAG
      {relations=[],rewrs=[],congs=[],dprocs=[]}
    val _ = converted "documented one-way congruence fragment lift proof"
      (congruence tracked public_fragment [])
      ``T /\ audit_p`` ``audit_p:bool``
    val (installed,bundle,inventory) =
      bind ext_pure_ss [BoundedRewrites.Ntimes original 2]
    val source = hd (#2 (hd inventory))
    val _ = check "documented bundle has one installed native source"
      (length inventory = 1 andalso
       length (S.rewrite_source_handles installed) = 1 andalso
       S.same_rewrite_source
         (source,hd (S.rewrite_source_handles installed)))
    val aliased = attach installed source view
    val _ = converted "documented view spends original allowance"
      (S.SIMP_CONV aliased []) ``F \/ audit_p`` ``audit_p:bool``
    val second = S.install_rewrite_bundle bundle [(source,view)]
      ext_pure_ss
    val _ = converted "documented bundle reuse shares remaining allowance"
      (S.SIMP_CONV second []) ``T /\ audit_p`` ``audit_p:bool``
    val _ = converted "documented original remains exhausted"
      (S.SIMP_CONV installed []) ``T /\ audit_p`` ``T /\ audit_p``
    val _ = converted "documented view remains exhausted"
      (S.SIMP_CONV second []) ``F \/ audit_p`` ``F \/ audit_p``
  in () end
end
