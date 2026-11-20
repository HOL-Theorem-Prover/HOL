(* Independent standard recipes: compare ordinary and tracked public APIs.
   All proof comparisons include the entire hypothesis set. *)
structure selftest =
struct

open HolKernel Parse boolLib boolSyntax testutils
structure O = simpLib
structure S = simpExtLib
val ext_ABBREV_ss = simpExtLib.lift_ssfrag boolSimps.ABBREV_ss
val ext_BOOL_ss = simpExtLib.lift_ssfrag boolSimps.BOOL_ss
val ext_COMBIN_ss = simpExtLib.lift_ssfrag combinSimps.COMBIN_ss
val ext_COND_elim_ss = simpExtLib.lift_ssfrag boolSimps.COND_elim_ss
val ext_CONG_ss = simpExtLib.lift_ssfrag boolSimps.CONG_ss
val ext_CONJ_ss = simpExtLib.lift_ssfrag boolSimps.CONJ_ss
val ext_DISJ_ss = simpExtLib.lift_ssfrag boolSimps.DISJ_ss
val ext_DNF_ss = simpExtLib.lift_ssfrag boolSimps.DNF_ss
val ext_EQUIV_EXTRACT_ss = simpExtLib.lift_ssfrag boolSimps.EQUIV_EXTRACT_ss
val ext_ETA_ss = simpExtLib.lift_ssfrag boolSimps.ETA_ss
val ext_HIDE_ss = simpExtLib.lift_ssfrag boolSimps.HIDE_ss
val ext_LABEL_CONG_ss = simpExtLib.lift_ssfrag boolSimps.LABEL_CONG_ss
val ext_LET_ss = simpExtLib.lift_ssfrag boolSimps.LET_ss
val ext_LIFT_COND_ss = simpExtLib.lift_ssfrag boolSimps.LIFT_COND_ss
val ext_NORMEQ_ss = simpExtLib.lift_ssfrag boolSimps.NORMEQ_ss
val ext_NOT_ss = simpExtLib.lift_ssfrag boolSimps.NOT_ss
val ext_PURE_ss = simpExtLib.lift_ssfrag pureSimps.PURE_ss
val ext_UNWIND_ss = simpExtLib.lift_ssfrag boolSimps.UNWIND_ss
val ext_bool_ss = simpExtLib.lift_simpset boolSimps.bool_ss
val ext_literal_case_ss = simpExtLib.lift_ssfrag boolSimps.literal_case_ss
val ext_pure_ss = simpExtLib.lift_simpset pureSimps.pure_ss
structure E = TraverseExt
val checks = ref 0
fun check label ok =
  (checks := !checks + 1; tprint label;
   if ok then OK () else die label)
fun same (a,b) = aconv (concl a) (concl b) andalso
  HOLset.equal (hypset a,hypset b)
fun thms xs ys = ListPair.allEq same (xs,ys)
fun terms xs ys = ListPair.allEq (uncurry aconv) (xs,ys)
fun total cv = QCONV (TRY_CONV cv)
fun compare label ordinary tracked rules tm =
  check label (same (total (O.SIMP_CONV ordinary rules) tm,
                    total (S.SIMP_CONV tracked rules) tm))
fun expected label ss tm output = let
  val th = total (S.SIMP_CONV ss []) tm
in check label (null (hyp th) andalso aconv (lhs (concl th)) tm andalso
                aconv (rhs (concl th)) output) end
fun fragment label ordinary tracked =
  check (label ^ ": fragment name and ordered rewrite ingredients")
    (O.frag_name ordinary = S.frag_name tracked andalso
     thms (O.frag_rewrites ordinary) (S.frag_rewrites tracked))
fun fails label f = check label
  (case Exn.capture f () of Exn.Exn (HOL_ERR _) => true | _ => false)

(* The whole exported boolean catalog, including intentionally opt-in items. *)
val catalog =
  [("PURE",pureSimps.PURE_ss,ext_PURE_ss),
   ("BOOL",boolSimps.BOOL_ss,ext_BOOL_ss),
   ("CONG",boolSimps.CONG_ss,ext_CONG_ss),
   ("ABBREV",boolSimps.ABBREV_ss,ext_ABBREV_ss),
   ("CONJ",boolSimps.CONJ_ss,ext_CONJ_ss),
   ("DISJ",boolSimps.DISJ_ss,ext_DISJ_ss),
   ("NOT",boolSimps.NOT_ss,ext_NOT_ss),
   ("COND_elim",boolSimps.COND_elim_ss,ext_COND_elim_ss),
   ("LIFT_COND",boolSimps.LIFT_COND_ss,ext_LIFT_COND_ss),
   ("UNWIND",boolSimps.UNWIND_ss,ext_UNWIND_ss),
   ("ETA",boolSimps.ETA_ss,ext_ETA_ss),
   ("LET",boolSimps.LET_ss,ext_LET_ss),
   ("literal_case",boolSimps.literal_case_ss,
      ext_literal_case_ss),
   ("DNF",boolSimps.DNF_ss,ext_DNF_ss),
   ("EQUIV_EXTRACT",boolSimps.EQUIV_EXTRACT_ss,
      ext_EQUIV_EXTRACT_ss),
   ("NORMEQ",boolSimps.NORMEQ_ss,ext_NORMEQ_ss),
   ("LABEL_CONG",boolSimps.LABEL_CONG_ss,ext_LABEL_CONG_ss),
   ("HIDE",boolSimps.HIDE_ss,ext_HIDE_ss)]
val _ = List.app (fn (n,oFrag,tFrag) => fragment n oFrag tFrag) catalog
val _ = check "bool recipe order matches ordinary and stays explicit"
  (map S.frag_name (S.ssfrags_of ext_bool_ss) =
   map O.frag_name (O.ssfrags_of boolSimps.bool_ss) andalso
   map S.frag_name (List.rev (S.ssfrags_of ext_bool_ss)) =
   map SOME ["PURE","BOOL","NOT","CONG","UNWIND"])
val _ = check "PURE installs no rewrite sources"
  (null (S.rewrite_source_handles ext_pure_ss))
val boolInputs =
  [``(\x:bool. x /\ T) p``,
   ``if p then (f:bool -> bool) p else g p``,
   ``p ==> (p /\ q)``, ``?x:bool. (x = p) /\ Q x``,
   ``~(p \/ q)``, ``\x:bool. f x:bool``]
val _ = List.app (compare "bool ordinary/tracked theorem"
  boolSimps.bool_ss ext_bool_ss []) boolInputs
val _ = expected "BOOL beta and clause result" ext_bool_ss
  ``(\x:bool. x /\ T) p`` ``p:bool``
val _ = expected "BOOL congruence carries branch context"
  ext_bool_ss ``if p then (f:bool -> bool) p else g p``
  ``if p then (f:bool -> bool) T else g F``
val _ = expected "ETA is not in bool_ss" ext_bool_ss
  ``\x:bool. f x:bool`` ``\x:bool. f x:bool``
val _ = expected "PURE has no implicit beta conversion"
  ext_pure_ss ``(\x:bool. x) p`` ``(\x:bool. x) p``
val _ = let
  val conditional = ASSUME ``p ==> ((pure_f:bool -> bool) x = y)``
  val premise = ASSUME ``p:bool``
  val tm = ``(pure_f:bool -> bool) x``
  val rules = [conditional,premise]
  val _ = compare "PURE conditional rewrite maker agrees"
    pureSimps.pure_ss ext_pure_ss rules tm
in check "PURE conditional maker retains complete proof"
     (same (total (S.SIMP_CONV ext_pure_ss rules) tm,
            MP conditional premise)) end
val examples =
  [("PURE", ``(\x:bool. x) p``),
   ("BOOL", ``(\x:bool. x /\ T) p``),
   ("CONG", ``p ==> (p /\ q)``),
   ("ABBREV", ``Abbrev (x = (p /\ T))``),
   ("CONJ", ``p /\ ((f:bool -> bool) p)``),
   ("DISJ", ``p \/ ((f:bool -> bool) p)``),
   ("NOT", ``~(p /\ q)``),
   ("COND_elim", ``(f:bool -> bool) (if p then q else r)``),
   ("LIFT_COND", ``(f:bool -> bool) (if p then q else r)``),
   ("UNWIND", ``?x:bool. (x = p) /\ Q x``),
   ("ETA", ``(f:(bool -> bool) -> bool) (\x. g x)``),
   ("LET", ``let x = (p /\ T) in (f:bool -> bool) x``),
   ("literal_case", ``literal_case (\x:bool. f x:bool) (p /\ T)``),
   ("DNF", ``p /\ (q \/ r)``),
   ("EQUIV_EXTRACT", ``(p /\ q) <=> (p /\ r)``),
   ("NORMEQ", ``T = p``),
   ("LABEL_CONG", ``lab :- (p /\ T)``),
   ("HIDE", ``hide (p /\ T)``)]
val _ = List.app (fn (name,tm) => let
  val (_,ofrag,tfrag) = valOf (List.find (fn (n,_,_) => n=name) catalog)
in compare (name ^ ": installed recipe theorem")
     (O.++ (pureSimps.pure_ss,ofrag))
     (S.++ (ext_pure_ss,tfrag)) [] tm end) examples
val _ = check "SimpLHS/SimpRHS theorem markers agree"
  (same (boolSimps.SimpLHS,boolSimps.SimpLHS) andalso
   same (boolSimps.SimpRHS,boolSimps.SimpRHS))
val _ = check "SimpL/SimpR theorem constructors agree"
  (same (boolSimps.SimpL conjunction,boolSimps.SimpL conjunction) andalso
   same (boolSimps.SimpR disjunction,boolSimps.SimpR disjunction))

(* COMBIN is constructed from named theorem inputs, not an ordinary fragment. *)
val _ = fragment "COMBIN" combinSimps.COMBIN_ss ext_COMBIN_ss
val combinO = O.++ (boolSimps.bool_ss,combinSimps.COMBIN_ss)
val combinT = S.++ (ext_bool_ss,ext_COMBIN_ss)
val combinNames =
  ["I_THM","I_o_ID","K_THM","S_THM","o_ASSOC'","o_THM","W_THM","C_THM",
   "K_o_THM","UPDATE_EQ","UPDATE_APPLY_ID_RWT","UPDATE_APPLY1"]
val _ = check "COMBIN exact immutable theorem order"
  (thms (S.frag_rewrites ext_COMBIN_ss)
    (map (DB.fetch "combin") combinNames))
val _ = List.app (fn tm => compare "COMBIN ordinary/tracked theorem"
  combinO combinT [] tm)
  [``I (p:bool)``, ``K (p:bool) (q:bool)``,
   ``S (f:bool -> bool -> bool) g x``,
   ``((f:bool -> bool) o g) x``, ``W (f:bool -> bool -> bool) x``,
   ``C (f:bool -> bool -> bool) x y``,
   ``((x =+ (y:bool)) (f:bool -> bool)) x``]
val _ = expected "COMBIN I result" combinT ``I (p:bool)`` ``p:bool``
val _ = expected "COMBIN K result" combinT ``K (p:bool) (q:bool)`` ``p:bool``
val _ = check "COMBIN native sources retain theory-qualified names"
  (List.all (fn source => case #1 (S.source_rewrite source) of
      SOME {Thy,Name} => Thy="combin" andalso
        List.exists (fn n => String.isPrefix (n ^ ".") Name) combinNames
    | NONE => false)
    (S.rewrite_source_handles
      (S.++ (ext_pure_ss,ext_COMBIN_ss))))

(* TypeBase direct construction and lookup share data, not compiled sources.
   Stored names and fallback names both remain available in tracked sources. *)
val boolInfo = valOf (TypeBase.fetch bool)
val _ = fragment "TypeBase bool direct" (O.tyi_to_ssdata boolInfo)
  (S.tyi_to_ssdata boolInfo)
val _ = fragment "TypeBase bool lookup" (O.type_ssfrag bool)
  (S.type_ssfrag bool)
val _ = check "TypeBase direct/lookup ordered contents agree"
  (thms (S.frag_rewrites (S.type_ssfrag bool))
        (S.frag_rewrites (S.tyi_to_ssdata boolInfo)))
val _ = compare "TypeBase bool ordinary/tracked theorem"
  (O.++ (pureSimps.pure_ss,O.type_ssfrag bool))
  (S.++ (ext_pure_ss,S.type_ssfrag bool)) []
  ``bool_CASE T (p:bool) q``
val _ = fails "tracked TypeBase missing type rejected"
  (fn () => S.type_ssfrag (mk_vartype "'standard_missing"))
val _ = fails "ordinary TypeBase missing type rejected"
  (fn () => O.type_ssfrag (mk_vartype "'standard_missing"))
val _ = let
  val rule = ASSUME ``(type_recipe_f:bool -> bool) x = y``
  val info = TypeBasePure.put_simpls
    {rewrs=[boolTheory.NOT_CLAUSES,rule],convs=[]} boolInfo
  val ofrag = O.tyi_to_ssdata info
  val tfrag = S.tyi_to_ssdata info
  val _ = fragment "TypeBase mixed names" ofrag tfrag
  val _ = check "TypeBase reverses original rewrite order"
    (thms (S.frag_rewrites tfrag) [rule,boolTheory.NOT_CLAUSES])
  val ss = S.++ (S.++ (ext_pure_ss,
    S.named_rewrites "type-removable" []),tfrag)
  val hs = S.rewrite_source_handles ss
  val sources = map S.source_rewrite hs
  val _ = check "TypeBase fallback name retained in compiled source"
    (List.exists (fn (name,th) =>
      name = SOME {Thy="",Name="min$bool simpl. 2.1"} andalso same (th,rule))
      sources)
  val _ = check "TypeBase stored theorem identity retained"
    (List.exists (fn (name,_) => case name of
      SOME {Thy,Name} => Thy="bool" andalso
        String.isPrefix "NOT_CLAUSES." Name | NONE => false) sources)
  val replay = S.remove_ssfrags_preserving_controls ["type-removable"] ss
  val _ = check "TypeBase native identities survive history replay"
    (ListPair.allEq S.same_rewrite_source
       (hs,S.rewrite_source_handles replay))
  val independent = S.++ (ext_pure_ss,S.tyi_to_ssdata info)
  val _ = check "TypeBase fresh construction has independent occurrences"
    (not (S.same_rewrite_source
      (hd hs,hd (S.rewrite_source_handles independent))))
in compare "TypeBase mixed rule complete theorem"
     (O.++ (pureSimps.pure_ss,ofrag)) ss [] (lhs (concl rule)) end

(* TypeBase conversions preserve their original closures and simp callback.
   They remain conversions, never invented native rewrite-source identities. *)
val _ = let
  val ordinaryCalls = ref 0
  val trackedCalls = ref 0
  val input = ``(\x:bool. x) type_conversion_arg``
  fun conversion calls =
    {name="standard TypeBase conversion",key=SOME ([],input),trace=2,
     conv=fn solve => fn stack => fn tm =>
       if aconv tm input then
         (calls := !calls + 1;
          check "TypeBase conversion retains simp callback and stack"
            (null stack andalso same (total (solve stack) T,REFL T));
          BETA_CONV tm)
       else NO_CONV tm}
  fun info calls = TypeBasePure.put_simpls
    {rewrs=[],convs=[conversion calls]} boolInfo
  val ofrag = O.tyi_to_ssdata (info ordinaryCalls)
  val tfrag = S.tyi_to_ssdata (info trackedCalls)
  val os = O.++ (pureSimps.pure_ss,ofrag)
  val ts = S.++ (ext_pure_ss,tfrag)
  val _ = check "TypeBase conversion construction/install is inert"
    (!ordinaryCalls = 0 andalso !trackedCalls = 0 andalso
     null (S.rewrite_source_handles ts))
  val ordinary = total (O.SIMP_CONV os []) input
  val tracked = total (S.SIMP_CONV ts []) input
  val _ = check "TypeBase conversion ordinary/tracked complete theorem"
    (same (ordinary,tracked) andalso same (tracked,BETA_CONV input))
in check "TypeBase conversion uses each original closure exactly once"
     (!ordinaryCalls = 1 andalso !trackedCalls = 1) end

(* Replay retains exclusions, traversal limits and historical rewrite makers.
   Reconstructing only ssfrags_of is deliberately not used by these clients. *)
val _ = let
  val a = ASSUME ``(recipe_f:bool -> bool) x = y``
  val b = ASSUME ``(recipe_g:bool -> bool) x = z``
  val callsO = ref ([] : string list)
  val callsT = ref ([] : string list)
  fun maker calls label rw = (calls := !calls @ [label]; [rw])
  fun ofilter label = O.SSFRAG {name=SOME label,
    filter=SOME (maker callsO label),rewrs=[],convs=[],congs=[],ac=[],
    dprocs=[]}
  fun tfilter label = S.SSFRAG {name=SOME label,
    filter=SOME (maker callsT label),rewrs=[],convs=[],congs=[],ac=[],
    dprocs=[]}
  val names = [({Thy="bool",Name="recipe_a"},a),
               ({Thy="bool",Name="recipe_b"},b)]
  val os = O.++ (O.++ (O.++ (O.++ (O.empty_ss,ofilter "maker1"),
      O.named_rewrites_with_names "rules" names),ofilter "maker2"),
      O.named_rewrites "drop" [])
  val ts = S.++ (S.++ (S.++ (S.++ (S.empty_ss,tfilter "maker1"),
      S.named_rewrites_with_names "rules" names),tfilter "maker2"),
      S.named_rewrites "drop" [])
  val os = O.-* (O.limit 0 os,["recipe_b"])
  val ts = S.-* (S.limit 0 ts,["recipe_b"])
  val _ = callsO := []
  val _ = callsT := []
  val oreplay = O.remove_ssfrags ["drop"] os
  val treplay = S.remove_ssfrags ["drop"] ts
  val _ = check "replay maker order/count matches ordinary history"
    (!callsO = ["maker1","maker1"] andalso !callsT = !callsO)
  val _ = check "replay preserves explicit traversal limit"
    (#limit (O.traversedata_for_ss oreplay) = SOME 0 andalso
     #limit (S.traversedata_for_ss treplay) = SOME 0)
  val _ = compare "limited replay ordinary/tracked proof"
    oreplay treplay [] (lhs (concl a))
  val _ = check "zero limit prevents native rewrite"
    (same (total (S.SIMP_CONV treplay []) (lhs (concl a)),
           REFL (lhs (concl a))))
  val ou = O.unlimit oreplay
  val tu = S.unlimit treplay
  val _ = compare "unlimited replay ordinary/tracked proof"
    ou tu [] (lhs (concl a))
  val _ = check "unlimited replay retains original complete proof"
    (same (total (S.SIMP_CONV tu []) (lhs (concl a)),a))
  val _ = check "literal exclusion persists across replay"
    (same (total (S.SIMP_CONV tu []) (lhs (concl b)),
           REFL (lhs (concl b))))
  val _ = compare "excluded rule proof matches ordinary after replay"
    ou tu [] (lhs (concl b))
  val laterO = O.++ (ou,O.rewrites [a])
  val laterT = S.++ (tu,S.rewrites [a])
  val _ = check "future additions see surviving historical maker chain"
    (!callsO = ["maker1","maker1","maker1","maker2"] andalso
     !callsT = !callsO)
  val excludedO = O.exclude_ssfrags ["rules"] laterO
  val excludedT = S.exclude_ssfrags ["rules"] laterT
  val _ = check "fragment exclusion prohibition survives replay/addition"
    (O.ssfrag_names_of
      (O.++ (excludedO,O.named_rewrites "rules" [b])) =
     S.ssfrag_names_of
      (S.++ (excludedT,S.named_rewrites "rules" [b])) andalso
     not (List.exists (fn n => n="rules")
       (S.ssfrag_names_of
         (S.++ (excludedT,S.named_rewrites "rules" [b])))))
in compare "future addition complete proof matches ordinary"
     laterO laterT [] (lhs (concl a)) end

(* Ordinary opaque reducers enter only through explicit lift. Verify private
   exception payloads, collector order and exact callback continuations. *)
val _ = let
  exception Private of unit ref * thm list
  val token = ref ()
  val collections = ref 0
  val applications = ref 0
  val solverCalls = ref 0
  val convCalls = ref 0
  val fact = ASSUME ``recipe_context:bool``
  val atom = ``recipe_atom:bool``
  val stack = [``recipe_stack:bool``]
  val rule = ASSUME ``recipe_atom = recipe_output``
  fun collect (Private (r,old),ths) =
        (check "lift collector preserves private payload"
           (Portable.pointer_eq (r,token));
         collections := !collections + 1; Private (r,old @ ths))
    | collect _ = raise Fail "lost private collector payload"
  val ordinary = Traverse.REDUCER
    {name=SOME "standard recipe opaque",initial=Private (token,[]),
     addcontext=collect,
     apply=fn {context,solver,conv,stack=actual,relation=(rel,refl)} => fn tm =>
       (applications := !applications + 1;
        check "lift apply preserves payload and collected facts"
          (case context of Private (r,ths) =>
             Portable.pointer_eq (r,token) andalso thms ths [fact]
           | _ => false);
        check "lift apply preserves stack/relation/reflexivity"
          (terms actual stack andalso aconv rel equality andalso
           same (refl tm,REFL tm));
        check "lift forwards solver continuation arguments/result"
          (same (solver stack (concl fact),fact));
        check "lift forwards conversion continuation arguments/result"
          (same (conv stack atom,rule));
        rule)}
  val lifted = E.lift ordinary
  val ss = S.++ (S.empty_ss,S.dproc_ss lifted)
  val _ = ignore (S.traversedata_for_ss ss)
  val _ = ignore (S.xtraversedata_for_ss ss)
  val _ = check "lift/install/projections invoke no opaque callbacks"
    (!collections = 0 andalso !applications = 0 andalso
     null (S.rewrite_source_handles ss))
  val withContext = E.addctxt [fact] lifted
  val _ = check "explicit context addition collects exactly once"
    (!collections = 1 andalso !applications = 0)
  val rd = E.reducer_data withContext
  val rc = E.reducer_config_data withContext
  fun solver actual tm =
    (solverCalls := !solverCalls + 1;
     if terms actual stack andalso aconv tm (concl fact) then fact
     else raise Fail "solver arguments changed")
  fun conv actual tm =
    (convCalls := !convCalls + 1;
     if terms actual stack andalso aconv tm atom then rule
     else raise Fail "conversion arguments changed")
  val expected = #apply (Traverse.dest_reducer
    (Traverse.addctxt [fact] ordinary))
    {context=Private (token,[fact]),solver=solver,conv=conv,
     stack=stack,relation=(equality,REFL)} atom
  val got = #apply rd
    {context= #initial rd,solver=solver,conv=conv,stack=stack,
     relation=(equality,REFL),cond_depth=7,term_ord=fn _ => LESS} atom
  val configured = #apply rc
    {context= #initial rc,solver=solver,conv=conv,stack=stack,
     relation=(equality,REFL),cond_depth=NONE,term_ord=fn _ => GREATER} atom
in check "both lifted views match ordinary complete theorem and callbacks"
     (same (got,expected) andalso same (configured,expected) andalso
      !collections = 2 andalso !applications = 3 andalso
      !solverCalls = 3 andalso !convCalls = 3) end

(* The opaque ordinary reducer also runs through the actual engines. *)
val _ = let
  exception Facts of unit ref * thm list
  val token = ref ()
  val input = ``recipe_engine_input:bool``
  val rule = ASSUME ``recipe_engine_input = recipe_engine_output``
  val fact = ASSUME ``recipe_engine_context:bool``
  val callsO = ref 0
  val callsT = ref 0
  fun reducer calls = Traverse.REDUCER
    {name=SOME "engine opaque",initial=Facts (token,[]),
     addcontext=fn (Facts (r,old),ths) => Facts (r,old @ ths)
       | _ => raise Fail "engine collector payload changed",
     apply=fn {context,stack,relation=(rel,refl),...} => fn tm =>
       if aconv tm input then
         (calls := !calls + 1;
          check "engine lift preserves context, stack and relation"
            (null stack andalso aconv rel equality andalso
             same (refl tm,REFL tm) andalso
             (case context of Facts (r,ths) =>
                Portable.pointer_eq (r,token) andalso thms ths [fact]
              | _ => false));
          rule)
       else NO_CONV tm}
  val os = O.++ (O.empty_ss,O.dproc_ss (reducer callsO))
  val ts = S.++ (S.empty_ss,S.dproc_ss (E.lift (reducer callsT)))
  val ordinary = Traverse.TRAVERSE (O.traversedata_for_ss os) [fact]
  val tracked = E.TRAVERSE (S.traversedata_for_ss ts) [fact]
  val _ = check "engine lifted reducer matches ordinary complete theorem"
    (same (total ordinary input,total tracked input))
  val _ = check "engine lifted result retains rule hypotheses"
    (same (total tracked input,rule))
  val configured = E.XTRAVERSE (S.xtraversedata_for_ss ts) [fact]
  val _ = check "configured engine lifted result retains complete theorem"
    (same (total configured input,rule))
in check "engine ordinary and lifted callback counts are exact"
     (!callsO = 1 andalso !callsT = 3) end

val _ = print ("STANDARD_RECIPE_CHECKS=" ^ Int.toString (!checks) ^ "\n")
val _ = OS.Process.exit OS.Process.success

end (* struct *)
