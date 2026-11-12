fun mk_abs_eq lhs rhs = let
  val ty = Term.type_of lhs
  val eq = Term.mk_thy_const
    {Thy="min",Name="=",Ty=Type.--> (ty,Type.--> (ty,Type.bool))}
in Term.mk_comb(Term.mk_comb(eq,lhs),rhs) end;

fun mk_abs_fixture () = let
  val x = Term.mk_var("x",Type.bool)
  val x' = Term.mk_var("x'",Type.bool)
  val body = mk_abs_eq x' x
  (* The cosmetic x clashes with the free x; dest_abs opens with x'. *)
  val lam = Term.rename_bvar "x" (Term.mk_abs(x',body))
in (x',lam) end;

val () = load_pft ["PFTReader","PFTReplay"];
val () = if identity_phase = "produce" then let
    val () = Theory.new_theory "pft_mk_abs"
    val (expected_binder,lam) = mk_abs_fixture ()
    val (binder,child,finish) = Thm.Mk_abs (Thm.REFL lam)
    val () = if Term.aconv binder expected_binder then ()
             else raise Fail "unexpected source Mk_abs binder"
    val () = ignore (Theory.save_thm("RESULT",finish child))
    val matching = Term.mk_abs(expected_binder,expected_binder)
    val (_,body,finish) = Thm.Mk_abs (Thm.REFL matching)
    val () = ignore (Theory.save_thm("MATCHING",finish body))
  in Theory.export_theory () end
  else let
    val () = PFTEmit.emit_theory
      {trace=".hol/objs/pft_mk_absTheory.tr.gz",
       output="hol4/pft_mk_abs.pft.bin",ruleset=PFTEmit.HOL4}
    val db = PFTReplay.replay PFTReplay.empty_trDB
      "hol4/pft_mk_abs.pft.bin"
    val (_,lam) = mk_abs_fixture ()
    val expected = mk_abs_eq lam lam
    val th = valOf (PFTReplay.lookup db "pft_mk_abs$RESULT")
    val () = if null (Thm.hyp th) andalso
                Term.aconv (Thm.concl th) expected then ()
             else raise Fail "Mk_abs replay sequent mismatch"
    val nodes = ref PIntMap.empty
    val checked = ref []
    fun skip _ = ()
    fun instruction opcode (reader:PFTReader.stream_reader) = let
      val desc = PFTOpcodes.lookup_desc PFTOpcodes.hol4_descs opcode
      val results = List.map (fn _ => #readVarint reader ())
        (#results desc)
      val args = PFTReader.read_raw_args desc reader
    in List.app (fn id => nodes := PIntMap.add id (#tag desc,args) (!nodes))
         results end
    fun node id = PIntMap.find id (!nodes)
    fun saved (name,id) = let
      open PFTOpcodes
      val valid = case name of
          "pft_mk_abs$RESULT" =>
            (case node id of
               ("TRANS",[VId _,VId abs]) => #1 (node abs) = "ABS_THM"
             | _ => false)
        | "pft_mk_abs$MATCHING" => #1 (node id) = "Mk_abs"
        | _ => true
    in if valid then checked := name :: !checked
       else raise Fail ("wrong Mk_abs instructions at SAVE " ^ name) end
    val _ = PFTReader.read
      {file="hol4/pft_mk_abs.pft.bin",binary=true,
       format_handler={tyvar=skip,tyop=skip,var=skip,const=skip,
         comb=skip,abs=skip,new_const=skip,new_type=skip,axiom=skip,
         save=saved,load=skip,del=skip,del_range=skip},
       ruleset_handler=instruction}
    val () = if List.all (fn name => List.exists (fn s => s = name) (!checked))
                ["pft_mk_abs$RESULT","pft_mk_abs$MATCHING"] then ()
             else raise Fail "missing Mk_abs SAVE"
    val x = Term.mk_var("x'",Type.bool)
    val matching = Term.mk_abs(x,x)
    val th = valOf (PFTReplay.lookup db "pft_mk_abs$MATCHING")
    val () = if null (Thm.hyp th) andalso Term.aconv (Thm.concl th)
                (mk_abs_eq matching matching) then ()
             else raise Fail "matching Mk_abs replay sequent mismatch"
  in print "MK_ABS_HOL_EXACT_PASS\n" end;
