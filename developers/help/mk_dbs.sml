(*---------------------------------------------------------------------------*
 * This file generates a database containing the HOL ".doc" files, and also  *
 * a database that indexes everything that is accessible in the system.      *
 *---------------------------------------------------------------------------*)

(* app load ["Mosml","Database","Parsspec"]; *)

fun mkentry s = let
  val content = let
    val (pfx,sfx) = Substring.position "-lc.adoc" (Substring.all s)
  in
    if Substring.size sfx = 0 orelse Substring.size sfx <> 8 then
      String.substring(s,0,size s - 5)
    else
      String.substring(s,0,size s - 8)
  end
in
  {comp=Database.Term(content, SOME"HOL"), file=s, line=0}
end

local fun is_adocfile s = 
         size s>5 andalso String.extract(s, size s - 5, NONE) = ".adoc"
in
fun docdir_to_entries path (endpath, entries) =
  let val dir = Path.concat (path, endpath)
      val L0 = Mosml.listDir dir
      val L1 = List.filter is_adocfile L0
  in
    List.foldl (fn (e,l) => (mkentry e::l)) entries L1
  end
end;

val docdirs = let
  val instr = TextIO.openIn "../../tools/documentation-directories"
    handle _ => (print "Couldn't open documentation directories file";
                 raise Fail "File not found")
  val wholefile = TextIO.inputAll instr
  val _ = TextIO.closeIn instr
in
  String.tokens Char.isSpace wholefile
end


(*---------------------------------------------------------------------------
 * The database of all hol ".doc" files.
 *---------------------------------------------------------------------------*)
fun buildDb holpath = let
  val doc_indices = List.foldl (docdir_to_entries holpath) [] docdirs
  fun foldfn (arg as (s, indices)) =
    Parsspec.processfile [] (Path.concat(holpath, "sigobj")) arg
    handle _ =>
      (print ("\n  *** Exception raised attempting to process file "^s^
              " ***\n");
       indices)
  val all_indices =
    List.foldr foldfn doc_indices
    ["Const_def.sig", "Parse.sig", "Theory.sig", "Const_spec.sig",
     "Parse_support.sig", "Count.sig", "Hol_pp.sig", 
     "Thm.sig", "Dsyntax.sig", "Preterm.sig", "Absyn.sig", "Exception.sig",
     "Type.sig", "Lexis.sig", "Type_def.sig", "Lib.sig",
     "Globals.sig", "Net.sig", "Term.sig", "AncestorDB.sig", "DB.sig",

     (* basicHol90Lib *)
     "Prim_rec.sig", "Tactical.sig", "Conv.sig", "Tactic.sig",
     "Drule.sig", "Resolve.sig", "Thm_cont.sig", "Rewrite.sig", 
     "Type_def_support.sig", "Rsyntax.sig", "Psyntax.sig",
     "TypeBase.sig", "DefnBase.sig",

     (* jrh ind_defs *)
     "IndDefLib.sig",

     (* Integer *)
     "integerTheory.sig", "Cooper.sig", "intLib.sig",

     (* arithLib *)
     "Arith.sig","Norm_arith.sig","Sol_ranges.sig","Term_coeffs.sig",
     "Arith_cons.sig","Norm_bool.sig","Solve.sig","Theorems.sig",
     "Exists_arith.sig","Norm_ineqs.sig","Solve_ineqs.sig",
     "Thm_convs.sig", "Gen_arith.sig","Prenex.sig","Streams.sig",
     "arithLib.sig","Instance.sig","Qconv.sig","Sub_and_cond.sig",
     "Int_extra.sig","Rationals.sig","Sup_Inf.sig",

     (* min and bool theories *)
     "boolTheory.sig","minTheory.sig",

     (* combin theory *)
     "combinTheory.sig",

     (* datatype *)
     "Datatype.sig",
     "Define_type.sig","rec_typeTheory.sig",
     "RecordType.sig", "EquivType.sig",

     (* decisionLib *)
     "DecisionArithConvs.sig","NumArith.sig","NumType.sig",
     "DecisionConv.sig","NumArithCons.sig","Taut.sig",
     "DecisionTheorems.sig","NumHOLType.sig",
     "LazyThm.sig","NumInequalityCoeffs.sig",

     (* goalstackLib *)
     "goalstackLib.sig",

     (* hol_match *)
     "Ho_match.sig","Ho_resolve.sig", "Ho_net.sig","Ho_rewrite.sig",

     (* hol88 *)
     "hol88Lib.sig",

     (* hol90 *)
     "HOLTheory.sig",

     (* tfm ind_def *)
     "ind_defLib.sig",

     (* list *)
     "ListConv1.sig","rich_listTheory.sig","listTheory.sig",
     "ListConv2.sig","listLib.sig","operatorTheory.sig",

     (* lazy list *)
     "llistTheory.sig",

     (* lite *)
     "liteLib.sig",

     (* meson *)
     "Canon_Port.sig","jrhTactics.sig","mesonLib.sig",

     (* mutrec *)
     "ConsThms.sig","MutRecMask.sig","TypeInfo.sig",
     "MutRecDef.sig","Recftn.sig","mutrecLib.sig",

     (* nested_rec *)
     "DefType.sig","GenFuns.sig","TypeOpTable.sig",
     "DefTypeInfo.sig","NestedRecMask.sig","TypeTable.sig",
     "ExistsFuns.sig","StringTable.sig","nested_recLib.sig",

     (* num *)
     "numTheory.sig", "prim_recTheory.sig", "arithmeticTheory.sig",
     "numeralTheory.sig", "numLib.sig",

     (* one *)
     "oneTheory.sig",

     (* option *)
     "optionLib.sig","optionTheory.sig",

     (* pair *)
     "Let_conv.sig","Pair_conv.sig","pairLib.sig",
     "Pair_basic.sig","Pair_exists.sig","pairTheory.sig",
     "Pair_both1.sig","Pair_forall.sig",
     "Pair_both2.sig","Pair_syn.sig", "pairTools.sig",

     (* pred_set *)
     "PFset_conv.sig","PSet_ind.sig","pred_setTheory.sig",
     "PGspec.sig","pred_setLib.sig",

     (* Quotations *)
     "Q.sig",

     (* Reduce *)
     "Arithconv.sig","Boolconv.sig","reduceLib.sig",

     (* Refute *)
     "AC.sig","Canon.sig",

     (* Res_quan *)
     "Cond_rewrite.sig","Res_quan.sig","res_quanLib.sig",
     "res_quanTheory.sig",

     (* set *)
     "Fset_conv.sig","Gspec.sig","Set_ind.sig",
     "setLib.sig","setTheory.sig",

     (* simpLib *)
     "Cache.sig","SatisfySimps.sig","Unify.sig","listSimps.sig",
     "Cond_rewr.sig","Sequence.sig","Unwind.sig","pairSimps.sig",
     "HOLSimps.sig","simpLib.sig","sumSimps.sig",
     "rich_listSimps.sig","Termtable.sig","arithSimps.sig",
     "Opening.sig","Traverse.sig","boolSimps.sig",
     "Satisfy.sig","Travrules.sig","combinSimps.sig","Trace.sig",

     (* string *)
     "Ascii.sig","String_conv.sig","stringLib.sig",
     "asciiTheory.sig","stringTheory.sig",

     (* disjoint union *)
     "sumTheory.sig",

     (* tautLib *)
     "tautLib.sig",

     (* TFL *)
     "RW.sig", "Defn.sig", "TotalDefn.sig",
     "relationTheory.sig", 

     (* tree theories *)
     "treeTheory.sig", "ltreeTheory.sig",

     (* unwind *)
     "unwindLib.sig",

     (* boss *)
     "bossLib.sig",

     (* word *)
     "wordLib.sig",
     "bword_arithTheory.sig","wordTheory.sig","word_numTheory.sig",
     "bword_bitopTheory.sig","word_baseTheory.sig",
     "bword_numTheory.sig","word_bitopTheory.sig",

     (* HolBdd*)
     "HolBdd.sig", "HolBddTheory.sig", "StateEnum.sig",
     "bdd.sig", "bvec.sig", "fdd.sig", "muddyLib.sig",

     (* computeLib *)
     "computeLib.sig", "compute_rules.sig",

     (* temporalLib *)
     "Omega_AutomataTheory.sig", "Past_Temporal_LogicTheory.sig",
     "Temporal_LogicTheory.sig", "temporalLib.sig",

     (* multisets *)
     "bagTheory.sig",

     (* basic automated proof *)
     "BasicProvers.sig",

     (* real numbers *)
     "Diff.sig", "limTheory.sig", "realTheory.sig",
     "RealArith.sig", "netsTheory.sig", "realaxTheory.sig",
     "RealSS.sig", "polyTheory.sig", "seqTheory.sig",
     "hratTheory.sig", "powserTheory.sig", "topologyTheory.sig",
     "hrealTheory.sig", "realLib.sig", "transcTheory.sig",

     (* Rings *)

     "abstraction.sig",        "prelimTheory.sig",
     "canonicalTheory.sig",    "quoteTheory.sig",
     "integerRingLib.sig",     "ringLib.sig",
     "integerRingTheory.sig",  "ringNormTheory.sig",
     "numRingLib.sig",         "ringTheory.sig",
     "numRingTheory.sig",      "semi_ringTheory.sig"]

 in
   Database.writebase (Path.concat(holpath, Path.concat ("help", "HOLdbase")),
                       Database.fromList all_indices)
 end;


fun errmsg s = TextIO.output(TextIO.stdErr, s ^ "\n");

val _ =
    case Mosml.argv () of
	[_,path]  => buildDb path
      |    _      => errmsg "Usage: mk_dbs <hol98-directory>/"

