(*---------------------------------------------------------------------------*
 * This file generates a database containing the HOL ".doc" files, and also  *
 * a database that indexes everything that is accessible in the system.      *
 *---------------------------------------------------------------------------*)

(* app load ["Mosml","Database","Parsspec"]; *)

fun mkentry s = {comp = Database.Term(s, SOME"HOL"),
                 file = s^".doc", line = 0};

fun mapfilter f [] = []
  | mapfilter f (h::t) =
     let val L = mapfilter f t
     in f h::L handle Interrupt => raise Interrupt
                    |        _  => L
     end;

fun docdir_to_entries path (endpath, entries) =
  let val dir = Path.concat (path, endpath)
      val L0 = Mosml.listDir dir
      val L1 = List.filter (fn s => not(s=".") andalso not(s="..")) L0
      val L2 = mapfilter (fn s => String.substring(s,0,String.size s - 4)) L1
  in
    List.foldl (fn (e,l) => (mkentry e::l)) entries L2
  end;

(*---------------------------------------------------------------------------
 * The database of all hol ".doc" files.
 *---------------------------------------------------------------------------*)
fun buildDb holpath =
let val doc_indices = List.foldl (docdir_to_entries holpath) []
           ["help/Docfiles",
            "src/arith/help/entries",
            "src/hol88/help/entries",
            "src/list/help/entries",
            "src/pair/help/entries",
            "src/pred_set/help/entries",
            "src/reduce/help/entries",
            "src/res_quan/help/entries",
            "src/set/help/entries",
            "src/string/help/entries",
            "src/taut/help/entries",
            "src/unwind/help/entries",
            "src/utils/help",
            "src/word/help/entries"]

    val all_indices =
       List.foldr (Parsspec.processfile [] (Path.concat(holpath,"sigobj")))
       doc_indices
          ["Const_def.sig", "Parse.sig", "Theory.sig", "Const_spec.sig",
           "Parse_support.sig", "Count.sig", "Hol_pp.sig", (*"PoD.sig", *)
           "Thm.sig", "Dsyntax.sig", "Preterm.sig", "Exception.sig",
           "Type.sig", "Lexis.sig", "Type_def.sig", "Lib.sig",
           "Globals.sig", "Net.sig", "Term.sig",

          (* basicHol90Lib *)
          "Prim_rec.sig", "Tactical.sig", "Conv.sig", "Psyntax.sig",
          "Drule.sig", "Resolve.sig", "Thm_cont.sig",
          "Rewrite.sig", "Type_def_support.sig", "Rsyntax.sig", "Tactic.sig",

           (* jrh ind_defs *)
           "IndDefLib.sig",

           (* Integer *)
           "integerTheory.sig", "useful.sig",

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
           "Datatype.sig","TypeBase.sig",
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
           "Ho_match.sig","Ho_resolve.sig","Ho_theorems.sig",
           "Ho_net.sig","Ho_rewrite.sig",

           (* hol88 *)
           "hol88Lib.sig",

           (* hol90 *)
           "HOLTheory.sig",

           (* tfm ind_def *)
           "ind_defLib.sig",

           (* list *)
           "ListConv1.sig","rich_listTheory.sig","listTheory.sig",
           "ListConv2.sig","listLib.sig","operatorTheory.sig",
           "ConstrProofs.sig",

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
           "Num_conv.sig","arithmeticTheory.sig","numTheory.sig",
              "Num_induct.sig","numLib.sig","prim_recTheory.sig",

           (* one *)
           "oneTheory.sig",

           (* option *)
           "optionLib.sig","optionTheory.sig",

           (* pair *)
           "Let_conv.sig","Pair_conv.sig","pairLib.sig",
           "Pair_basic.sig","Pair_exists.sig","pairTheory.sig",
           "Pair_both1.sig","Pair_forall.sig",
           "Pair_both2.sig","Pair_syn.sig",

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
           "res_quanTheory.sig","restr_binderTheory.sig",

           (* set *)
           "Fset_conv.sig","Gspec.sig","Set_ind.sig",
           "setLib.sig","setTheory.sig",

           (* simpLib *)
           "Cache.sig","SatisfySimps.sig","Unify.sig","listSimps.sig",
           "Cond_rewr.sig","Sequence.sig","Unwind.sig","pairSimps.sig",
           "HOLSimps.sig","simpLib.sig","UnwindSimps.sig","sumSimps.sig",
           "rich_listSimps.sig","Termtable.sig","arithSimps.sig",
           "Opening.sig","Traverse.sig","boolSimps.sig",
           "Satisfy.sig","Travrules.sig","combinSimps.sig","Trace.sig",

           (* string *)
           "Ascii.sig","String_conv.sig","stringLib.sig",
           "asciiTheory.sig","stringTheory.sig",

           (* sums *)
           "sumTheory.sig",

           (* tautLib *)
           "tautLib.sig",

           (* TFL *)
           "Context.sig","Thry.sig","listTools.sig","RW.sig",
           "USyntax.sig","pairTools.sig","Rules.sig","WFTheory.sig",
           (* "pair_caseTheory.sig", *)
           "TCTheory.sig","arithTools.sig",
           "primWFTheory.sig","Tfl.sig","boolTools.sig","tflLib.sig",
           "Thms.sig",  (* "datatypeRW.sig", *)

           (* tree theories *)
           "treeTheory.sig", "ltreeTheory.sig",

           (* unwind *)
             "unwindLib.sig",

           (* utils *)
           "utilsLib.sig",

           (* phb *)
           "bossLib.sig",

           (* word *)
           "wordLib.sig",
          "bword_arithTheory.sig","wordTheory.sig","word_numTheory.sig",
              "bword_bitopTheory.sig","word_baseTheory.sig",
              "bword_numTheory.sig","word_bitopTheory.sig"]

 in
   Database.writebase (Path.concat(holpath, Path.concat ("help", "HOLdbase")),
                       Database.fromList all_indices)
 end;


fun errmsg s = TextIO.output(TextIO.stdErr, s ^ "\n");

val _ =
    case Mosml.argv () of
	[_,path]  => buildDb path
      |    _      => errmsg "Usage: mk_dbs <hol98-directory>/"

