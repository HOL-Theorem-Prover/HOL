(*---------------------------------------------------------------------------*)
(* A list of the signatures that we think users will be interested in.       *)
(*---------------------------------------------------------------------------*)

val keepers = 
  [ (* portableML *)
     "Arbnum.sig", "Arbint.sig", "Portable.sig",

     (*0*)
      "Type-sig.sml", "Term-sig.sml", "Thm-sig.sml", 
      "Theory-sig.sml", "Net-sig.sml", "Count.sig", 
      "Feedback.sig", "Lexis.sig", "Lib.sig", "Globals.sig", 

     (* parse *)
     "Parse.sig",  "Hol_pp.sig", "Absyn.sig", "Preterm.sig", 

     (* boolLib *)
     "Abbrev.sig", "DB.sig", "boolSyntax.sig", "boolTheory.sig",
     "Drule.sig", "Tactical.sig", "Tactic.sig", "Thm_cont.sig",
     "Conv.sig", "QConv.sig", "Ho_Net.sig", "Ho_Rewrite.sig", 
     "Rewrite.sig", "Rsyntax.sig", "Psyntax.sig",
     "TypeBase.sig", "DefnBase.sig", "Prim_rec.sig",

     (* jrh ind_defs *)
     "IndDefLib.sig", "InductiveDefinition.sig", "IndDefRules.sig",

     (* HolBdd *)
     "HolBdd.sig", "HolBddTheory.sig", "StateEnum.sig",

     (* multisets *)
     "bagTheory.sig", "bagLib.sig", "bagSimps.sig", "bagSyntax.sig",
     "containerTheory.sig",

     (* basic automated proof *)
     "BasicProvers.sig",

     (* boss *)
     "bossLib.sig", "SingleStep.sig",

     (* combin theory *)
     "combinTheory.sig",

     (* computeLib *)
     "computeLib.sig", "compute_rules.sig",

     (* datatype *)
     "Datatype.sig", "ind_typeTheory.sig", "ind_types.sig",
     "RecordType.sig", "EquivType.sig",

     (* finite maps *)
     "finite_mapTheory.sig", 

     (* goalstackLib *)
     "goalstackLib.sig",

     (* hol88 *)
     "hol88Lib.sig",

     (* Integer *)
     "integerTheory.sig", "Cooper.sig", "intLib.sig",
     "gcdTheory.sig", "dividesTheory.sig", "intSyntax.sig",

     (* list *)
     "rich_listTheory.sig", "listTheory.sig", "listLib.sig",
     "operatorTheory.sig", "listSyntax.sig", "listSimps.sig",

     (* lite *)
     "liteLib.sig",

     (* lazy list *)
     "llistTheory.sig",

     (* meson *)
     "Canon_Port.sig","jrhTactics.sig","mesonLib.sig",

     (* muddy *)
     "bdd.sig","bvec.sig","fdd.sig", "muddyLib.sig",

     (* num *)
     "numSyntax.sig", 
     "numTheory.sig", "prim_recTheory.sig", "arithmeticTheory.sig",
     "numeralTheory.sig", "numLib.sig", "arithSimps.sig",
     "reduceLib.sig",  "Arithconv.sig","Boolconv.sig", "arithLib.sig",

     (* one *)
     "oneTheory.sig",

     (* option *)
     "optionLib.sig","optionTheory.sig", "optionSyntax.sig",

     (* pair *)
     "pairLib.sig", "pairTheory.sig", "pairSyntax.sig",
     "PairedLambda.sig", "pairSimps.sig", "pairTools.sig",

     (* pred_set *)
     "PFset_conv.sig", "PSet_ind.sig", "PGspec.sig","pred_setLib.sig",
     "pred_setTheory.sig", "pred_setSimps.sig",

     (* probability *)
     "probLib.sig", "probTheory.sig",
     "boolean_sequenceTheory.sig", "boolean_sequenceTools.sig",
     "prob_algebraTheory.sig",     "prob_indepTheory.sig", 
     "prob_canonTheory.sig",       "prob_canonTools.sig", 
     "prob_extraTheory.sig",       "prob_extraTools.sig", 
     "prob_pseudoTheory.sig",      "prob_pseudoTools.sig", 
     "prob_uniformTheory.sig",     "prob_uniformTools.sig", 
     "state_transformerTheory.sig",

     (* Quotations *)
     "Q.sig",

     (* real numbers *)
     "Diff.sig", "limTheory.sig", "realTheory.sig",
     "RealArith.sig", "netsTheory.sig", "realaxTheory.sig",
     "realSimps.sig", "polyTheory.sig", "seqTheory.sig",
     "hratTheory.sig", "powserTheory.sig", "topologyTheory.sig",
     "hrealTheory.sig", "realLib.sig", "transcTheory.sig",

     (* refute *)
     "AC.sig","Canon.sig",

     (* relation *)
     "relationTheory.sig",

     (* res_quan *)
     "Res_quan.sig", "res_quanLib.sig", "res_quanTheory.sig",

     (* Rings *)

     "abstraction.sig",        "prelimTheory.sig",
     "canonicalTheory.sig",    "quoteTheory.sig",
     "integerRingLib.sig",     "ringLib.sig",
     "integerRingTheory.sig",  "ringNormTheory.sig",
     "numRingLib.sig",         "ringTheory.sig",
     "numRingTheory.sig",      "semi_ringTheory.sig",

     (* simpLib *)
     "Cache.sig", "SatisfySimps.sig","Unify.sig",
     "Cond_rewr.sig", "Unwind.sig", "pureSimps.sig",
     "simpLib.sig", "boolSimps.sig", "Satisfy.sig", "combinSimps.sig",

     (* string *)
     "stringLib.sig", "stringTheory.sig", "stringSyntax.sig", 
     "stringSimps.sig",

     (* disjoint union *)
     "sumTheory.sig", "sumSimps.sig", "sumSyntax.sig",

     (* tautLib *)
     "tautLib.sig",

     (* temporalLib *)
     "Omega_AutomataTheory.sig", "Past_Temporal_LogicTheory.sig",
     "Temporal_LogicTheory.sig", "temporalLib.sig",

     (* TFL *)
     "Defn.sig", "TotalDefn.sig",

     (* unwind *)
     "unwindLib.sig",

     (* word *)
     "wordLib.sig",
     "bword_arithTheory.sig","wordTheory.sig","word_numTheory.sig",
     "bword_bitopTheory.sig","word_baseTheory.sig",
     "bword_numTheory.sig","word_bitopTheory.sig"];
