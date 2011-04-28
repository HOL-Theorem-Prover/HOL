structure Keepers = struct
(*---------------------------------------------------------------------------*)
(* A list of the signatures that we think users will be interested in.       *)
(*---------------------------------------------------------------------------*)

val keepers =
  [ "Systeml.sig",

    (* portableML *)
     "Arbnum.sig", "Arbnumcore.sig", "Arbint.sig", "Arbintcore.sig",
     "Portable.sig",

     (*0*)
      "Type.sig", "Term.sig", "Thm.sig", "Theory.sig", "Definition.sig",
      "Net.sig", "Count.sig", "Feedback.sig", "Lexis.sig", "Tag.sig",
      "Lib.sig", "Globals.sig",

     (* parse *)
     "Parse.sig", "Hol_pp.sig", "Absyn.sig", "Preterm.sig",

     (* boolLib *)
     "Abbrev.sig", "DB.sig", "boolSyntax.sig", "boolTheory.sig",
     "Drule.sig", "Tactical.sig", "Tactic.sig", "Thm_cont.sig",
     "Conv.sig", "ConseqConv.sig", "Ho_Net.sig", "Ho_Rewrite.sig",
     "Rewrite.sig", "Rsyntax.sig", "Psyntax.sig",
     "TypeBase.sig", "TypeBasePure.sig", "DefnBase.sig", "Prim_rec.sig",

     (* marker *)
     "markerLib.sig", "markerSyntax.sig",

     (* emit *)
     "EmitML.sig", "EmitTeX.sig",

     (* jrh ind_defs *)
     "IndDefLib.sig", "InductiveDefinition.sig", "IndDefRules.sig",

     (* multisets *)
     "bagTheory.sig", "bagLib.sig", "bagSimps.sig", "bagSyntax.sig",
     "containerTheory.sig",

     (* basic automated proof *)
     "BasicProvers.sig",

     (* boss *)
     "bossLib.sig",

     (* combin theory *)
     "combinTheory.sig", "combinSyntax.sig",

     (* computeLib *)
     "computeLib.sig",

     (* datatype *)
     "Datatype.sig", "ind_typeTheory.sig", "ind_types.sig",
     "RecordType.sig", "EquivType.sig",

     (* finite maps *)
     "finite_mapTheory.sig",

     (* proofManagerLib *)
     "proofManagerLib.sig",

     (* Integer *)
     "integerTheory.sig", "Cooper.sig", "intLib.sig", "intSyntax.sig",
     "integer_wordTheory.sig", "integer_wordSyntax.sig",

     (* list *)
     "rich_listTheory.sig", "listTheory.sig", "listLib.sig",
     "operatorTheory.sig", "listSyntax.sig", "listSimps.sig",

     (* lite *)
     "liteLib.sig",

     (* lazy list *)
     "llistTheory.sig",

     (* meson *)
     "Canon_Port.sig", "jrhTactics.sig", "mesonLib.sig",

     (* n-bit *)
     "fcpTheory.sig",
     "bitTheory.sig",
     "bitSyntax.sig",
     "wordsTheory.sig",
     "wordsSyntax.sig",
     "fcpLib.sig",
     "fcpSyntax.sig",
     "wordsLib.sig",
     "blastLib.sig",

     (* patricia *)
     "patriciaTheory.sig",
     "patriciaSyntax.sig",
     "patriciaLib.sig",
     "patricia_castsTheory.sig",
     "patricia_castsSyntax.sig",
     "patricia_castsLib.sig",

     (* num *)
     "numSyntax.sig",
     "numTheory.sig", "prim_recTheory.sig", "arithmeticTheory.sig",
     "numeralTheory.sig", "whileTheory.sig", "Arith.sig", "numLib.sig",
     "numSimps.sig", "reduceLib.sig", "dividesTheory.sig", "gcdTheory.sig",

     (* one *)
     "oneTheory.sig",

     (* option *)
     "optionLib.sig", "optionTheory.sig", "optionSyntax.sig",

     (* pair *)
     "pairLib.sig", "pairTheory.sig", "pairSyntax.sig",
     "PairedLambda.sig", "pairSimps.sig", "pairTools.sig",
     "PairRules.sig",

     (* pred_set *)
     "pred_setLib.sig",
     "pred_setTheory.sig", "pred_setSyntax.sig", "pred_setSimps.sig",

     (* probability *)
     "probLib.sig", "probTheory.sig",
     "boolean_sequenceTheory.sig",
     "prob_algebraTheory.sig", "prob_indepTheory.sig",
     "prob_canonTheory.sig",
     "prob_extraTheory.sig",
     "prob_pseudoTheory.sig",
     "prob_uniformTheory.sig",
     "state_transformerTheory.sig",

     (* Quotations *)
     "Q.sig",

     (* rational numbers *)
     "ratTheory.sig", "ratLib.sig", "ratSyntax.sig", "ratRingLib.sig",

     (* real numbers *)
     "limTheory.sig", "realTheory.sig",
     "RealArith.sig", "netsTheory.sig", "realaxTheory.sig",
     "realSimps.sig", "polyTheory.sig", "seqTheory.sig",
     "hratTheory.sig", "powserTheory.sig", "topologyTheory.sig",
     "hrealTheory.sig", "realLib.sig", "transcTheory.sig",

     (* refute *)
     "AC.sig", "Canon.sig",

     (* relation *)
     "relationTheory.sig",

     (* res_quan *)
     "Cond_rewrite.sig", "res_quanLib.sig", "res_quanTools.sig",
     "res_quanTheory.sig",

     (* Rings *)

     "prelimTheory.sig",
     "canonicalTheory.sig",    "quoteTheory.sig",
     "integerRingLib.sig",     "ringLib.sig",
     "integerRingTheory.sig",  "ringNormTheory.sig",
     "numRingLib.sig",         "ringTheory.sig",
     "numRingTheory.sig",      "semi_ringTheory.sig",

     (* simpLib *)
     "simpLib.sig", "boolSimps.sig",

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

     (* HolSat *)
     "HolSatLib.sig",

     (* simpsets *)
     "optionSimps.sig", "intSimps",

     (* sorting theory *)
     "sortingTheory.sig", "permLib.sig",

     (* fixed point operators on sets *)
     "fixedPointTheory.sig",

     (* paths theory *)
     "pathTheory.sig",

     (* Encoding and Decoding *)
     "CoderTheory.sig", "DecodeTheory.sig",
     "EncodeTheory.sig", "EncodeVarTheory.sig",

     (* Floating point arithmetic *)
     "floatTheory.sig", "ieeeTheory.sig",

     (* quantifier elimination *)
     "quantHeuristicsLib.sig"

  ];
end;
