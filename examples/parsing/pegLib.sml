structure pegLib :> pegLib =
struct

fun add_peg_compset cs =
  (computeLib.add_thms
    [grammarTheory.isTOK_def
    ,grammarTheory.language_def
    ,grammarTheory.derive_def
    ,grammarTheory.ptree_fringe_def
    ,grammarTheory.complete_ptree_def
    ,grammarTheory.ptree_head_def
    ,grammarTheory.ptree_size_def
    ,pegTheory.subexprs_def
    ,pegTheory.wfG_def
    ,pegTheory.Gexprs_def
    ,pegexecTheory.poplist_aux_def
    ,pegexecTheory.poplistval_def
    ,pegexecTheory.pegparse_def
    ,pegexecTheory.destResult_def
    ,pegexecTheory.applykont_thm
    ,pegexecTheory.peg_exec_thm
    ] cs;
   List.app (computeLib.add_datatype_info cs o valOf o TypeBase.fetch)
    [``:('a,'b)grammar$symbol``
    ,``:('a,'b)grammar``
    ,``:('a,'b)parsetree``
    ,``:('a,'b,'c)pegsym``
    ,``:('a,'b,'c)peg``
    ,``:('a,'b,'c)kont``
    ,``:('a,'b,'c)evalcase``
    ])

end
