structure preARMSyntax =
struct

open HolKernel Parse boolLib preARMTheory pairLib 
     numSyntax optionSyntax listSyntax;

(*----------------------------------------------------------------------------*)
(* Generate ARM programs                                                      *)
(*----------------------------------------------------------------------------*)

fun eval_exp (Assem.MEM {reg = regNo, offset = offset, wback = flag}) =
      mk_comb(Term`MEM:(num # num) -> EXP`, mk_pair(term_of_int regNo, term_of_int offset))
 |  eval_exp (Assem.NCONST e) =
      mk_comb(Term`NCONST`, term_of_int e)
 |  eval_exp (Assem.WCONST e) =
      mk_comb(Term`WCONST`, mk_comb (Term`n2w`, term_of_int e))
 |  eval_exp (Assem.REG e) =
      mk_comb(Term`REG`, term_of_int e)
 |  eval_exp (Assem.WREG e) =
      mk_comb(Term`WREG`, term_of_int e)
 |  eval_exp (Assem.PAIR(e1,e2)) =
      mk_pair(eval_exp e1, eval_exp e2)
 |  eval_exp _ =
      raise ERR "ARM" ("invalid expression")

fun mk_ARM arm =
  let

    val (fname, ftype, args,stms,outs) = arm;

    fun mk_stm (Assem.OPER {oper = (op1, cond1, flag), dst = dlist, src = slist, jump = jumps}) =
        let 
	    val ops = list_mk_pair [mk_const(Assem.print_op op1, Type `:OPERATOR`),
				     if cond1 = NONE then mk_none (Type `:COND`)
				     else mk_comb(Term`SOME:COND->COND option`, mk_const(Assem.print_cond cond1, Type `:COND`)), 
				     boolSyntax.F]
	    val (slist,dlist) = if op1 = Assem.LDMFD orelse op1 = Assem.STR then (dlist,slist)
				else if op1 = Assem.CMP then (slist, [])
				else (slist,dlist)
	    val d1 = if length dlist = 0 then 
			mk_none (Type `:EXP`)
		     else mk_some (eval_exp (hd dlist));
            val s1 = mk_list (List.map eval_exp slist, Type `:EXP`);
            val j1 = (case jumps of
                         NONE => mk_none (Type `:OFFSET`)
                      |  SOME l =>
                                if Symbol.name (hd l) = "+" then
                                        mk_some (mk_comb(Term`POS`, term_of_int (Symbol.index (hd l))))
                                else mk_some (mk_comb(Term`NEG`, term_of_int (Symbol.index (hd l))))
                     )
        in
            list_mk_pair [ops,d1,s1,j1]
        end

    |  mk_stm (Assem.MOVE inst) =
        list_mk_pair [list_mk_pair [Term`MOV`, Term`NONE : COND option`, boolSyntax.F],
                      mk_some (eval_exp (#dst inst)),
                      mk_list ([eval_exp (#src inst)], Type `:EXP`),
                      mk_none (Type `:OFFSET`)
                     ]

    |  mk_stm (Assem.LABEL _) =
	( print "Please use link2 to remove the labels first \n";
	  raise ERR "ARM" ("invalid ARM program")
	)

  in
     ( fname, ftype,
       args,
       mk_list(List.map mk_stm stms, Type `:INST`),
       outs
     )
  end

end (* structure *)
