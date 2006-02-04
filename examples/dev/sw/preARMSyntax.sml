structure preARMSyntax =
struct

local
  open HolKernel Parse boolLib preARMTheory pairLib 
       numSyntax optionSyntax listSyntax
in
(*----------------------------------------------------------------------------*)
(* Generate ARM programs                                                      *)
(*----------------------------------------------------------------------------*)

fun eval_exp (Assem.MEM {reg = regNo, offset = offset, wback = flag}) =
      mk_comb(Term`MEM:(num # OFFSET) -> EXP`,
                mk_pair(term_of_int regNo,
                  mk_comb(if offset >= 0 then Term`POS` else Term`NEG`,
                          term_of_int (abs offset))))
 |  eval_exp (Assem.NCONST e) =
      mk_comb(Term`NCONST`, mk_numeral (Arbint.toNat e))
 |  eval_exp (Assem.WCONST e) =
      mk_comb(Term`WCONST`, mk_comb (Term`n2w`, mk_numeral (Arbint.toNat e)))
 |  eval_exp (Assem.REG e) =
      mk_comb(Term`REG`, term_of_int e)
 |  eval_exp (Assem.WREG e) =
      mk_comb(Term`WREG`, term_of_int e)
 |  eval_exp (Assem.PAIR(e1,e2)) =
      mk_pair(eval_exp e1, eval_exp e2)
 |  eval_exp _ =
      raise ERR "ARM" ("invalid expression")

fun mk_ARM (arm,anfs) =
  let

    fun mk_stm (Assem.OPER {oper = (op1, cond1, flag), dst = dlist, src = slist, jump = jumps}) =
        let
            val ops = list_mk_pair [ mk_thy_const {Name = Assem.print_op op1, Thy = "preARM", Ty = Type `:OPERATOR`},

				     (* For instruction BL, jump is always effective; and, when the pc appears in the destination list, then
					a jump occurs												*) 
                                     if op1 = Assem.BL orelse not (List.find (fn r => r = Assem.REG 15 orelse r = Assem.WREG 15) dlist = NONE)  then 
						Term(`SOME AL:COND option`)         (* always jumps *)

				     else if cond1 = NONE then mk_none (Type `:COND`)
                                     else mk_comb(Term`SOME:COND->COND option`,
                                                   mk_const(Assem.print_cond cond1, Type `:COND`)),
                                     Term`F`]

            val j1 = case (List.find (fn e => e = Assem.REG 15 orelse e = Assem.WREG 15) dlist) of
                                (* check whether the pc is in the destination list *)
                        NONE => (case jumps of
                                       NONE => mk_none (Type `:OFFSET`)
                                    |  SOME l =>
                                                if Symbol.name (hd l) = "+" then
                                                        mk_some (mk_comb(Term`POS`, term_of_int (Symbol.index (hd l))))
                                                else mk_some (mk_comb(Term`NEG`, term_of_int (Symbol.index (hd l))))
                                ) |
                        SOME l => mk_some (Term`INR`)     (* the pc is modified to be the value in a register *)

            val (slist,dlist) = if op1 = Assem.LDMFD orelse op1 = Assem.STR then (dlist,slist)
                                else if op1 = Assem.CMP then (slist, [])
                                else (slist,dlist)
            val d1 = if length dlist = 0 then
                        mk_none (Type `:EXP`)
                     else mk_some (eval_exp (hd dlist));
            val s1 = mk_list (List.map eval_exp slist, Type `:EXP`);

        in
            list_mk_pair [ops,d1,s1,j1]
        end

   |  mk_stm (Assem.MOVE inst) =
        list_mk_pair [list_mk_pair [Term`MOV`, Term`NONE : COND option`, Term`F`],
                      mk_some (eval_exp (#dst inst)),
                      mk_list ([eval_exp (#src inst)], Type `:EXP`),
                      mk_none (Type `:OFFSET`)
                     ]

    |  mk_stm (Assem.LABEL _) =
        ( print "Please use link2 to remove the labels first \n";
          raise ERR "ARM" ("invalid ARM program")
        )

    fun one_fun (fname, ftype, args, stms, outs, rs) =
        List.map mk_stm stms;

  in
     ((arm,anfs),
      mk_list(List.foldl (fn (f,instL) => instL @ (one_fun f)) [] arm, Type `:INST`)
     )
  end

end (* local open *)
end (* structure *)
