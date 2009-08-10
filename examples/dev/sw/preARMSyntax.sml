structure preARMSyntax =
struct

local
  open HolKernel Parse boolLib preARMTheory pairLib
       numSyntax optionSyntax listSyntax
in

(*----------------------------------------------------------------------------*)
(* Create ARM progroms to be used in HOL                                      *)
(* From ML programs to HOL programs                                           *)
(*----------------------------------------------------------------------------*)

fun to_exp (Assem.MEM {reg = regNo, offset = offset, wback = flag}) =
      mk_comb(Term`MEM:(num # OFFSET) -> EXP`,
                mk_pair(term_of_int regNo,
                  mk_comb(if offset >= 0 then Term`POS` else Term`NEG`,
                          term_of_int (abs offset))))
 |  to_exp (Assem.NCONST e) =
      mk_comb(Term`NCONST`, mk_numeral (Arbint.toNat e))
 |  to_exp (Assem.WCONST e) =
      mk_comb(Term`WCONST`, mk_comb (Term`n2w:num->word32`, mk_numeral (Arbint.toNat e)))
 |  to_exp (Assem.REG e) =
      mk_comb(Term`REG`, term_of_int e)
 |  to_exp (Assem.WREG e) =
      mk_comb(Term`WREG`, term_of_int e)
 |  to_exp (Assem.PAIR(e1,e2)) =
      mk_pair(to_exp e1, to_exp e2)
 |  to_exp _ =
      raise ERR "ARM" ("invalid expression")

fun mk_arm (ins,stms,outs) =
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
                     else mk_some (to_exp (hd dlist));
            val s1 = mk_list (List.map to_exp slist, Type `:EXP`);

        in
            list_mk_pair [ops,d1,s1,j1]
        end

   |  mk_stm (Assem.MOVE inst) =
        list_mk_pair [list_mk_pair [Term`MOV`, Term`NONE : COND option`, Term`F`],
                      mk_some (to_exp (#dst inst)),
                      mk_list ([to_exp (#src inst)], Type `:EXP`),
                      mk_none (Type `:OFFSET`)
                     ]

    |  mk_stm (Assem.LABEL _) =
        ( print "Please use link2 to remove the labels first \n";
          raise ERR "ARM" ("invalid ARM program")
        )

    fun one_fun (args, stms, outs) =
        (to_exp args,
         mk_list(List.map mk_stm stms, Type `:INST`),
         to_exp outs
        )

  in
      one_fun (ins,stms,outs)
  end

(*----------------------------------------------------------------------------*)
(* Convert from HOL programs to ML programs                                   *)
(*----------------------------------------------------------------------------*)

fun from_op operator =
  if operator = Term `ADD` then Assem.ADD
  else if operator = Term `SUB:OPERATOR` then Assem.SUB
  else if operator = Term `RSB:OPERATOR` then Assem.RSB
  else if operator = Term `MUL:OPERATOR` then Assem.MUL
  else if operator = Term `MLA:OPERATOR` then Assem.MLA
  else if operator = Term `AND:OPERATOR` then Assem.AND
  else if operator = Term `ORR:OPERATOR` then Assem.ORR
  else if operator = Term `EOR:OPERATOR` then Assem.EOR
  else if operator = Term `CMP:OPERATOR` then Assem.CMP
  else if operator = Term `TST:OPERATOR` then Assem.TST
  else if operator = Term `LSL:OPERATOR` then Assem.LSL
  else if operator = Term `LSR:OPERATOR` then Assem.LSR
  else if operator = Term `ASR:OPERATOR` then Assem.ASR
  else if operator = Term `ROR:OPERATOR` then Assem.ROR
  else if operator = Term `LDR:OPERATOR` then Assem.LDR
  else if operator = Term `LDMFD:OPERATOR` then Assem.LDMFD
  else if operator = Term `STR:OPERATOR` then Assem.STR
  else if operator = Term `STMFD:OPERATOR` then Assem.STMFD
  else if operator = Term `MRS:OPERATOR` then Assem.MRS
  else if operator = Term `MSR:OPERATOR` then Assem.MSR
  else if operator = Term `BL:OPERATOR` then Assem.BL
  else if operator = Term `B:OPERATOR` then Assem.B
  else if operator = Term `SWI:OPERATOR` then Assem.SWI
  else if operator = Term `NOP:OPERATOR` then Assem.NOP
  else raise Fail "from_op: invalid ARM operator!"

fun from_cond cond =
  if cond = Term `SOME EQ` then SOME (Assem.EQ)
  else if cond = Term `SOME NE` then SOME (Assem.NE)
  else if cond = Term `SOME GE` then SOME (Assem.GE)
  else if cond = Term `SOME LT` then SOME (Assem.LT)
  else if cond = Term `SOME GT` then SOME (Assem.GT)
  else if cond = Term `SOME LE` then SOME (Assem.LE)
  else if cond = Term `SOME AL` then SOME (Assem.AL)
  else if cond = Term `SOME NV` then SOME (Assem.NV)
  else NONE;


fun from_exp t =
    if is_comb t then
       let val (c,v) = dest_comb t
       in
           if same_const c (Term`REG`) then Assem.REG (int_of_term v)
           else if same_const c (Term`WREG`) then Assem.WREG (int_of_term v)
           else if same_const c (Term`NCONST`) then Assem.NCONST ((Arbint.fromNat o dest_numeral) v)
           else if same_const c (Term`WCONST`) then Assem.WCONST ((Arbint.fromNat o dest_numeral) (#2(dest_comb v)))
           else (* MEM *)
               let val (regNo,offset) = dest_pair v
                   val (p,q) = dest_comb offset
               in  Assem.MEM {reg = int_of_term regNo,
                              offset = if same_const p (Term `POS`) then int_of_term q
                                       else (~1 * int_of_term q),
                              wback = false
                             }
               end
        end
    else
        let val (t1,t2) = dest_pair t in
            Assem.PAIR (from_exp t1, from_exp t2)
        end


fun dest_arm stms =
  let

    fun dest_stm stm =
        let
          val [operator0, op_cond0, flag0, dst0, srcL0, jump0] = strip_pair stm;
        in
          if operator0 = Term`MOV` then
             Assem.MOVE {dst = from_exp (dest_some dst0),
                         src = from_exp (hd (#1 (dest_list srcL0)))
                        }
          else
            let
              val operator1 = from_op operator0;
              val op_cond1 = if operator1 = Assem.BL then NONE
                           else from_cond op_cond0;
              val flag1 = false;

              val dst1 = if dst0 = mk_none (Type `:EXP`) then []
                       else [from_exp (dest_some dst0)];
              val srcL1 = List.map from_exp (#1 (dest_list srcL0));
              val (dst2,srcL2) = if operator1 = Assem.LDMFD orelse operator1 = Assem.STR then (srcL1,dst1)
                                else if operator1 = Assem.CMP then ([], srcL1)
                                else (dst1,srcL1);

              val jump1 = if jump0 = mk_none (Type `:OFFSET`) then NONE
                        else let val l = dest_some jump0
                                 val (sign, v) = dest_comb l;
                                 val sign' = if sign = Term`POS` then "+" else "-"
                                 val v' = int_of_term v;
                             in
                                 SOME [Symbol.mkSymbol sign' v']
                             end
            in
              Assem.OPER {oper = (operator1, op_cond1, flag1), dst = dst2, src = srcL2, jump = jump1}
            end
       end
  in
      List.map dest_stm (#1 (dest_list stms))
  end

end (* local open *)
end (* structure *)
