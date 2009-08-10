
open HolKernel boolLib bossLib Parse;

open ppc_coretypesTheory;


val _ = new_theory "ppc_ast";


(* ---------------------------------------------------------------------------------- *>

  This theory defines the abstract syntax tree (AST) for PowerPC instructions.

  It leaves out the following which don't correspond to a PowerPC instruction:

    | Pallocframe of Z => Z       (* allocate new stack frame *)
    | Pallocblock                 (* allocate new heap block *)
    | Plfi of freg => float       (* load float constant *)
    | Plabel of label             (* define a code label *)
    | Pfreeframe                  (* deallocate stack frame and restore previous frame *)
    | Pmfcrbit of ireg => crbit   (* move condition bit to reg *)

  Types ireg, freg, ppc_constant, and crbit are used from ppc_coretypesTheory.

<* ---------------------------------------------------------------------------------- *)


val _ = Hol_datatype `
  instruction =
    Padd of ireg => ireg => ireg            (* integer addition *)
  | Paddi of ireg => ireg => ppc_constant   (* add immediate *)
  | Paddis of ireg => ireg => ppc_constant  (* add immediate high *)
  | Paddze of ireg => ireg                  (* add Carry bit *)
  | Pand_ of ireg => ireg => ireg           (* bitwise and *)
  | Pandc of ireg => ireg => ireg           (* bitwise and-complement *)
  | Pandi_ of ireg => ireg => ppc_constant  (* and immediate and set conditions *)
  | Pandis_ of ireg => ireg => ppc_constant (* and immediate high and set conditions *)
  | Pb of word24                            (* unconditional branch *)
  | Pbc of word5 => crbit => 14 word        (* conditional branch *)
  | Pbctr                                   (* branch to contents of register CTR *)
  | Pbctrl                                  (* branch to contents of CTR and link *)
  | Pbl of word24                           (* branch and link *)
  | Pblr                                    (* branch to contents of register LR *)
  | Pcmplw of ireg => ireg                  (* unsigned integer comparison *)
  | Pcmplwi of ireg => ppc_constant         (* same, with immediate argument *)
  | Pcmpw of ireg => ireg                   (* signed integer comparison *)
  | Pcmpwi of ireg => ppc_constant          (* same, with immediate argument *)
  | Pcror of crbit => crbit => crbit        (* or between condition bits *)
  | Pdivw of ireg => ireg => ireg           (* signed division *)
  | Pdivwu of ireg => ireg => ireg          (* unsigned division *)
  | Peqv of ireg => ireg => ireg            (* bitwise not-xor *)
  | Pextsb of ireg => ireg                  (* 8-bit sign extension *)
  | Pextsh of ireg => ireg                  (* 16-bit sign extension *)
  | Pfabs of freg => freg                   (* float absolute value *)
  | Pfadd of freg => freg => freg           (* float addition *)
  | Pfcmpu of freg => freg                  (* float comparison *)
  | Pfcti of ireg => freg                   (* float-to-int conversion *)
  | Pfdiv of freg => freg => freg           (* float division *)
  | Pfmadd of freg => freg => freg => freg  (* float multiply-add *)
  | Pfmr of freg => freg                    (* float move *)
  | Pfmsub of freg => freg => freg => freg  (* float multiply-sub *)
  | Pfmul of freg => freg => freg           (* float multiply *)
  | Pfneg of freg => freg                   (* float negation *)
  | Pfrsp of freg => freg                   (* float round to single precision *)
  | Pfsub of freg => freg => freg           (* float subtraction *)
  | Pictf of freg => ireg                   (* int-to-float conversion *)
  | Piuctf of freg => ireg                  (* unsigned int-to-float conversion *)
  | Plbz of ireg => ppc_constant => ireg    (* load 8-bit unsigned word32 *)
  | Plbzx of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Plfd of freg => ppc_constant => ireg    (* load 64-bit float *)
  | Plfdx of freg => ireg => ireg           (* same, with 2 index regs *)
  | Plfs of freg => ppc_constant => ireg    (* load 32-bit float *)
  | Plfsx of freg => ireg => ireg           (* same, with 2 index regs *)
  | Plha of ireg => ppc_constant => ireg    (* load 16-bit signed word32 *)
  | Plhax of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Plhz of ireg => ppc_constant => ireg    (* load 16-bit unsigned word32 *)
  | Plhzx of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Plwz of ireg => ppc_constant => ireg    (* load 32-bit word32 *)
  | Plwzx of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Pmfcrbit of ireg => crbit               (* move condition bit to reg *)
  | Pmflr of ireg                           (* move LR to reg *)
  | Pmr of ireg => ireg                     (* integer move *)
  | Pmtctr of ireg                          (* move ireg to CTR *)
  | Pmtlr of ireg                           (* move ireg to LR *)
  | Pmulli of ireg => ireg => ppc_constant  (* integer multiply immediate *)
  | Pmullw of ireg => ireg => ireg          (* integer multiply *)
  | Pnand of ireg => ireg => ireg           (* bitwise not-and *)
  | Pnor of ireg => ireg => ireg            (* bitwise not-or *)
  | Por of ireg => ireg => ireg             (* bitwise or *)
  | Porc of ireg => ireg => ireg            (* bitwise or-complement *)
  | Pori of ireg => ireg => ppc_constant    (* or with immediate *)
  | Poris of ireg => ireg => ppc_constant   (* or with immediate high *)
  | Prlwinm of ireg => ireg => word5 => word5 => word5 (* rotate and mask *)
  | Pslw of ireg => ireg => ireg            (* shift left *)
  | Psraw of ireg => ireg => ireg           (* shift right signed *)
  | Psrawi of ireg => ireg => word5         (* shift right signed immediate *)
  | Psrw of ireg => ireg => ireg            (* shift right unsigned *)
  | Pstb of ireg => ppc_constant => ireg    (* store 8-bit word *)
  | Pstbx of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Pstfd of freg => ppc_constant => ireg   (* store 64-bit float *)
  | Pstfdx of freg => ireg => ireg          (* same, with 2 index regs *)
  | Pstfs of freg => ppc_constant => ireg   (* store 32-bit float *)
  | Pstfsx of freg => ireg => ireg          (* same, with 2 index regs *)
  | Psth of ireg => ppc_constant => ireg    (* store 16-bit word *)
  | Psthx of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Pstw of ireg => ppc_constant => ireg    (* store 32-bit word*)
  | Pstwx of ireg => ireg => ireg           (* same, with 2 index regs *)
  | Psubfc of ireg => ireg => ireg          (* reversed integer subtraction *)
  | Psubfic of ireg => ireg => ppc_constant (* integer subtraction from immediate *)
  | Pxor of ireg => ireg => ireg            (* bitwise xor *)
  | Pxori of ireg => ireg => ppc_constant   (* bitwise xor with immediate *)
  | Pxoris of ireg => ireg => ppc_constant  (* bitwise xor with immediate high *)
`;



val _ = export_theory ();
