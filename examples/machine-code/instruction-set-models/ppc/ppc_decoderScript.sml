
open HolKernel boolLib bossLib Parse;
open wordsTheory stringTheory stringLib listTheory stringSimps listLib simpLib;
open decoderTheory bit_listTheory opmonTheory;

open ppc_astTheory;

val _ = new_theory "ppc_decoder";


(* ---------------------------------------------------------------------------------- *>

  A decoder for PowerPC instructions is defined and, at the end, pre-evaluated for
  fast execution with EVAL.

<* ---------------------------------------------------------------------------------- *)

val ppc_match_step_def = Define `
  ppc_match_step name =
    if name = "0" then DF else
    if name = "1" then DT else
    if MEM name ["A";"B";"C";"D";"S";"BO";"BI";"crbA";"crbB";"crbD";"SH";"MB";"ME"] then
      assign_drop name 5
    else if MEM name ["BD"] then
      assign_drop name 14
    else if MEM name ["SIMM";"UIMM";"d"] then
      assign_drop name 16
    else if MEM name ["LI"] then
      assign_drop name 24
    else if MEM name ["AA";"Rc";"OE";"y";"z"] then
      assign_drop name 1
    else
      option_fail`;

(* The following strings are copied from the PowerPC manual. *)

val ppc_syntax = ``
  [("0 1 1 1 1 1 D A B 0 1 0 0 0 0 1 0 1 0 0",
     (\v. Padd (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 0 1 1 1 0 D A SIMM",
     (\v. Paddi (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 0 1 1 1 1 D A SIMM",
     (\v. Paddis (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 1 1 1 1 1 D A 0 0 0 0 0 0 0 1 1 0 0 1 0 1 0 0",
     (\v. Paddze (b2w v "D") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 0 0 0 0 1 1 1 0 0 1",
     (\v. Pand_ (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 0 0 0 1 1 1 1 0 0 0",
     (\v. Pandc (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 0 0 S A UIMM",
     (\v. Pandi_ (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 1 1 0 1 S A UIMM",
     (\v. Pandis_ (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 0 0 1 0 LI 0 0",
     (\v. Pb (b2w v "LI")));
   ("0 1 0 0 0 0 BO BI BD 0 0",
     (\v. Pbc (b2w v "BO") (b2w v "BI") (b2w v "BD")));
   ("0 1 0 0 1 0 LI 0 1",
     (\v. Pbl (b2w v "LI")));
   ("0 1 0 0 1 1  1 z 1 z z  BI 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0",
     (\v. Pblr));
   ("0 1 0 0 1 1  1 z 1 z z  BI 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 0",
     (\v. Pbctr));
   ("0 1 0 0 1 1  1 z 1 z z  BI 0 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1",
     (\v. Pbctrl));
   ("0 1 1 1 1 1 0 0 0 0 0 A B 0 0 0 0 1 0 0 0 0 0 0",
     (\v. Pcmplw (b2w v "A") (b2w v "B")));
   ("0 0 1 0 1 0 0 0 0 0 0 A UIMM",
     (\v. Pcmplwi (b2w v "A") (b2w v "UIMM")));
   ("0 1 1 1 1 1 0 0 0 0 0 A B 0 0 0 0 0 0 0 0 0 0 0",
     (\v. Pcmpw (b2w v "A") (b2w v "B")));
   ("0 0 1 0 1 1 0 0 0 0 0 A SIMM",
     (\v. Pcmpwi (b2w v "A") (b2w v "SIMM")));
   ("0 1 0 0 1 1 crbD crbA crbB 0 1 1 1 0 0 0 0 0 1 0",
     (\v. Pcror (b2w v "crbD") (b2w v "crbA") (b2w v "crbB")));
   ("0 1 1 1 1 1 D A B 0 1 1 1 1 0 1 0 1 1 0",
     (\v. Pdivw (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 D A B 0 1 1 1 0 0 1 0 1 1 0",
     (\v. Pdivwu (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 0 0 0 1 1 1 0 0 0",
     (\v. Peqv (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A 0 0 0 0 0 1 1 1 0 1 1 1 0 1 0 0",
     (\v. Pextsb (b2w v "A") (b2w v "S")));
   ("0 1 1 1 1 1 S A 0 0 0 0 0 1 1 1 0 0 1 1 0 1 0 0",
     (\v. Pextsh (b2w v "A") (b2w v "S")));
   ("1 0 0 0 1 0 D A d",
     (\v. Plbz (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 0 0 1 0 1 0 1 1 1 0",
     (\v. Plbzx (b2w v "D") (b2w v "A") (b2w v "B")));
   ("1 0 1 0 1 0 D A d",
     (\v. Plha (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 1 0 1 0 1 0 1 1 1 0",
     (\v. Plhax (b2w v "D") (b2w v "A") (b2w v "B")));
   ("1 0 1 0 0 0 D A d",
     (\v. Plhz (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 1 0 0 0 1 0 1 1 1 0",
     (\v. Plhzx (b2w v "D") (b2w v "A") (b2w v "B")));
   ("1 0 0 0 0 0 D A d",
     (\v. Plwz (b2w v "D") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 D A B 0 0 0 0 0 1 0 1 1 1 0",
     (\v. Plwzx (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 D 0 1 0 0 0 0 0 0 0 0 0 1 0 1 0 1 0 0 1 1 0",
     (\v. Pmflr (b2w v "D")));
   ("0 1 1 1 1 1 S A S! 0 1 1 0 1 1 1 1 0 0 0",
     (\v. Pmr (b2w v "A") (b2w v "S")));
   ("0 1 1 1 1 1 D 0 1 0 0 1 0 0 0 0 0 0 1 1 1 0 1 0 0 1 1 0",
     (\v. Pmtctr (b2w v "D")));
   ("0 1 1 1 1 1 D 0 1 0 0 0 0 0 0 0 0 0 1 1 1 0 1 0 0 1 1 0",
     (\v. Pmtlr (b2w v "D")));
   ("0 0 0 1 1 1 D A SIMM",
     (\v. Pmulli (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 1 1 1 1 1 D A B 0 0 1 1 1 0 1 0 1 1 0",
     (\v. Pmullw (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 1 1 0 1 1 1 0 0 0",
     (\v. Pnand (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 0 0 1 1 1 1 1 0 0 0",
     (\v. Pnor (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 1 0 1 1 1 1 0 0 0",
     (\v. Por (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 0 1 1 0 0 1 1 1 0 0 0",
     (\v. Porc (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 0 0 0 S A UIMM",
     (\v. Pori (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 1 0 0 1 S A UIMM",
     (\v. Poris (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 0 1 0 1 S A SH MB ME 0",
     (\v. Prlwinm (b2w v "A") (b2w v "S") (b2w v "SH") (b2w v "MB") (b2w v "ME")));
   ("0 1 1 1 1 1 S A B 0 0 0 0 0 1 1 0 0 0 0",
     (\v. Pslw (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A B 1 1 0 0 0 1 1 0 0 0 0",
     (\v. Psraw (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 1 1 1 S A SH 1 1 0 0 1 1 1 0 0 0 0",
     (\v. Psrawi (b2w v "A") (b2w v "S") (b2w v "SH")));
   ("0 1 1 1 1 1 S A B 1 0 0 0 0 1 1 0 0 0 0",
     (\v. Psrw (b2w v "A") (b2w v "S") (b2w v "B")));
   ("1 0 0 1 1 0 S A d",
     (\v. Pstb (b2w v "S") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 0 1 1 0 1 0 1 1 1 0",
     (\v. Pstbx (b2w v "S") (b2w v "A") (b2w v "B")));
   ("1 0 1 1 0 0 S A d",
     (\v. Psth (b2w v "S") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 1 1 0 0 1 0 1 1 1 0",
     (\v. Psthx (b2w v "S") (b2w v "A") (b2w v "B")));
   ("1 0 0 1 0 0 S A d",
     (\v. Pstw (b2w v "S") (b2w v "d") (b2w v "A")));
   ("0 1 1 1 1 1 S A B 0 0 1 0 0 1 0 1 1 1 0",
     (\v. Pstwx (b2w v "S") (b2w v "A") (b2w v "B")));
   ("0 1 1 1 1 1 D A B 0 0 0 0 0 0 1 0 0 0 0",
     (\v. Psubfc (b2w v "D") (b2w v "A") (b2w v "B")));
   ("0 0 1 0 0 0 D A SIMM",
     (\v. Psubfic (b2w v "D") (b2w v "A") (b2w v "SIMM")));
   ("0 1 1 1 1 1 S A B 0 1 0 0 1 1 1 1 0 0 0",
     (\v. Pxor (b2w v "A") (b2w v "S") (b2w v "B")));
   ("0 1 1 0 1 0 S A UIMM",
     (\v. Pxori (b2w v "A") (b2w v "S") (b2w v "UIMM")));
   ("0 1 1 0 1 1 S A UIMM",
     (\v. Pxoris (b2w v "A") (b2w v "S") (b2w v "UIMM")))]    ``;

val ppc_decode_def = Define `
  ppc_decode = match_list ppc_match_step (REVERSE o tokenise) (\k x. SOME (k (FST x))) ^ppc_syntax`;

(* -- partially pre-evaluate ppc_decode -- *)

fun eval_term_ss tm_name tm = conv_ss
  { name = tm_name, trace = 3, key = SOME ([],tm), conv = K (K EVAL) };
val token_ss = eval_term_ss "tokenise" ``tokenise x``;
val if_ss = conv_ss { name = "if", trace = 3,
  key = SOME ([],``if x then (y:'a) else z``),
  conv = K (K ((RATOR_CONV o RATOR_CONV o RAND_CONV) EVAL)) };

val ppc_decode_thm = let
  val n2bits_ss = eval_term_ss "n2bits" ``n2bits m n``;
  val th1 = REWRITE_CONV [MAP,ppc_decode_def,combinTheory.o_DEF,match_list_def] ``ppc_decode``
  val th2 = SIMP_RULE (std_ss++token_ss) [match_def,REV_DEF,REVERSE_REV] th1
  val th3 = SIMP_RULE (bool_ss++if_ss++n2bits_ss) [MAP,ppc_match_step_def] th2
  val th4 = REWRITE_RULE [option_then_assoc,drop_eq_thm,option_do_def] th3
  val th5 = REWRITE_RULE [option_try_def,GSYM option_orelse_assoc] th4
  val th6 = REWRITE_RULE [option_then_OVER_orelse] th5
  val th7 = REWRITE_RULE [option_orelse_assoc] th6
  in th7 end;

fun permanently_add_to_compset name thm = let
  val _ = save_thm(name,thm)
  val _ = computeLib.add_funs [thm]
  val _ = adjoin_to_theory {sig_ps = NONE, struct_ps = SOME (fn ppstrm =>
    let val S = (fn s => (PP.add_string ppstrm s; PP.add_newline ppstrm)) in
            S ("val _ = computeLib.add_funs ["^name^"];")
    end)}
  in print ("Permanently added to compset: "^name^"\n") end;

val _ = permanently_add_to_compset "ppc_decode_thm" ppc_decode_thm;


val _ = export_theory ();

