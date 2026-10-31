(* ------------------------------------------------------------------------
   RISCV step evaluator
   ------------------------------------------------------------------------ *)

structure riscv_stepLib :> riscv_stepLib =
struct

open HolKernel boolLib bossLib
open blastLib riscvTheory riscv_stepTheory

structure Parse = struct
  open Parse
  val (Type, Term) =
      parse_from_grammars $ valOf $ grammarDB {thyname="riscv_step"}
end
open Parse

val ERR = Feedback.mk_HOL_ERR "riscv_stepLib"

val () = HOLFlags.set_bflag (Parse.show_assums, true)

val s = ``s:riscv_state``

(* -------------------------------------------------------------------------
   Fetch
   ------------------------------------------------------------------------- *)

local
  val i16 = fcpSyntax.mk_int_numeric_type 16
  val i32 = fcpSyntax.mk_int_numeric_type 32
  val x = Term.mk_var ("x", ``:rawInstType``)
  fun padded_opcode v =
    let
      val (l, ty) = listSyntax.dest_list v
      val () = ignore (ty = Type.bool andalso List.length l <= 32 orelse
               raise ERR "mk_opcode" "bad opcode")
      fun ends_in_TT [] = false
        | ends_in_TT [x] = false
        | ends_in_TT [x,y] = aconv x y andalso aconv x boolSyntax.T
        | ends_in_TT (x::xs) = ends_in_TT xs
    in
      if ends_in_TT l then
        listSyntax.mk_list (utilsLib.padLeft boolSyntax.F 32 l, ty)
      else
        listSyntax.mk_list (utilsLib.padLeft boolSyntax.F 16 l, ty)
    end
  fun pad_opcode v =
    let
      val xs = padded_opcode v
      val (l,ty) = listSyntax.dest_list xs
    in
      if length l < 32 then mk_comb(``Half``,bitstringSyntax.mk_v2w (xs, i16))
                       else mk_comb(``Word``,bitstringSyntax.mk_v2w (xs, i32))
    end
in
  val padded_opcode = padded_opcode
  fun fetch v = let
    val vs = pad_opcode v
    val lemma = if can (match_term ``Word _``) vs
                then riscv_stepTheory.Fetch32 else riscv_stepTheory.Fetch16
    val bs = vs |> rand |> rand
    in lemma |> SPEC bs |> SIMP_RULE std_ss [listTheory.CONS_11]
             |> REWRITE_RULE [GSYM AND_IMP_INTRO] |> UNDISCH_ALL end
  val fetch_hex = fetch o bitstringSyntax.bitstring_of_hexstring
end

(* -------------------------------------------------------------------------
   Decode
   ------------------------------------------------------------------------- *)

local
  val Decode =
    riscvTheory.Decode_def
    |> Thm.SPEC (bitstringSyntax.mk_vec 32 0)
    |> Conv.RIGHT_CONV_RULE
         (REWRITE_CONV
            [riscvTheory.boolify32_v2w, asImm12_def, asImm20_def,
             asSImm12_def]
          THENC Conv.DEPTH_CONV PairedLambda.let_CONV
          THENC EVAL
         )
  val DecodeRVC =
    riscvTheory.DecodeRVC_def
    |> Thm.SPEC (bitstringSyntax.mk_vec 16 0)
    |> Conv.RIGHT_CONV_RULE
         (REWRITE_CONV [riscvTheory.boolify16_v2w]
          THENC Conv.DEPTH_CONV PairedLambda.let_CONV
          THENC EVAL
         )
  val v32 = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 32 0))
  val v16 = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 16 0))
in
  val get_opc = boolSyntax.rand o boolSyntax.rand o utilsLib.lhsc
  fun DecodeRISCV tm =
    let
      val (l,ty) = listSyntax.dest_list tm
    in
      if length l < 32 then
        DecodeRVC |> Thm.INST (fst (Term.match_term v16 tm)) |> REWRITE_RULE []
                  |> MATCH_MP DecodeRVC_IMP_DecodeAny |> UNDISCH
      else
        Decode |> Thm.INST (fst (Term.match_term v32 tm)) |> REWRITE_RULE []
               |> MATCH_MP Decode_IMP_DecodeAny
    end
end

fun make_nop (s, p) =
  (s ^ "_NOP",
   String.substring (p, 0, 20) ^ "FFFFF" ^ String.extract (p, 25, NONE))

fun find_all_rvc s =
  let
    val tm = utilsLib.pattern s
    val th = DecodeRISCV tm
    val tm = th |> concl |> rand
  in
    if not (is_cond tm) then [s] else let
      val (b,_,_) = dest_cond tm
      val v = hd (free_vars b |> rev)
      val index = dest_var v |> fst |> explode |> tl |> implode |> string_to_int
      fun flip_nth_underscore n [] = fail ()
        | flip_nth_underscore n (x::xs) =
             if x <> #"_" then let
               val (ys,zs) = flip_nth_underscore n xs
               in (x::ys,x::zs) end
             else if n = 0 then (#"F" :: xs, #"T" :: xs) else let
               val (ys,zs) = flip_nth_underscore (n-1) xs
               in (x::ys,x::zs) end
      val (s1,s2) = flip_nth_underscore index (explode s)
    in
      find_all_rvc (implode s1) @ find_all_rvc (implode s2)
    end
  end;

val rvc_pats = map (fn s => ("RVC_" ^ s, s))
  (find_all_rvc "______________TF" @
   find_all_rvc "______________FT" @
   find_all_rvc "______________FF")

val riscv_decodes =
  List.map (I ## (DecodeRISCV o utilsLib.pattern)) rvc_pats @
  List.map (I ## (DecodeRISCV o utilsLib.pattern))
  (let
     val l =
  [
   ("JALR",   "_________________FFF_____TTFFTTT"),
   ("JAL",    "_________________________TTFTTTT"),
   ("LUI",    "_________________________FTTFTTT"),
   ("AUIPC",  "_________________________FFTFTTT"),
   ("ADDI",   "_________________FFF_____FFTFFTT"),
   ("SLLI",   "FFFFFF___________FFT_____FFTFFTT"),
   ("SLTI",   "_________________FTF_____FFTFFTT"),
   ("SLTIU",  "_________________FTT_____FFTFFTT"),
   ("XORI",   "_________________TFF_____FFTFFTT"),
   ("SRLI",   "FFFFFF___________TFT_____FFTFFTT"),
   ("SRAI",   "FTFFFF___________TFT_____FFTFFTT"),
   ("ORI",    "_________________TTF_____FFTFFTT"),
   ("ANDI",   "_________________TTT_____FFTFFTT"),
   ("ADD",    "FFFFFFF__________FFF_____FTTFFTT"),
   ("SUB",    "FTFFFFF__________FFF_____FTTFFTT"),
   ("SLL",    "FFFFFFF__________FFT_____FTTFFTT"),
   ("SLT",    "FFFFFFF__________FTF_____FTTFFTT"),
   ("SLTU",   "FFFFFFF__________FTT_____FTTFFTT"),
   ("XOR",    "FFFFFFF__________TFF_____FTTFFTT"),
   ("SRL",    "FFFFFFF__________TFT_____FTTFFTT"),
   ("SRA",    "FTFFFFF__________TFT_____FTTFFTT"),
   ("OR",     "FFFFFFF__________TTF_____FTTFFTT"),
   ("AND",    "FFFFFFF__________TTT_____FTTFFTT"),
   ("ADDIW",  "_________________FFF_____FFTTFTT"),
   ("SLLIW",  "FFFFFFF__________FFT_____FFTTFTT"),
   ("SRLIW",  "FFFFFFF__________TFT_____FFTTFTT"),
   ("SRAIW",  "FTFFFFF__________TFT_____FFTTFTT"),
   ("ADDW",   "FFFFFFF__________FFF_____FTTTFTT"),
   ("SUBW",   "FTFFFFF__________FFF_____FTTTFTT"),
   ("SLLW",   "FFFFFFF__________FFT_____FTTTFTT"),
   ("SRLW",   "FFFFFFF__________TFT_____FTTTFTT"),
   ("SRAW",   "FTFFFFF__________TFT_____FTTTFTT"),
   ("MUL",    "FFFFFFT__________FFF_____FTTFFTT"),
   ("MULH",   "FFFFFFT__________FFT_____FTTFFTT"),
   ("MULHSU", "FFFFFFT__________FTF_____FTTFFTT"),
   ("MULHU",  "FFFFFFT__________FTT_____FTTFFTT"),
   ("DIV",    "FFFFFFT__________TFF_____FTTFFTT"),
   ("DIVU",   "FFFFFFT__________TFT_____FTTFFTT"),
   ("REM",    "FFFFFFT__________TTF_____FTTFFTT"),
   ("REMU",   "FFFFFFT__________TTT_____FTTFFTT"),
   ("MULW",   "FFFFFFT__________FFF_____FTTTFTT"),
   ("DIVW",   "FFFFFFT__________TFF_____FTTTFTT"),
   ("DIVUW",  "FFFFFFT__________TFT_____FTTTFTT"),
   ("REMW",   "FFFFFFT__________TTF_____FTTTFTT"),
   ("REMUW",  "FFFFFFT__________TTT_____FTTTFTT"),
   ("LB",     "_________________FFF_____FFFFFTT"),
   ("LH",     "_________________FFT_____FFFFFTT"),
   ("LW",     "_________________FTF_____FFFFFTT"),
   ("LD",     "_________________FTT_____FFFFFTT"),
   ("LBU",    "_________________TFF_____FFFFFTT"),
   ("LHU",    "_________________TFT_____FFFFFTT"),
   ("LWU",    "_________________TTF_____FFFFFTT"),
   (* CSR instructions: csr, rs1 or uimm, funct3, rd *)
   ("CSRRW",  "_________________FFT_____TTTFFTT"),
   ("CSRRS",  "_________________FTF_____TTTFFTT"),
   ("CSRRC",  "_________________FTT_____TTTFFTT"),
   ("CSRRWI", "_________________TFT_____TTTFFTT"),
   ("CSRRSI", "_________________TTF_____TTTFFTT"),
   ("CSRRCI", "_________________TTT_____TTTFFTT")
  ]
     (* Atomics and floating-point instructions that write rd *)
     val l2 =
  [
   ("LR_W",      "FFFTF__FFFFF_____FTF_____FTFTTTT"),
   ("LR_D",      "FFFTF__FFFFF_____FTT_____FTFTTTT"),
   ("SC_W",      "FFFTT____________FTF_____FTFTTTT"),
   ("SC_D",      "FFFTT____________FTT_____FTFTTTT"),
   ("AMOSWAP_W", "FFFFT____________FTF_____FTFTTTT"),
   ("AMOADD_W",  "FFFFF____________FTF_____FTFTTTT"),
   ("AMOXOR_W",  "FFTFF____________FTF_____FTFTTTT"),
   ("AMOAND_W",  "FTTFF____________FTF_____FTFTTTT"),
   ("AMOOR_W",   "FTFFF____________FTF_____FTFTTTT"),
   ("AMOMIN_W",  "TFFFF____________FTF_____FTFTTTT"),
   ("AMOMAX_W",  "TFTFF____________FTF_____FTFTTTT"),
   ("AMOMINU_W", "TTFFF____________FTF_____FTFTTTT"),
   ("AMOMAXU_W", "TTTFF____________FTF_____FTFTTTT"),
   ("AMOSWAP_D", "FFFFT____________FTT_____FTFTTTT"),
   ("AMOADD_D",  "FFFFF____________FTT_____FTFTTTT"),
   ("AMOXOR_D",  "FFTFF____________FTT_____FTFTTTT"),
   ("AMOAND_D",  "FTTFF____________FTT_____FTFTTTT"),
   ("AMOOR_D",   "FTFFF____________FTT_____FTFTTTT"),
   ("AMOMIN_D",  "TFFFF____________FTT_____FTFTTTT"),
   ("AMOMAX_D",  "TFTFF____________FTT_____FTFTTTT"),
   ("AMOMINU_D", "TTFFF____________FTT_____FTFTTTT"),
   ("AMOMAXU_D", "TTTFF____________FTT_____FTFTTTT"),
   ("FEQ_S",     "TFTFFFF__________FTF_____TFTFFTT"),
   ("FLT_S",     "TFTFFFF__________FFT_____TFTFFTT"),
   ("FLE_S",     "TFTFFFF__________FFF_____TFTFFTT"),
   ("FEQ_D",     "TFTFFFT__________FTF_____TFTFFTT"),
   ("FLT_D",     "TFTFFFT__________FFT_____TFTFFTT"),
   ("FLE_D",     "TFTFFFT__________FFF_____TFTFFTT"),
   ("FMV_X_S",   "TTTFFFFFFFFF_____FFF_____TFTFFTT"),
   ("FCLASS_S",  "TTTFFFFFFFFF_____FFT_____TFTFFTT"),
   ("FMV_X_D",   "TTTFFFTFFFFF_____FFF_____TFTFFTT"),
   ("FCLASS_D",  "TTTFFFTFFFFF_____FFT_____TFTFFTT"),
   ("FCVT_W_S",  "TTFFFFFFFFFF_____________TFTFFTT"),
   ("FCVT_WU_S", "TTFFFFFFFFFT_____________TFTFFTT"),
   ("FCVT_L_S",  "TTFFFFFFFFTF_____________TFTFFTT"),
   ("FCVT_LU_S", "TTFFFFFFFFTT_____________TFTFFTT"),
   ("FCVT_W_D",  "TTFFFFTFFFFF_____________TFTFFTT"),
   ("FCVT_WU_D", "TTFFFFTFFFFT_____________TFTFFTT"),
   ("FCVT_L_D",  "TTFFFFTFFFTF_____________TFTFFTT"),
   ("FCVT_LU_D", "TTFFFFTFFFTT_____________TFTFFTT")
  ]
   in
      l @ List.map make_nop l @ l2 @ List.map make_nop l2 @
  [
   ("SB",     "_________________FFF_____FTFFFTT"),
   ("SH",     "_________________FFT_____FTFFFTT"),
   ("SW",     "_________________FTF_____FTFFFTT"),
   ("SD",     "_________________FTT_____FTFFFTT"),
   ("BEQ",    "_________________FFF_____TTFFFTT"),
   ("BNE",    "_________________FFT_____TTFFFTT"),
   ("BLT",    "_________________TFF_____TTFFFTT"),
   ("BGE",    "_________________TFT_____TTFFFTT"),
   ("BLTU",   "_________________TTF_____TTFFFTT"),
   ("BGEU",   "_________________TTT_____TTFFFTT"),
   ("FENCE",      "_________________FFF_____FFFTTTT"),
   ("FENCE_I",    "_________________FFT_____FFFTTTT"),
   ("ECALL",      "FFFFFFFFFFFFFFFFFFFFFFFFFTTTFFTT"),
   ("EBREAK",     "FFFFFFFFFFFTFFFFFFFFFFFFFTTTFFTT"),
   ("MRET",       "FFTTFFFFFFTFFFFFFFFFFFFFFTTTFFTT"),
   ("WFI",        "FFFTFFFFFTFTFFFFFFFFFFFFFTTTFFTT"),
   ("SFENCE_VMA", "FFFTFFT__________FFFFFFFFTTTFFTT"),
   ("FLW",        "_________________FTF_____FFFFTTT"),
   ("FLD",        "_________________FTT_____FFFFTTT"),
   ("FSW",        "_________________FTF_____FTFFTTT"),
   ("FSD",        "_________________FTT_____FTFFTTT"),
   ("FMADD_S",    "_____FF__________________TFFFFTT"),
   ("FMSUB_S",    "_____FF__________________TFFFTTT"),
   ("FNMSUB_S",   "_____FF__________________TFFTFTT"),
   ("FNMADD_S",   "_____FF__________________TFFTTTT"),
   ("FMADD_D",    "_____FT__________________TFFFFTT"),
   ("FMSUB_D",    "_____FT__________________TFFFTTT"),
   ("FNMSUB_D",   "_____FT__________________TFFTFTT"),
   ("FNMADD_D",   "_____FT__________________TFFTTTT"),
   ("FADD_S",     "FFFFFFF__________________TFTFFTT"),
   ("FSUB_S",     "FFFFTFF__________________TFTFFTT"),
   ("FMUL_S",     "FFFTFFF__________________TFTFFTT"),
   ("FDIV_S",     "FFFTTFF__________________TFTFFTT"),
   ("FSQRT_S",    "FTFTTFFFFFFF_____________TFTFFTT"),
   ("FMIN_S",     "FFTFTFF__________FFF_____TFTFFTT"),
   ("FMAX_S",     "FFTFTFF__________FFT_____TFTFFTT"),
   ("FSGNJ_S",    "FFTFFFF__________FFF_____TFTFFTT"),
   ("FSGNJN_S",   "FFTFFFF__________FFT_____TFTFFTT"),
   ("FSGNJX_S",   "FFTFFFF__________FTF_____TFTFFTT"),
   ("FCVT_S_W",   "TTFTFFFFFFFF_____________TFTFFTT"),
   ("FCVT_S_WU",  "TTFTFFFFFFFT_____________TFTFFTT"),
   ("FCVT_S_L",   "TTFTFFFFFFTF_____________TFTFFTT"),
   ("FCVT_S_LU",  "TTFTFFFFFFTT_____________TFTFFTT"),
   ("FMV_S_X",    "TTTTFFFFFFFF_____FFF_____TFTFFTT"),
   ("FADD_D",     "FFFFFFT__________________TFTFFTT"),
   ("FSUB_D",     "FFFFTFT__________________TFTFFTT"),
   ("FMUL_D",     "FFFTFFT__________________TFTFFTT"),
   ("FDIV_D",     "FFFTTFT__________________TFTFFTT"),
   ("FSQRT_D",    "FTFTTFTFFFFF_____________TFTFFTT"),
   ("FMIN_D",     "FFTFTFT__________FFF_____TFTFFTT"),
   ("FMAX_D",     "FFTFTFT__________FFT_____TFTFFTT"),
   ("FSGNJ_D",    "FFTFFFT__________FFF_____TFTFFTT"),
   ("FSGNJN_D",   "FFTFFFT__________FFT_____TFTFFTT"),
   ("FSGNJX_D",   "FFTFFFT__________FTF_____TFTFFTT"),
   ("FCVT_D_W",   "TTFTFFTFFFFF_____________TFTFFTT"),
   ("FCVT_D_WU",  "TTFTFFTFFFFT_____________TFTFFTT"),
   ("FCVT_D_L",   "TTFTFFTFFFTF_____________TFTFFTT"),
   ("FCVT_D_LU",  "TTFTFFTFFFTT_____________TFTFFTT"),
   ("FMV_D_X",    "TTTTFFTFFFFF_____FFF_____TFTFFTT"),
   ("FCVT_S_D",   "FTFFFFFFFFFT_____________TFTFFTT"),
   ("FCVT_D_S",   "FTFFFFTFFFFF_____________TFTFFTT")
  ]
  end)

local
  val net =
    List.foldl (fn ((_, th), nt) => LVTermNet.insert (nt, ([], get_opc th), th))
      LVTermNet.empty riscv_decodes
in
  fun riscv_decode v =
    let
      val tm = padded_opcode v
    in
      case LVTermNet.match (net, tm) of
         [] => DecodeRISCV tm (* fallback *)
       | [(([], opc), th)] => Thm.INST (fst (Term.match_term opc tm)) th
       | [(([], opc), th), _] => Thm.INST (fst (Term.match_term opc tm)) th
       | _ => raise ERR "decode" (utilsLib.long_term_to_string v)
    end
  val riscv_decode_hex = riscv_decode o bitstringSyntax.bitstring_of_hexstring
  val riscv_dict = List.map (I ## (rand o get_opc)) riscv_decodes
end

(*
val thms = List.map (riscv_decode o snd) riscv_dict
*)

(* -------------------------------------------------------------------------
   Run
   ------------------------------------------------------------------------- *)

val STATE_CONV =
  Conv.QCONV
    (REWRITE_CONV
       ([ASSUME ``^s.exception = riscv$NoException``,
         ASSUME ``^s.c_NextFetch ^s.procID = NONE``,
         riscv_stepTheory.update_pc, updateTheory.UPDATE_EQ] @
        utilsLib.datatype_rewrites true "riscv" ["riscv_state"]))

val state_rule = Conv.RIGHT_CONV_RULE STATE_CONV
val full_state_rule = utilsLib.ALL_HYP_CONV_RULE STATE_CONV o state_rule



val fetch_inst =
  Thm.INST [] (* [s |-> snd (pairSyntax.dest_pair (utilsLib.rhsc (fetch ``[F]``)))] *)

local
  val rwts = List.map (full_state_rule o fetch_inst o DB.fetch "riscv_step")
               (valOf (utilsLib.get_rewrites{thyname="riscv_step"}))
  val fnd = utilsLib.find_rw (utilsLib.mk_rw_net utilsLib.lhsc rwts)
  (* Decide the tests on instruction fields that the instantiation has made
     ground: v2w l = n2w m (the rounding-mode field), and word_bit n (v2w l)
     (bit 5 of a shift amount). *)
  fun is_ground_v2w tm =
    bitstringSyntax.is_v2w tm andalso List.null (Term.free_vars tm)
  fun field_conv tm =
    case Lib.total boolSyntax.dest_eq tm of
       SOME (l, r) =>
         if is_ground_v2w l andalso wordsSyntax.is_n2w r then
           (Conv.LAND_CONV bitstringLib.v2w_n2w_CONV
            THENC wordsLib.word_EQ_CONV) tm
         else raise ERR "field_conv" ""
     | NONE =>
         (case Lib.total wordsSyntax.dest_word_bit tm of
             SOME (n, w) =>
               if is_ground_v2w w andalso numSyntax.is_numeral n then
                 (Conv.RAND_CONV bitstringLib.v2w_n2w_CONV
                  THENC wordsLib.WORD_EVAL_CONV) tm
               else raise ERR "field_conv" ""
           | NONE => raise ERR "field_conv" "")
  val rule = Conv.DEPTH_CONV (wordsLib.word_EQ_CONV ORELSEC field_conv)
             THENC REWRITE_CONV [riscv_stepTheory.v2w_0_rwts,
                                 riscv_stepTheory.frm_rounding_v2w]
  val eval_simp_rule =
    utilsLib.ALL_HYP_CONV_RULE rule o Conv.CONV_RULE (Conv.RHS_CONV rule)
  fun eval tm rwt =
    let
      val thm = eval_simp_rule (utilsLib.INST_REWRITE_CONV1 rwt tm)
    in
      if utilsLib.vacuous thm then NONE else SOME thm
    end
  val neg_count = List.length o List.filter boolSyntax.is_neg o Thm.hyp
  fun err tm s = ( Parse.print_term tm; print "\n"; raise ERR "run" s )
in
  fun run tm =
    (case List.mapPartial (eval tm) (fnd tm) of
        [] => err tm "no valid step theorem"
      | [x] => x
      | l => List.last (mlibUseful.sort_map neg_count Int.compare l))
    handle (e as HOL_ERR herr) =>
      if message_of herr = "not found" andalso
         top_function_of herr = "find_rw"
      then
         err tm "instruction instance not supported"
      else raise e
end

(* -------------------------------------------------------------------------
   C extension
   ------------------------------------------------------------------------- *)

val rvc_tm = ``(^s.c_MCSR ^s.procID).misa.C``

(* H6 *)
val no_interrupt = ``~(^s.c_MCSR ^s.procID).mstatus.MIE``

(* The M-mode contract H1-H4 and H6 (riscv_stepTheory), as the word-level
   conjuncts that the step theorems carry. *)
val contract_hyps =
  let
    val mcsr = ``^s.c_MCSR ^s.procID``
    fun conjs th = boolSyntax.strip_conj (utilsLib.rhsc (Thm.SPEC mcsr th))
  in
    [``^s.c_privilege ^s.procID = 3w``, ``~^mcsr.mstatus.MPRV``,
     no_interrupt] @
    conjs riscv_stepTheory.pmp_unlocked_def @
    conjs riscv_stepTheory.pmp_off_or_napot_def
  end

(* tidy_up_signalAddressException simplifies the hypotheses of the
   instruction theorem with srw_ss, which reorders the operands of the PMP
   conjuncts; the fetch theorem has them as written.  Put them back, so
   that each conjunct is a hypothesis once and in the form above. *)
local
  fun norm c =
    let
      val eq = Conv.QCONV (SIMP_CONV (srw_ss()) []) c
    in
      if Term.aconv (utilsLib.rhsc eq) c then NONE
      else SOME (utilsLib.rhsc eq, EQ_MP eq (Thm.ASSUME c))
    end
  val normal_forms = List.mapPartial norm contract_hyps
in
  fun canonical_contract_rule th =
    List.foldl
      (fn ((c', th'), th) =>
         if HOLset.member (Thm.hypset th, c') then PROVE_HYP th' th else th)
      th normal_forms
end

(* A hypothesis without free variables, such as the alignment of an address
   given by x0 and an offset, is decided: it is removed if true, and if it
   is false the instruction traps (here, on a misaligned access) and there
   is no step theorem.  So is a disjunct without free variables, such as
   the test of bit 1 of a jump target given by x0 and an offset in
   ~word_bit 1 target \/ misa.C: the hypothesis becomes misa.C if the
   test is false, and is removed if it is true. *)
local
  fun closed tm = List.null (Term.free_vars tm)
  fun decide tm =
    let
      val eq = EVAL tm
    in
      if Teq (utilsLib.rhsc eq) orelse Feq (utilsLib.rhsc eq) then eq
      else raise Conv.UNCHANGED
    end
  fun disj_conv tm =
    if closed tm then decide tm
    else if boolSyntax.is_disj tm then Conv.BINOP_CONV disj_conv tm
    else raise Conv.UNCHANGED
  val or_clauses = Conv.QCONV (PURE_REWRITE_CONV [boolTheory.OR_CLAUSES])
  fun hyp_conv tm = Conv.RIGHT_CONV_RULE or_clauses (disj_conv tm)
in
  fun ground_hyp_rule th =
    List.foldl
      (fn (h, th) =>
         case Lib.total hyp_conv h of
            NONE => th
          | SOME eq =>
              let
                val h' = utilsLib.rhsc eq
              in
                if Teq h' then PROVE_HYP (EQ_MP (SYM eq) TRUTH) th
                else if Feq h' then
                  raise ERR "riscv_step"
                    ("instruction traps: " ^ Parse.term_to_string h ^
                     " is false")
                else PROVE_HYP (EQ_MP (SYM eq) (ASSUME h')) th
              end) th (Thm.hyp th)
end

local
  val st = Term.mk_var ("st", ``:riscv_state``)
  val rvc_pat = ``(^st.c_MCSR ^st.procID).misa.C``
  fun rvc_terms th =
    Lib.op_mk_set aconv
      (List.concat
         (List.map (HolKernel.find_terms (Lib.can (Term.match_term rvc_pat)))
            (Thm.hyp th)))
  fun hyp_rule msg cs rwts th =
    List.foldl
      (fn (h, th) =>
         if List.exists (fn c => Term.free_in c h) cs then
           let
             val eq = Conv.QCONV (REWRITE_CONV rwts) h
             val h' = utilsLib.rhsc eq
           in
             if Feq h' then raise ERR "riscv_rvc_rule" msg
             else if Teq h' then PROVE_HYP (EQ_MP (SYM eq) TRUTH) th
             else PROVE_HYP (EQ_MP (SYM eq) (ASSUME h')) th
           end
         else th) th (Thm.hyp th)
in
  fun riscv_rvc_rule b th =
    let
      val cs = rvc_terms th
      val rwts = List.map (fn c => ASSUME (if b then c else mk_neg c)) cs
      val msg = if b then "requires the C extension to be disabled"
                else "requires the C extension"
    in
      hyp_rule msg cs rwts th
    end
end

(* -------------------------------------------------------------------------
   CSR instructions

   The step theorems of the CSR instructions (riscv_stepTheory) are for any
   CSR number; csr_rule evaluates them for the CSR number of the
   instruction: the read (CSRMap), the write (writeCSR, with the
   legalisation of the written value in write'CSRMap, and the log of the
   value read back), and the access conditions, which are hypotheses:
   is_CSR_defined and, for a write, that the CSR is not read-only are
   decided (an instruction that fails them is illegal and has no step
   theorem here), and check_CSR_conditions becomes mstatus.FS <> Off for
   fflags, frm and fcsr and is true for every other CSR in M-mode.  The
   locks of the PMP entries (pmpcfg0/2, pmpaddr0-15) are decided by H3, a
   hypothesis of every step theorem: no entry is locked, so a write of
   pmpaddr<i> is never ignored, and the legalised value of pmpcfg0/2 does
   not depend on the old one (riscv_stepTheory.legalize_pmpcfg_unlocked).
   ------------------------------------------------------------------------- *)

local
  val csr_ty = wordsSyntax.mk_int_word_type 12
  fun closed tm = List.null (Term.free_vars tm)
  val csr_number_conv =
    Conv.DEPTH_CONV
      (fn tm =>
         if bitstringSyntax.is_v2w tm andalso Term.type_of tm = csr_ty andalso
            closed tm
           then bitstringLib.v2w_n2w_CONV tm
         else raise Conv.UNCHANGED)
  (* the closed hypotheses of a CSR step theorem: existence and
     writability of the CSR *)
  val is_CSR_defined_tm = ``riscv$is_CSR_defined``
  fun is_access_hyp h =
    case Lib.total Term.dest_comb h of
       SOME (f, _) => Term.same_const f is_CSR_defined_tm
     | NONE => false
  val writable_pat = ``~((11 >< 10) (c: word12) = 3w: word2)``
  fun is_writable_hyp h = Lib.can (Term.match_term writable_pat) h
  (* the CSR number of an instruction must be known *)
  fun csr_number_of th =
    case List.find (fn h => is_access_hyp h orelse is_writable_hyp h)
           (Thm.hyp th) of
       SOME h =>
         if closed h then ()
         else raise ERR "riscv_step"
                "the CSR number of a CSR instruction must be a constant"
     | NONE => raise ERR "riscv_step" "not a CSR step theorem"
  fun decide_access_rule th =
    List.foldl
      (fn (h, th) =>
         if (is_access_hyp h orelse is_writable_hyp h) andalso closed h then
           let
             val eq =
               (csr_number_conv
                THENC PURE_REWRITE_CONV [is_CSR_defined_def]
                THENC EVAL) h
             val r = utilsLib.rhsc eq
           in
             if Teq r then PROVE_HYP (EQT_ELIM eq) th
             else if Feq r then
               raise ERR "riscv_step"
                 ("instruction traps: " ^ Parse.term_to_string h ^ " is false")
             else raise ERR "riscv_step"
                    ("cannot decide " ^ Parse.term_to_string h)
           end
         else th) th (Thm.hyp th)
  val record_rwts =
    utilsLib.datatype_rewrites true "riscv"
      ["riscv_state", "MachineCSR", "SupervisorCSR", "UserCSR",
       "StateDelta", "mstatus", "misa", "mie", "mip", "mcause", "FPCSR",
       "Privilege", "ExtStatus"] @
    [combinTheory.UPDATE_EQ, combinTheory.APPLY_UPDATE_THM]
  val word_eq_ss =
    simpLib.std_conv_ss
      {name = "word_eq", conv = wordsLib.word_EQ_CONV,
       pats = [``n2w a = n2w b: 'a word``]}
  (* a conditional update, such as the write of sip when mideleg delegates
     SSI, as an update with a conditional value *)
  val cond_updates =
    utilsLib.mk_cond_update_thms
      [``:riscv_state``, ``:MachineCSR``, ``:SupervisorCSR``, ``:UserCSR``,
       ``:mstatus``, ``:mip``, ``:StateDelta``]
  val csr_ss =
    std_ss ++ simpLib.rewrites (record_rwts @ cond_updates) ++ word_eq_ss
  (* H3, by which no PMP entry is locked *)
  val h3 =
    List.map Thm.ASSUME
      (boolSyntax.strip_conj
         (utilsLib.rhsc (Thm.SPEC ``^s.c_MCSR ^s.procID``
                           riscv_stepTheory.pmp_unlocked_def)))
  val pmpcfg_ent_unlocked =
    REWRITE_RULE [riscv_stepTheory.pmp_unlocked_def]
      riscv_stepTheory.pmpcfg_ent_unlocked
  (* CSRMap and write'CSRMap for one CSR number k: the case of their
     definitions reduced to the branch of k, computed once for each k.  The
     compset has only these and the equality of word literals, so that the
     branch is left as it is (the words compset would, for one, expand the
     bit_field_insert of a write of fflags). *)
  val csr_cmp =
    computeLib.add_conv
      (``$= : 'a word -> 'a word -> bool``, 2, bitstringLib.word_eq_CONV)
      (computeLib.add_thms [CSRMap_def, write'CSRMap_def]
         (computeLib.copy computeLib.bool_compset))
  val instances = ref (Redblackmap.mkDict Arbnum.compare)
  fun csr_instances k =
    case Redblackmap.peek (!instances, k) of
       SOME thms => thms
     | NONE =>
         let
           val c = wordsSyntax.mk_n2w (numSyntax.mk_numeral k, ``:12``)
           val v = Term.mk_var ("v", ``:word64``)
           fun inst tm =
             Drule.GEN_ALL (computeLib.CBV_CONV csr_cmp (Term.mk_comb (tm, s)))
           val thms =
             [inst ``riscv$CSRMap ^c``, inst ``riscv$write'CSRMap (^v, ^c)``]
         in
           instances := Redblackmap.insert (!instances, k, thms)
           ; thms
         end
  fun csr_numbers tm =
    List.map (wordsSyntax.dest_mod_word_literal)
      (HolKernel.find_terms
         (fn t => wordsSyntax.is_word_literal t andalso
                  Term.type_of t = csr_ty) tm)
  val csr_defs =
    [CSR_def, write'CSR_def, writeCSR_def,
     Delta_def, write'Delta_def, MCSR_def, write'MCSR_def, SCSR_def,
     write'SCSR_def, check_CSR_conditions_def, fpEnabled_def,
     counterReadAllowed_def, ext_status_def, is_mhpm_CSR_def,
     legalize_mstatus_def, legalize_sstatus_def, legalize_misa_def,
     legalize_xtvec_def, legalize_xepc_def, legalize_mcause_def,
     legalize_scause_def, legalize_satp_def, write_pmpaddr_def,
     read_mstatus_def, read_sstatus_def, read_xepc_def, haveRVC_def,
     riscv_stepTheory.read_mip_eval, mtime_def, mtimecmp_def, msip_def,
     MEM_def,
     CLINT_BASE_def, MSTATUS_WMASK_def, MSTATUS_CONST_def, MSTATUS_SD_def,
     SSTATUS_MASK_def, write'reg'FPCSR_def, boolTheory.literal_case_THM,
     boolTheory.LET_THM, pairTheory.UNCURRY_DEF,
     riscv_stepTheory.legalize_pmpcfg_unlocked, pmpcfg_ent_unlocked,
     riscv_stepTheory.reg_rec_id, riscv_stepTheory.reg'mip_updates,
     riscv_stepTheory.fflags_insert, riscv_stepTheory.mtimecmp_address] @ h3
  (* again after the ground terms are evaluated, which can make them apply:
     the address of mtimecmp is known only then *)
  val csr_values =
    [riscv_stepTheory.reg_rec_id, riscv_stepTheory.reg'mip_updates,
     riscv_stepTheory.mtimecmp_address]
  (* Ground words and booleans are evaluated, to numerals, but not the
     register numbers (v2w), which stay as in the other step theorems. *)
  val v2w_conv = Conv.DEPTH_CONV bitstringLib.v2w_n2w_CONV
  fun ground_conv tm =
    if closed tm then
      if bitstringSyntax.is_v2w tm then raise Conv.UNCHANGED
      else
        let
          val ty = Term.type_of tm
        in
          if wordsSyntax.is_word_type ty orelse ty = Type.bool then
            let
              val th = Conv.QCONV (v2w_conv THENC EVAL) tm
            in
              if Term.aconv (utilsLib.rhsc th) tm then raise Conv.UNCHANGED
              else th
            end
          else Conv.SUB_CONV ground_conv tm
        end
    else Conv.SUB_CONV ground_conv tm
  fun csr_conv tm =
    let
      val th1 = Conv.QCONV csr_number_conv tm
      val tm1 = utilsLib.rhsc th1
      val ks = Lib.mk_set (List.map fst (csr_numbers tm1))
      val rwts = List.concat (List.map csr_instances ks)
    in
      Thm.TRANS th1
        (Conv.QCONV
           (SIMP_CONV csr_ss (rwts @ csr_defs)
            THENC Conv.TRY_CONV ground_conv
            THENC SIMP_CONV csr_ss csr_values) tm1)
    end
in
  val csr_inst_names =
    ["CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI", "CSRRCI"]
  (* The left-hand side, the instruction as riscv_step built it, is kept. *)
  fun csr_rule th =
    ( csr_number_of th
    ; th |> decide_access_rule
         |> utilsLib.ALL_HYP_CONV_RULE csr_conv
         |> Conv.RIGHT_CONV_RULE csr_conv )
end

(* -------------------------------------------------------------------------
   Evaluator
   ------------------------------------------------------------------------- *)

local
  fun mkselnm ty f = TypeBasePure.mk_recordtype_fieldsel{tyname=ty,fieldname=f}
  fun mk_proj s =
    Lib.curry Term.mk_comb
      (Term.prim_mk_const {Thy = "riscv", Name = mkselnm "riscv_state" s})
  fun proj f = STATE_CONV o f o utilsLib.rhsc
  val proj_exception = proj (mk_proj "exception")
  val proj_NextFetch = mk_proj "c_NextFetch"
  val proj_procID = mk_proj "procID"
  val proj_NextFetch_procID =
    proj (fn tm => Term.mk_comb (proj_NextFetch tm, proj_procID tm))
  val ap_snd = Thm.AP_TERM ``SND: unit # riscv_state -> riscv_state``
  val snd_conv = Conv.REWR_CONV pairTheory.SND
  fun spec_run thm3 ethm =
    Conv.RIGHT_CONV_RULE
      (Conv.RAND_CONV (Conv.REWR_CONV ethm) THENC snd_conv) (ap_snd thm3)
  fun next th = PURE_REWRITE_RULE [word_bit_0_lemmas] o state_rule o Drule.MATCH_MP th
  val MP_Next_n = next riscv_stepTheory.NextRISCV
  val MP_Next_c = next riscv_stepTheory.NextRISCV_cond_branch
  val MP_Next_b = next riscv_stepTheory.NextRISCV_branch
  val MP_Next_mret = next riscv_stepTheory.NextRISCV_mret
  (* NextRISCV_trap with its last antecedent, that the trap is not
     delegated, apart: in M-mode (H1) it holds whatever medeleg is. *)
  val NextRISCV_trap =
    let
      val th = Drule.SPEC_ALL riscv_stepTheory.NextRISCV_trap
      val cs = boolSyntax.strip_conj (fst (boolSyntax.dest_imp (Thm.concl th)))
      val a5 = boolSyntax.list_mk_conj (List.take (cs, 5))
      val a6 = List.last cs
    in
      Thm.DISCH a5
        (Thm.DISCH a6
           (Thm.MP th (Drule.LIST_CONJ
                         (Drule.CONJUNCTS (Thm.ASSUME a5) @ [Thm.ASSUME a6]))))
    end
  val h1 = ``^s.c_privilege ^s.procID = 3w``
  val not_delegated_conv =
    STATE_CONV THENC REWRITE_CONV [Thm.ASSUME h1]
  (* The cause, the trap value and the privilege that the trap is taken
     from (MPP), for the trap of the instruction: M-mode by H1. *)
  val trap_conv =
    let
      val rwts =
        utilsLib.datatype_rewrites true "riscv"
          ["riscv_state", "SynchronousTrap", "ExceptionType"]
      val word_eq_ss =
        simpLib.std_conv_ss
          {name = "word_eq", conv = wordsLib.word_EQ_CONV,
           pats = [``n2w a = n2w b: 'a word``]}
    in
      SIMP_CONV (std_ss ++ simpLib.rewrites rwts ++ word_eq_ss)
        [Thm.ASSUME h1, excCode_def, riscv_stepTheory.rawInstBits_def]
      THENC Conv.DEPTH_CONV
              (fn tm => if wordsSyntax.is_w2w tm andalso
                           List.null (Term.free_vars tm)
                          then wordsLib.WORD_GROUND_CONV tm
                        else raise Conv.UNCHANGED)
    end
  fun MP_Next_trap thm =
    let
      val th = Drule.MATCH_MP NextRISCV_trap thm
      val not_delegated =
        EQT_ELIM (not_delegated_conv (fst (boolSyntax.dest_imp (Thm.concl th))))
    in
      Thm.MP th not_delegated
      |> state_rule
      |> Conv.RIGHT_CONV_RULE trap_conv
    end
  val Mret_tm = ``riscv$Mret``
  val Trap_tm = ``riscv$Trap``
  fun is_csr_inst thm2 =
    case boolSyntax.strip_comb (utilsLib.rhsc thm2) of
       (c, [a]) =>
         Term.is_const c andalso fst (Term.dest_const c) = "System" andalso
         (case Lib.total (Term.dest_const o fst o boolSyntax.strip_comb) a of
             SOME (n, _) => Lib.mem n csr_inst_names
           | NONE => false)
     | _ => false
  val Run_CONV = utilsLib.Run_CONV ("riscv", s) o utilsLib.rhsc
  val inst_rvc = Thm.INST [Term.mk_var ("rvc", Type.bool) |-> rvc_tm]
  fun tidy_up_rvc th =
    if tmem rvc_tm (Thm.hyp th) then riscv_rvc_rule true th else th
  fun tidy_up_signalAddressException th =
    let
      val rw = UNDISCH avoid_signalAddressException
      fun FORCE_REWR_CONV rw tm =
        let
          val (p,_) = match_term (rw |> concl |> rator |> rand) tm
        in INST p rw end handle HOL_ERR _ => NO_CONV tm;
    in
      CONV_RULE (DEPTH_CONV (FORCE_REWR_CONV rw)) th
      |> DISCH_ALL |> SIMP_RULE std_ss [word_bit_add_lsl_simp]
      |> SIMP_RULE (srw_ss ()) [] |> UNDISCH_ALL
    end
in
  fun riscv_step v =
    let
      val thm1 = fetch v
      val thm2 = riscv_decode v |> SIMP_RULE std_ss [] |> inst_rvc
      val new_s = thm1 |> concl |> rand |> rand
      val thm3 = fetch_inst (Drule.SPEC_ALL (Run_CONV thm2)) |> INST [s |-> new_s]
      val tm = utilsLib.rhsc thm3
      val thm4 =
        if Term.aconv tm new_s then
          thm3 (* FENCE and FENCE.I: Run does nothing *)
        else
          let
            val ethm = run tm
            val ethm = if is_csr_inst thm2 then csr_rule ethm else ethm
            val ethm = tidy_up_signalAddressException ethm
          in
            Conv.RIGHT_CONV_RULE (Conv.REWR_CONV ethm) thm3
          end
      val thm5 = proj_exception thm4
      val thm6 = proj_NextFetch_procID thm4
      val thm = Drule.LIST_CONJ [thm1, thm2, thm4, thm5, thm6]
      val tm = utilsLib.rhsc thm6
    in
      (* H6: NextRISCV takes no interrupt, so its step is one of the spec's
         Next only if no interrupt can be taken; in M-mode that holds when
         mstatus.MIE is clear (riscv_stepTheory.checkInterrupts_Machine).
         The equation itself does not depend on it.  tidy_up_rvc runs again
         after ground_hyp_rule, which can leave misa.C as a hypothesis (a
         jump to a constant target with bit 1 set), to drop the hypotheses
         that misa.C implies. *)
      (Drule.ADD_ASSUM no_interrupt o tidy_up_rvc o ground_hyp_rule o
       canonical_contract_rule)
        (tidy_up_rvc
           (* by NextFetch after the instruction: it falls through (NONE),
              branches (BranchTo, or a test of it), returns from a trap
              (Mret, NextRISCV_mret) or raises one (Trap, NextRISCV_trap) *)
           (if optionSyntax.is_none tm
              then MP_Next_n thm
            else if boolSyntax.is_cond tm
              then MP_Next_c thm
            else
              let
                val nf = optionSyntax.dest_some tm
              in
                if Term.aconv nf Mret_tm then MP_Next_mret thm
                else if Term.same_const Trap_tm (fst (boolSyntax.strip_comb nf))
                  then MP_Next_trap thm
                else MP_Next_b thm
              end))
    end
end

val riscv_step_hex = riscv_step o bitstringSyntax.bitstring_of_hexstring

val hex_to_padded_opcode =
  padded_opcode o bitstringSyntax.bitstring_of_hexstring

(* ========================================================================= *)

(* Testing
fun find_opc n = Lib.assoc n riscv_dict
val v = find_opc "BEQ"
val v = find_opc "JAL"
val v = find_opc "ADDI"
val v = bitstringSyntax.bitstring_of_hexstring "B3"
val thms = List.map (Count.apply riscv_step o snd) riscv_dict

val v = (v |> rand)
val th = riscv_step v

val v = bitstringSyntax.bitstring_of_hexstring "56fd"
val th = riscv_step v

filter (not o can (riscv_step o bitstringSyntax.bitstring_of_hexstring)) vs

open riscv_stepLib
*)

end
