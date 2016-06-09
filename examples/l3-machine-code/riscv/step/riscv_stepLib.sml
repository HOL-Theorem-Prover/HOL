(* ------------------------------------------------------------------------
   RISCV step evaluator
   ------------------------------------------------------------------------ *)

structure riscv_stepLib :> riscv_stepLib =
struct

open HolKernel boolLib bossLib
open blastLib riscvTheory riscv_stepTheory

structure Parse = struct
  open Parse
  val (Type, Term) = parse_from_grammars riscv_stepTheory.riscv_step_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "riscv_stepLib"

val () = show_assums := true

val s = ``s:riscv_state``

(* -------------------------------------------------------------------------
   Fetch
   ------------------------------------------------------------------------- *)

local
  val i32 = fcpSyntax.mk_int_numeric_type 32
  val x = Term.mk_var ("x", wordsSyntax.mk_int_word_type 32)
  fun padded_opcode v =
    let
      val (l, ty) = listSyntax.dest_list v
      val () = ignore (ty = Type.bool andalso List.length l <= 32 orelse
               raise ERR "mk_opcode" "bad opcode")
    in
      listSyntax.mk_list (utilsLib.padLeft boolSyntax.F 32 l, ty)
    end
  fun pad_opcode v = bitstringSyntax.mk_v2w (padded_opcode v, i32)
  val opc = riscv_stepTheory.Fetch
            |> utilsLib.rhsc
            |> pairSyntax.dest_pair |> fst
  val Fetch = REWRITE_RULE [ASSUME ``^opc = ^x``] riscv_stepTheory.Fetch
in
  val padded_opcode = padded_opcode
  fun fetch v = Thm.INST [x |-> pad_opcode v] Fetch
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
  val v = fst (bitstringSyntax.dest_v2w (bitstringSyntax.mk_vec 32 0))
in
  val get_opc = boolSyntax.rand o boolSyntax.rand o utilsLib.lhsc
  fun DecodeMIPS tm =
    Decode |> Thm.INST (fst (Term.match_term v tm)) |> REWRITE_RULE []
end

fun make_nop (s, p) =
  (s ^ "_NOP",
   String.substring (p, 0, 20) ^ "FFFFF" ^ String.extract (p, 25, NONE))


val riscv_decodes = List.map (I ## (DecodeMIPS o utilsLib.pattern))
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
   ("LWU",    "_________________TTF_____FFFFFTT")
  ]
   in
      l @ List.map make_nop l @
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
   ("BGEU",   "_________________TTT_____TTFFFTT")
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
         [] => DecodeMIPS tm (* fallback *)
       | [(([], opc), th)] => Thm.INST (fst (Term.match_term opc tm)) th
       | [(([], opc), th), _] => Thm.INST (fst (Term.match_term opc tm)) th
       | _ => raise ERR "decode" (utilsLib.long_term_to_string v)
    end
  val riscv_decode_hex = riscv_decode o bitstringSyntax.bitstring_of_hexstring
  val riscv_dict = List.map (I ## get_opc) riscv_decodes
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
  Thm.INST [s |-> snd (pairSyntax.dest_pair (utilsLib.rhsc (fetch ``[F]``)))]

local
  val rwts = List.map (full_state_rule o fetch_inst o DB.fetch "riscv_step")
               riscv_stepTheory.rwts
  val fnd = utilsLib.find_rw (utilsLib.mk_rw_net utilsLib.lhsc rwts)
  val rule = Conv.DEPTH_CONV wordsLib.word_EQ_CONV
             THENC REWRITE_CONV [riscv_stepTheory.v2w_0_rwts]
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
    handle HOL_ERR {message = "not found", origin_function = "find_rw", ...} =>
      err tm "instruction instance not supported"
end

(* -------------------------------------------------------------------------
   Evaluator
   ------------------------------------------------------------------------- *)

local
  fun mk_proj s =
    Lib.curry Term.mk_comb
      (Term.prim_mk_const {Thy = "riscv", Name = "riscv_state_" ^ s})
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
  fun next th = state_rule o Drule.MATCH_MP th
  val MP_Next_n = next riscv_stepTheory.NextRISCV
  val MP_Next_c = next riscv_stepTheory.NextRISCV_cond_branch
  val MP_Next_b = next riscv_stepTheory.NextRISCV_branch
  val Run_CONV = utilsLib.Run_CONV ("riscv", s) o utilsLib.rhsc
in
  fun riscv_step v =
    let
      val thm1 = fetch v
      val thm2 = riscv_decode v
      val thm3 = fetch_inst (Drule.SPEC_ALL (Run_CONV thm2))
      val tm = utilsLib.rhsc thm3
      val ethm = run tm
      val thm4 = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV ethm) thm3
      val thm5 = proj_exception thm4
      val thm6 = proj_NextFetch_procID thm4
      val thm = Drule.LIST_CONJ [thm1, thm2, thm4, thm5, thm6]
      val tm = utilsLib.rhsc thm6
    in
      if optionSyntax.is_none tm
        then MP_Next_n thm
      else if boolSyntax.is_cond tm
        then MP_Next_c thm
      else MP_Next_b thm
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

open riscv_stepLib
*)

end
