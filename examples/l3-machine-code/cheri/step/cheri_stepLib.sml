(* ------------------------------------------------------------------------
   CHERI step evaluator
   ------------------------------------------------------------------------ *)

structure cheri_stepLib :> cheri_stepLib =
struct

open HolKernel boolLib bossLib
open blastLib cheriTheory cheri_stepTheory

val ERR = Feedback.mk_HOL_ERR "cheri_stepLib"

val () = show_assums := true

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars cheri_step_grammars
end
open Parse


(* ------------------------------------------------------------------------- *)

(* Fetch *)

local
   val ty32 = fcpSyntax.mk_int_numeric_type 32
   val w = Term.mk_var ("w", wordsSyntax.mk_int_word_type 32)
   fun mk_opc l =
     let
       val (b1, l) = Lib.split_after 8 l
       val (b2, l) = Lib.split_after 8 l
       val (b3, b4) = Lib.split_after 8 l
     in
       bitstringSyntax.mk_v2w
         (listSyntax.mk_list (b1 @ b2 @ b3 @ b4, Type.bool), ty32)
     end
in
   fun pad_opcode v =
      let
         val (l, ty) = listSyntax.dest_list v
      in
         General.ignore (ty = Type.bool andalso List.length l <= 32 orelse
         raise ERR "pad_opcode" "bad opcode")
       ; utilsLib.padLeft boolSyntax.F 32 l
      end
   fun fetch v =
     Thm.INST [w |-> mk_opc (pad_opcode v)] cheri_stepTheory.Fetch_default
   val fetch_hex = fetch o bitstringSyntax.bitstring_of_hexstring
end

(* ------------------------------------------------------------------------- *)

(* Decoder *)

local
   val v = bitstringSyntax.mk_vec 32 0
   val Decode =
      Decode_def
      |> Thm.SPEC v
      |> Conv.RIGHT_CONV_RULE
             (
              REWRITE_CONV [cheriTheory.boolify32_v2w]
              THENC Conv.DEPTH_CONV PairedLambda.let_CONV
              THENC Conv.DEPTH_CONV bitstringLib.extract_v2w_CONV
             )
   val v = fst (bitstringSyntax.dest_v2w v)
   val unpredictable_tm = ``cheri$Unpredictable``
   fun fix_unpredictable thm =
      let
         val thm = REWRITE_RULE [not31] thm
      in
         case Lib.total (boolSyntax.dest_cond o utilsLib.rhsc) thm of
            SOME (b, t, _) =>
               if t ~~ unpredictable_tm
                  then REWRITE_RULE [ASSUME (boolSyntax.mk_neg b)] thm
               else thm
          | _ => thm
      end
in
   fun DecodeCHERI pat =
      let
         val s = fst (Term.match_term v pat)
      in
         Decode |> Thm.INST s
                |> REWRITE_RULE []
                |> Conv.RIGHT_CONV_RULE (Conv.REPEATC PairedLambda.let_CONV)
                |> fix_unpredictable
      end
end

val cheri_ipatterns = List.map (I ## utilsLib.pattern)
   [
    ("ADDI",   "FFTFFF__________________________"),
    ("ADDIU",  "FFTFFT__________________________"),
    ("SLTI",   "FFTFTF__________________________"),
    ("SLTIU",  "FFTFTT__________________________"),
    ("ANDI",   "FFTTFF__________________________"),
    ("ORI",    "FFTTFT__________________________"),
    ("XORI",   "FFTTTF__________________________"),
    ("DADDI",  "FTTFFF__________________________"),
    ("DADDIU", "FTTFFT__________________________"),
    ("MULT",   "FFFFFF__________FFFFFFFFFFFTTFFF"),
    ("MULTU",  "FFFFFF__________FFFFFFFFFFFTTFFT"),
    ("DMULT",  "FFFFFF__________FFFFFFFFFFFTTTFF"),
    ("DMULTU", "FFFFFF__________FFFFFFFFFFFTTTFT"),
    ("MADD",   "FTTTFF__________FFFFFFFFFFFFFFFF"),
    ("MADDU",  "FTTTFF__________FFFFFFFFFFFFFFFT"),
    ("MSUB",   "FTTTFF__________FFFFFFFFFFFFFTFF"),
    ("MSUBU",  "FTTTFF__________FFFFFFFFFFFFFTFT"),
    ("MUL",    "FTTTFF_______________FFFFFFFFFTF"),
    ("BEQ",    "FFFTFF__________________________"),
    ("BNE",    "FFFTFT__________________________"),
    ("BEQL",   "FTFTFF__________________________"),
    ("BNEL",   "FTFTFT__________________________")
   ]

val cheri_dpatterns = List.map (I ## utilsLib.pattern)
   [
    ("JALR",   "FFFFFF_____FFFFF__________FFTFFT")
   ]

val cheri_rpatterns = List.map (I ## utilsLib.pattern)
   [
    ("SLLV",   "FFFFFF_______________FFFFFFFFTFF"),
    ("SRLV",   "FFFFFF_______________FFFFFFFFTTF"),
    ("SRAV",   "FFFFFF_______________FFFFFFFFTTT"),
    ("MOVZ",   "FFFFFF_______________FFFFFFFTFTF"),
    ("MOVN",   "FFFFFF_______________FFFFFFFTFTT"),
    ("DSLLV",  "FFFFFF_______________FFFFFFTFTFF"),
    ("DSRLV",  "FFFFFF_______________FFFFFFTFTTF"),
    ("DSRAV",  "FFFFFF_______________FFFFFFTFTTT"),
    ("ADD",    "FFFFFF_______________FFFFFTFFFFF"),
    ("ADDU",   "FFFFFF_______________FFFFFTFFFFT"),
    ("SUB",    "FFFFFF_______________FFFFFTFFFTF"),
    ("SUBU",   "FFFFFF_______________FFFFFTFFFTT"),
    ("AND",    "FFFFFF_______________FFFFFTFFTFF"),
    ("OR",     "FFFFFF_______________FFFFFTFFTFT"),
    ("XOR",    "FFFFFF_______________FFFFFTFFTTF"),
    ("NOR",    "FFFFFF_______________FFFFFTFFTTT"),
    ("SLT",    "FFFFFF_______________FFFFFTFTFTF"),
    ("SLTU",   "FFFFFF_______________FFFFFTFTFTT"),
    ("DADD",   "FFFFFF_______________FFFFFTFTTFF"),
    ("DADDU",  "FFFFFF_______________FFFFFTFTTFT"),
    ("DSUB",   "FFFFFF_______________FFFFFTFTTTF"),
    ("DSUBU",  "FFFFFF_______________FFFFFTFTTTT")
   ]

val cheri_jpatterns = List.map (I ## utilsLib.pattern)
   [
    ("SLL",    "FFFFFFFFFFF_______________FFFFFF"),
    ("SRL",    "FFFFFFFFFFF_______________FFFFTF"),
    ("SRA",    "FFFFFFFFFFF_______________FFFFTT"),
    ("DSLL",   "FFFFFFFFFFF_______________TTTFFF"),
    ("DSRL",   "FFFFFFFFFFF_______________TTTFTF"),
    ("DSRA",   "FFFFFFFFFFF_______________TTTFTT"),
    ("DSLL32", "FFFFFFFFFFF_______________TTTTFF"),
    ("DSRL32", "FFFFFFFFFFF_______________TTTTTF"),
    ("DSRA32", "FFFFFFFFFFF_______________TTTTTT")
   ]

val cheri_patterns0 = List.map (I ## utilsLib.pattern)
   [
    ("LUI",     "FFTTTTFFFFF_____________________"),
    ("DIV",     "FFFFFF__________FFFFFFFFFFFTTFTF"),
    ("DIVU",    "FFFFFF__________FFFFFFFFFFFTTFTT"),
    ("DDIV",    "FFFFFF__________FFFFFFFFFFFTTTTF"),
    ("DDIVU",   "FFFFFF__________FFFFFFFFFFFTTTTT"),
    ("MTHI",    "FFFFFF_____FFFFFFFFFFFFFFFFTFFFT"),
    ("MTLO",    "FFFFFF_____FFFFFFFFFFFFFFFFTFFTT"),
    ("MFHI",    "FFFFFFFFFFFFFFFF_____FFFFFFTFFFF"),
    ("MFLO",    "FFFFFFFFFFFFFFFF_____FFFFFFTFFTF"),
    ("BLTZ",    "FFFFFT_____FFFFF________________"),
    ("BGEZ",    "FFFFFT_____FFFFT________________"),
    ("BLTZL",   "FFFFFT_____FFFTF________________"),
    ("BGEZL",   "FFFFFT_____FFFTT________________"),
    ("BLTZAL",  "FFFFFT_____TFFFF________________"),
    ("BGEZAL",  "FFFFFT_____TFFFT________________"),
    ("BLTZALL", "FFFFFT_____TFFTF________________"),
    ("BGEZALL", "FFFFFT_____TFFTT________________"),
    ("BLEZ",    "FFFTTF_____FFFFF________________"),
    ("BGTZ",    "FFFTTT_____FFFFF________________"),
    ("BLEZL",   "FTFTTF_____FFFFF________________"),
    ("BGTZL",   "FTFTTT_____FFFFF________________"),
    ("JR",      "FFFFFF_____FFFFFFFFFF_____FFTFFF")
   ]

(*
val cheri_cpatterns = List.map (I ## utilsLib.pattern)
   [
    ("MFC0",    "FTFFFFFFFFF__________FFFFFFFF___"),
    ("MTC0",    "FTFFFFFFTFF__________FFFFFFFF___")
   ]
*)

val cheri_patterns = List.map (I ## utilsLib.pattern)
   [
    ("J",       "FFFFTF__________________________"),
    ("JAL",     "FFFFTT__________________________"),
    ("LDL",     "FTTFTF__________________________"),
    ("LDR",     "FTTFTT__________________________"),
    ("LB",      "TFFFFF__________________________"),
(*  ("LH",      "TFFFFT__________________________"), *)
    ("LWL",     "TFFFTF__________________________"),
    ("LW",      "TFFFTT__________________________"),
    ("LBU",     "TFFTFF__________________________"),
(*  ("LHU",     "TFFTFT__________________________"), *)
    ("LWR",     "TFFTTF__________________________"),
    ("LWU",     "TFFTTT__________________________"),
    ("SB",      "TFTFFF__________________________"),
(*  ("SH",      "TFTFFT__________________________"), *)
    ("SW",      "TFTFTT__________________________"),
    ("LL",      "TTFFFF__________________________"),
    ("LLD",     "TTFTFF__________________________"),
    ("LD",      "TTFTTT__________________________"),
    ("SC",      "TTTFFF__________________________"),
    ("SCD",     "TTTTFF__________________________"),
    ("SD",      "TTTTTT__________________________")
(*  ("ERET",    "FTFFFFTFFFFFFFFFFFFFFFFFFFFTTFFF")  *)
   ]

local
   val patterns =
      List.concat [cheri_ipatterns, cheri_jpatterns, cheri_dpatterns,
                   cheri_rpatterns, cheri_patterns0, cheri_patterns]
   fun padded_opcode v = listSyntax.mk_list (pad_opcode v, Type.bool)
   val get_opc = boolSyntax.rand o boolSyntax.rand o utilsLib.lhsc
   fun mk_net l =
      List.foldl
         (fn ((s:string, p), nt) =>
            let
               val thm = DecodeCHERI p
            in
               LVTermNet.insert (nt, ([], get_opc thm), (s, thm))
            end)
         LVTermNet.empty l
   fun find_opcode net =
      let
         fun find_opc tm =
            case LVTermNet.match (net, tm) of
               [(([], opc), (name, thm))] => SOME (name:string, opc, thm:thm)
             | _ => NONE
      in
         fn v =>
            let
               val pv = padded_opcode v
            in
               Option.map
                  (fn (name, opc, thm) =>
                     (name, opc, thm, fst (Term.match_term opc pv)))
                  (find_opc pv)
            end
      end
   fun x i = Term.mk_var ("x" ^ Int.toString i, Type.bool)
   fun assign_bits (p, i, n) =
      let
         val l = (i, n) |> (Arbnum.fromInt ## Lib.I)
                        |> bitstringSyntax.padded_fixedwidth_of_num
                        |> bitstringSyntax.dest_v2w |> fst
                        |> listSyntax.dest_list |> fst
      in
         Term.subst (Lib.mapi (fn i => fn b => x (i + p) |-> b) l)
      end
   val r0  = assign_bits (0, 0, 5)
   val r5  = assign_bits (5, 0, 5)
   val r10 = assign_bits (10, 0, 5)
   val sel = assign_bits (10, 0, 3)
   val dbg = assign_bits (5, 23, 5) o sel
   val err = assign_bits (5, 26, 5) o sel
   fun fnd l = find_opcode (mk_net l)
   fun fnd2 l tm = Option.map (fn (s, t, _, _) => (s, t)) (fnd l tm)
   fun comb (0, _    ) = [[]]
     | comb (_, []   ) = []
     | comb (m, x::xs) = map (fn y => x :: y) (comb (m-1, xs)) @ comb (m, xs)
   fun all_comb l =
     List.concat (List.tabulate (List.length l + 1, fn i => comb (i, l)))
   fun sb l =
      all_comb
         (List.map
            (fn (x, f:term -> term) => (fn (s, t) => (s ^ "_" ^ x, f t))) l)
   val fnd_sb = fnd2 ## sb
   val fp = fnd_sb (cheri_patterns, [])
   val f0 = fnd_sb (cheri_patterns0, [("0", r0)])
   val fd = fnd_sb (cheri_dpatterns, [("d0", r10)])
   val fi = fnd_sb (cheri_ipatterns, [("s0", r0), ("t0", r5)])
   val fj = fnd_sb (cheri_jpatterns, [("t0", r0), ("d0", r5)])
   val fr = fnd_sb (cheri_rpatterns, [("s0", r0), ("t0", r5), ("d0", r10)])
   (*
   val fc = (fnd2 cheri_cpatterns,
               [[fn (s, t) => (s ^ "_debug", dbg t)],
                [fn (s, t) => (s ^ "_errctl", err t)]])
   *)
   fun try_patterns [] tm = []
     | try_patterns ((f, l) :: r) tm =
         (case f tm of
             SOME x => List.map (List.foldl (fn (f, a) => f a) x) l
           | NONE => try_patterns r tm)
   val find_opc = try_patterns [fi, fr, fp, fj, fd, f0]
   val cheri_find_opc_ = fnd patterns
in
   val hex_to_padded_opcode =
      padded_opcode o bitstringSyntax.bitstring_of_hexstring
   fun cheri_decode v =
      case cheri_find_opc_ v of
         SOME (_, _, thm, s) => if List.null s then thm else Thm.INST s thm
       | NONE => raise ERR "decode" (utilsLib.long_term_to_string v)
   val cheri_decode_hex = cheri_decode o hex_to_padded_opcode
   fun cheri_find_opc opc =
      let
         val l = find_opc opc
      in
         List.filter (fn (_, p) => Lib.can (Term.match_term p) opc) l
      end
   val cheri_dict = Redblackmap.fromList String.compare patterns
   (* fun mk_cheri_pattern s = Redblackmap.peek (dict, utilsLib.uppercase s) *)
end

(*
  List.map (cheri_decode o snd) (Redblackmap.listItems cheri_dict)
*)

(* ------------------------------------------------------------------------- *)

(* Evaluator *)

local
   val eval_simp_rule =
      utilsLib.ALL_HYP_CONV_RULE
         (Conv.DEPTH_CONV wordsLib.word_EQ_CONV
          THENC REWRITE_CONV [v2w_0_rwts])
   fun eval0 tm rwt =
      let
         val thm = eval_simp_rule (utilsLib.INST_REWRITE_CONV1 rwt tm)
      in
         if utilsLib.vacuous thm then NONE else SOME thm
      end
  val thms = List.map (DB.fetch "cheri_step") cheri_stepTheory.rwts
  val find_thm = utilsLib.find_rw (utilsLib.mk_rw_net utilsLib.lhsc thms)
in
   fun eval tm =
      let
         fun err s = (Parse.print_term tm; print "\n"; raise ERR "eval" s)
      in
        (case List.mapPartial (eval0 tm) (find_thm tm) of
            [] => err "no valid step theorem"
          | [x] => x
          | [x, _] => x (* ignore exception case *)
          | l => (List.app (fn x => (Parse.print_thm x; print "\n")) l
                  ; err "more than one valid step theorem"))
        handle HOL_ERR {message = "not found",
                        origin_function = "find_rw", ...} =>
           err "instruction instance not supported"
      end
end

local
  val monop = #2 o HolKernel.syntax_fns1 "cheri"
  val binop = #2 o HolKernel.syntax_fns2 "cheri"
  fun monopr ty fld =
      monop $ TypeBasePure.mk_recordtype_fieldsel{tyname=ty,fieldname=fld}
  fun binopr ty fld =
      binop $ TypeBasePure.mk_recordtype_fieldfupd{tyname=ty,fieldname=fld}
  val mk_exception = monopr "cheri_state" "exception"
  val mk_exceptionSignalled = monop "exceptionSignalled"
  val mk_BranchDelay = monop "BranchDelay"
  val mk_BranchDelayPCC = monopr "cheri_state" "BranchDelayPCC"
  val mk_BranchTo = monop "BranchTo"
  val mk_BranchToPCC = monopr "cheri_state" "BranchToPCC"
  val mk_CCallBranch = monopr "cheri_state" "CCallBranch"
  val mk_CCallBranchDelay = monopr "cheri_state" "CCallBranchDelay"
  val mk_currentInst_fupd = binopr "cheri_state" "currentInst"
  fun currentInst w st' =
    mk_currentInst_fupd (combinSyntax.mk_K_1 (w, Term.type_of w), st')
  val st = ``s:cheri_state``
  val ths = [exceptionSignalled_def, BranchDelay_def, BranchTo_def]
  val datatype_conv =
    REWRITE_CONV
      (utilsLib.datatype_rewrites true "cheri"
         ["cheri_state",
          "procState", "DataType", "CP0", "CapCause", "StatusRegister",
          "ExceptionType"] @ ths)
  val dt_assume = ASSUME o utilsLib.rhsc o QCONV datatype_conv
  val procID_th = dt_assume ``^st.procID = 0w``
  val exceptionSignalled_th = dt_assume ``~exceptionSignalled ^st``
  val BranchDelayPCC_th = dt_assume ``^st.BranchDelayPCC = NONE``
  val BranchTo_th = dt_assume ``BranchTo ^st = NONE``
  val BranchToPCC_th = dt_assume ``^st.BranchToPCC = NONE``
  val CCallBranch_th = dt_assume ``~^st.CCallBranch``
  val CCallBranchDelay_th = dt_assume ``~^st.CCallBranchDelay``
  fun eqf_elim th = Drule.EQF_ELIM th handle HOL_ERR _ => th
  val STATE_CONV =
     eqf_elim o
     Conv.QCONV
       (datatype_conv
        THENC REWRITE_CONV
                [boolTheory.COND_ID, procID_th, exceptionSignalled_th,
                 BranchDelayPCC_th, BranchTo_th, BranchToPCC_th,
                 CCallBranch_th, CCallBranchDelay_th,
                 GSYM cheriTheory.recordtype_cheri_state_seldef_exception_def])
  val hyp_rule = utilsLib.ALL_HYP_CONV_RULE datatype_conv
  val full_rule = hyp_rule o Conv.RIGHT_CONV_RULE datatype_conv
  val state_rule = Conv.RIGHT_CONV_RULE (Conv.RAND_CONV (utilsLib.SRW_CONV []))
  val next_rule =
    hyp_rule o
    Conv.CONV_RULE
      (Conv.RAND_CONV (utilsLib.SRW_CONV [PC_def, CP0_def])
       THENC Conv.PATH_CONV "lrlr" (utilsLib.SRW_CONV [])
       THENC Conv.PATH_CONV "lrrrrrlrr" (utilsLib.SRW_CONV []))
  val NextStateCHERI_nodelay = next_rule cheri_stepTheory.NextStateCHERI_nodelay
  val NextStateCHERI_delay = next_rule cheri_stepTheory.NextStateCHERI_delay
  val MP_Next  = state_rule o Drule.MATCH_MP NextStateCHERI_nodelay
  val MP_NextB = state_rule o Drule.MATCH_MP NextStateCHERI_delay
  val Run_CONV = utilsLib.Run_CONV ("cheri", st) o utilsLib.rhsc
  val get = pairSyntax.dest_pair o utilsLib.rhsc
in
  fun cheri_step v =
    let
      val thm1 = fetch v
      val (w, st') = get thm1
      val thm2 = cheri_decode v
      val thm3 = Drule.SPEC_ALL (Run_CONV thm2)
      val ethm = eval (utilsLib.rhsc thm3)
      val thm3 = Conv.RIGHT_CONV_RULE (Conv.REWR_CONV ethm) thm3
      val thm3 = full_rule (Thm.INST [st |-> currentInst w st'] thm3)
      val tm = utilsLib.rhsc thm3
      val thms = List.map (fn f => STATE_CONV (f tm))
                    [mk_exception,
                     mk_BranchDelay,
                     mk_BranchDelayPCC,
                     mk_BranchToPCC,
                     mk_CCallBranch,
                     mk_CCallBranchDelay,
                     mk_BranchTo,
                     mk_exceptionSignalled]
      val thm = hyp_rule (Drule.LIST_CONJ ([thm1, thm2, thm3] @ thms))
    in
      [MP_Next thm]
      @
      ([MP_NextB thm] handle HOL_ERR _ => [])
    end
end

(*

 val tms = strip_conj (fst (dest_imp (concl NextStateCHERI_nodelay)))
 val tms = strip_conj (fst (dest_imp (concl NextStateCHERI_delay)))

 match_term (List.nth (tms, 0)) (concl thm1);
 match_term (List.nth (tms, 1)) (concl thm2);
 match_term (List.nth (tms, 2)) (concl thm3);
 match_term (List.nth (tms, 3)) (concl (List.nth (thms, 0)));
 match_term (List.nth (tms, 4)) (concl (List.nth (thms, 1)));
 match_term (List.nth (tms, 5)) (concl (List.nth (thms, 2)));
 match_term (List.nth (tms, 6)) (concl (List.nth (thms, 3)));
 match_term (List.nth (tms, 7)) (concl (List.nth (thms, 4)));
 match_term (List.nth (tms, 8)) (concl (List.nth (thms, 5)));

*)

val cheri_step_hex = cheri_step o bitstringSyntax.bitstring_of_hexstring

(* ========================================================================= *)

(* Testing

open cheri_stepLib

val step = cheri_step
fun test s = step (Redblackmap.find (cheri_dict, s))
fun test s = (Redblackmap.find (cheri_dict, s))

val v = test "ADDI";
val v = test "ADDU";
val v = test "J";
val v = test "BEQ";
val v = test "BEQL";
val v = test "BLTZAL";
val v = test "BLTZALL";
val v = test "LB";

val l = List.map (Lib.total step o snd) (Redblackmap.listItems cheri_dict)

*)

end
