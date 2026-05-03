(* Self-test: for every ruleset opcode, compare the byte output of the
   typed PFTWriter API against PFTWriter.write_raw. Run for both
   binary and JSON encodings.

   Run with mlton (via selftest-pftraw.mlb) or polyML/testutils. *)

open PFTOpcodes

fun tmpfile pfx =
  OS.FileSys.tmpName () ^ "-" ^ pfx

fun readBin f = let
  val s = BinIO.openIn f
  val v = BinIO.inputAll s
in BinIO.closeIn s; v end

fun readText f = let
  val s = TextIO.openIn f
  val t = TextIO.inputAll s
in TextIO.closeIn s; t end

fun cleanup f = OS.FileSys.remove f handle OS.SysErr _ => ()

(* ------------------------------------------------------------------- *)
(* Per-opcode typed emitters. Each is a function                       *)
(*   emit_typed : PFTWriter.pft_out -> result -> arg_val list -> unit  *)
(* which calls the specific typed PFTWriter.{HOL4,Candle}.* function. *)
(* ------------------------------------------------------------------- *)

fun u_id  (VId n)         = n  | u_id  _ = raise Fail "expected VId"
fun u_ids (VIdList ns)    = ns | u_ids _ = raise Fail "expected VIdList"
fun u_ps  (VIdPairs ps)   = ps | u_ps  _ = raise Fail "expected VIdPairs"
fun u_sps (VStrIdPairs xs)= xs | u_sps _ = raise Fail "expected VStrIdPairs"
fun u_nm  (VName s)       = s  | u_nm  _ = raise Fail "expected VName"
fun u_nms (VNameList ss)  = ss | u_nms _ = raise Fail "expected VNameList"

(* HOL4 typed dispatch *)
fun hol4_typed (opc: int) out r (args: arg_val list) =
  let open PFTWriter in case (opc, args) of
    (0x10, [a])       => HOL4.refl out r (u_id a)
  | (0x11, [a,b])     => HOL4.alpha out r (u_id a) (u_id b)
  | (0x12, [a])       => HOL4.assume out r (u_id a)
  | (0x13, [a])       => HOL4.beta_conv out r (u_id a)
  | (0x14, [a,b])     => HOL4.eq_mp out r (u_id a) (u_id b)
  | (0x15, [a,b])     => HOL4.mp out r (u_id a) (u_id b)
  | (0x16, [a])       => HOL4.sym out r (u_id a)
  | (0x17, [a,b])     => HOL4.trans out r (u_id a) (u_id b)
  | (0x18, [a,b])     => HOL4.conj out r (u_id a) (u_id b)
  | (0x19, [a])       => HOL4.conjunct1 out r (u_id a)
  | (0x1A, [a])       => HOL4.conjunct2 out r (u_id a)
  | (0x1B, [a,b])     => HOL4.disch out r (u_id a) (u_id b)
  | (0x1C, [a,b])     => HOL4.disj1 out r (u_id a) (u_id b)
  | (0x1D, [a,b])     => HOL4.disj2 out r (u_id a) (u_id b)
  | (0x1E, [a,b,c])   => HOL4.disj_cases out r (u_id a) (u_id b) (u_id c)
  | (0x1F, [a])       => HOL4.not_elim out r (u_id a)
  | (0x20, [a])       => HOL4.not_intro out r (u_id a)
  | (0x21, [a,b])     => HOL4.ccontr out r (u_id a) (u_id b)
  | (0x22, [a,b,c])   => HOL4.exists out r (u_id a) (u_id b) (u_id c)
  | (0x23, [a,b,c])   => HOL4.choose out r (u_id a) (u_id b) (u_id c)
  | (0x24, [a,b])     => HOL4.gen out r (u_id a) (u_id b)
  | (0x25, [a,b])     => HOL4.spec out r (u_id a) (u_id b)
  | (0x26, [a,b])     => HOL4.specialize out r (u_id a) (u_id b)
  | (0x27, [a,b])     => HOL4.genl out r (u_id a) (u_ids b)
  | (0x28, [a,b])     => HOL4.absl out r (u_id a) (u_ids b)
  | (0x29, [a,b,c])   => HOL4.gen_abs out r (u_id a) (u_id b) (u_ids c)
  | (0x30, [a,b])     => HOL4.abs_thm out r (u_id a) (u_id b)
  | (0x31, [a,b])     => HOL4.ap_term out r (u_id a) (u_id b)
  | (0x32, [a,b])     => HOL4.ap_thm out r (u_id a) (u_id b)
  | (0x33, [a,b])     => HOL4.mk_comb out r (u_id a) (u_id b)
  | (0x34, [a])       => HOL4.beta_thm out r (u_id a)
  | (0x35, [a,b])     => HOL4.mk_abs_thm out r (u_id a) (u_id b)
  | (0x36, [a,b,c])   => HOL4.mk_comb_thm out r (u_id a) (u_id b) (u_id c)
  | (0x37, [a])       => HOL4.eq_imp_rule1 out r (u_id a)
  | (0x38, [a])       => HOL4.eq_imp_rule2 out r (u_id a)
  | (0x39, [a,b])     => HOL4.inst out r (u_id a) (u_ps b)
  | (0x3A, [a,b])     => HOL4.inst_type out r (u_id a) (u_ps b)
  | (0x3B, [a,b,c])   => HOL4.subst out r (u_id a) (u_id b) (u_ps c)
  | (0x3C, [a,b])     => HOL4.deductAntisym out r (u_id a) (u_id b)
  | (0x40, [a,b])     => HOL4.def_tyop out r (u_id a) (u_nm b)
  | (0x41, [a,b])     => HOL4.def_spec out r (u_id a) (u_nms b)
  | (0x42, [a,b])     => HOL4.def_spec_gen out r (u_id a) (u_nms b)
  | (0x43, [a,b,c,d]) => HOL4.compute_init out r (u_id a) (u_id b)
                           (u_sps c) (u_sps d)
  | (0x44, [a,b,c])   => HOL4.compute out r (u_id a) (u_id b) (u_ids c)
  | _ => raise Fail ("hol4_typed: bad arity for opcode 0x" ^
                     Int.fmt StringCvt.HEX opc)
  end

fun candle_typed (opc: int) out r (args: arg_val list) =
  let open PFTWriter in case (opc, args) of
    (0x10, [a])           => Candle.refl out r (u_id a)
  | (0x11, [a,b])         => Candle.trans out r (u_id a) (u_id b)
  | (0x12, [a,b])         => Candle.mk_comb out r (u_id a) (u_id b)
  | (0x13, [a,b])         => Candle.abs_thm out r (u_id a) (u_id b)
  | (0x14, [a])           => Candle.beta out r (u_id a)
  | (0x15, [a])           => Candle.assume out r (u_id a)
  | (0x16, [a,b])         => Candle.eq_mp out r (u_id a) (u_id b)
  | (0x17, [a,b])         => Candle.deduct_antisym_rule out r (u_id a) (u_id b)
  | (0x18, [a,b])         => Candle.inst out r (u_id a) (u_ps b)
  | (0x19, [a,b])         => Candle.inst_type out r (u_id a) (u_ps b)
  | (0x20, [a])           => Candle.sym out r (u_id a)
  | (0x21, [a,b])         => Candle.prove_hyp out r (u_id a) (u_id b)
  | (0x30, [a,b])         => Candle.new_specification out r (u_id a) (u_nms b)
  | (0x31, [a,b,c,d])     => Candle.new_type_definition out r (u_id a)
                               (u_nm b) (u_nm c) (u_nm d)
  | (0x40, [a])           => Candle.compute_init out r (u_ids a)
  | (0x41, [a,b,c])       => Candle.compute out r (u_id a) (u_id b) (u_ids c)
  | _ => raise Fail ("candle_typed: bad arity for opcode 0x" ^
                     Int.fmt StringCvt.HEX opc)
  end

(* ---------------------------------------------------------------- *)
(* Synthesise plausible sample arguments for a given opcode_desc.   *)
(* We use distinct small integers so a miswiring is visible.         *)
(* ---------------------------------------------------------------- *)

fun sample_for (spec: arg_spec) (i: int) : arg_val =
  case #shape spec of
    AId _         => VId (i + 10)
  | AVal          => VVal (i + 100)
  | AIdList _     => VIdList [i+20, i+21, i+22]
  | AIdPairs _    => VIdPairs [(i+30,i+31), (i+32,i+33)]
  | AStrIdPairs _ => VStrIdPairs [("k1",i+40), ("k2",i+41)]
  | AName         => VName ("n" ^ Int.toString i)
  | ANameList     => VNameList ["n"^Int.toString i, "m"^Int.toString i]

fun sample_args (desc: opcode_desc) : arg_val list =
  let fun go _ [] = []
        | go i (s::rest) = sample_for s i :: go (i+1) rest
  in go 0 (#args desc) end

(* ---------------------------------------------------------------- *)

fun run_one (ruleset: string) binary
            (typed_emit: int -> PFTWriter.pft_out -> int -> arg_val list
                         -> unit)
            (opc, desc: opcode_desc) =
  let
    val ext = if binary then "bin" else "jsonl"
    val f_typed = tmpfile ("typed_" ^ ruleset ^ "_" ^
                           Int.fmt StringCvt.HEX opc ^ "." ^ ext)
    val f_raw   = tmpfile ("raw_"   ^ ruleset ^ "_" ^
                           Int.fmt StringCvt.HEX opc ^ "." ^ ext)
    val result = 7
    val args = sample_args desc
    fun emit_one f emit =
      let val out = PFTWriter.openOut
            {file=f, binary=binary, version="0.1.0", ruleset=ruleset}
          val () = emit out
          val () = PFTWriter.closeOut out
            {n_ty=0, n_tm=0, n_th=0, n_ci=0}
      in () end
    val () = emit_one f_typed
               (fn out => typed_emit opc out result args)
    val () = emit_one f_raw
               (fn out => PFTWriter.write_raw out
                            {opcode=opc, desc=desc,
                             result=result, args=args})
    val eq =
      if binary
      then Word8Vector.collate Word8.compare (readBin f_typed, readBin f_raw)
           = EQUAL
      else readText f_typed = readText f_raw
    val label = ruleset ^ " opcode 0x" ^ Int.fmt StringCvt.HEX opc ^
                " (" ^ ext ^ ", " ^ #tag desc ^ ")"
    val () = if eq
             then print ("OK  " ^ label ^ "\n")
             else (print ("FAIL " ^ label ^ "\n");
                   print ("  typed: " ^ f_typed ^ "\n");
                   print ("  raw:   " ^ f_raw ^ "\n"))
    val () = if eq then (cleanup f_typed; cleanup f_raw) else ()
  in eq end

fun run_all () =
  let
    val r1 = map (run_one "hol4"   true  hol4_typed)   hol4_descs
    val r2 = map (run_one "hol4"   false hol4_typed)   hol4_descs
    val r3 = map (run_one "candle" true  candle_typed) candle_descs
    val r4 = map (run_one "candle" false candle_typed) candle_descs
    val all = r1 @ r2 @ r3 @ r4
    val n = length all
    val passed = length (List.filter (fn b => b) all)
  in
    print ("\n" ^ Int.toString passed ^ "/" ^ Int.toString n ^ " passed\n");
    if passed = n then OS.Process.exit OS.Process.success
    else OS.Process.exit OS.Process.failure
  end

val () = run_all ()
