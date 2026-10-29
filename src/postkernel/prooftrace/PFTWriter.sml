structure PFTWriter :> PFTWriter = struct

(* --- Low-level output ---------------------------------------------------- *)

type pft_out = BinIO.outstream

fun bByte out b = BinIO.output1 (out, b)
fun bBytes out v = BinIO.output (out, v)

(* LEB128 varint *)
fun bVarint out (n: int) = let
  fun loop n =
    if n < 128 then bByte out (Word8.fromInt n)
    else (bByte out (Word8.orb(Word8.fromInt (n mod 128), 0wx80));
          loop (n div 128))
in loop n end

fun bString out s = let
  val bytes = Byte.stringToBytes s
in
  bVarint out (Word8Vector.length bytes);
  bBytes out bytes
end

fun bOpcode out opc = bByte out (Word8.fromInt opc)

(* --- Header and footer ---------------------------------------------------- *)

fun openOut {file, version, ruleset} = let
  val out = BinIO.openOut file
in bBytes out (Byte.stringToBytes "PFT\000");
   bVarint out version;
   bString out ruleset;
   out
end

fun closeOut out {n_ty, n_tm, n_th, n_ci} = let
  fun varint_size n = if n < 128 then 1 else 1 + varint_size (n div 128)
  val footer_len = 1 + varint_size n_ty + varint_size n_tm
                     + varint_size n_th + varint_size n_ci
  val () = bOpcode out 0xFF
  val () = bVarint out n_ty
  val () = bVarint out n_tm
  val () = bVarint out n_th
  val () = bVarint out n_ci
  val lo = Word8.fromInt (footer_len mod 256)
  val hi = Word8.fromInt (footer_len div 256)
in bByte out lo; bByte out hi;
   BinIO.closeOut out
end

(* --- Type commands ------------------------------------------------------- *)

fun tyvar out id name =
    (bOpcode out 0x01; bVarint out id; bString out name)

fun tyop out id name args =
    (bOpcode out 0x02; bVarint out id; bString out name;
     bVarint out (length args);
     List.app (bVarint out) args)

(* --- Term commands ------------------------------------------------------- *)

fun var out id name ty_id =
    (bOpcode out 0x03; bVarint out id; bString out name; bVarint out ty_id)

fun const out id name ty_id =
    (bOpcode out 0x04; bVarint out id; bString out name; bVarint out ty_id)

fun comb out id tm1 tm2 =
    (bOpcode out 0x05; bVarint out id; bVarint out tm1; bVarint out tm2)

fun abs out id tm1 tm2 =
    (bOpcode out 0x06; bVarint out id; bVarint out tm1; bVarint out tm2)

(* --- Kernel commands ------------------------------------------------------ *)

fun new_const out name ty_id =
    (bOpcode out 0x07; bString out name; bVarint out ty_id)

fun new_type out name arity =
    (bOpcode out 0x08; bString out name; bVarint out arity)

fun axiom out id tm nameOpt =
    (bOpcode out 0x09; bVarint out id; bVarint out tm;
     bString out (case nameOpt of SOME n => n | NONE => ""))

(* --- Theorem commands: helpers for common patterns ----------------------- *)

fun th_1 opc out id a =
  (bOpcode out opc; bVarint out id; bVarint out a)

fun th_2 opc out id a b =
  (bOpcode out opc; bVarint out id; bVarint out a; bVarint out b)

fun th_3 opc out id a b c =
  (bOpcode out opc; bVarint out id; bVarint out a; bVarint out b; bVarint out c)

(* --- HOL4 ruleset -------------------------------------------------------- *)

structure HOL4 = struct

(* --- Basic theorem rules ------------------------------------------------- *)

val refl       = th_1 0x10
val assume     = th_1 0x12
val beta_conv  = th_1 0x13
val sym        = th_1 0x16
val conjunct1  = th_1 0x19
val conjunct2  = th_1 0x1A
val not_elim   = th_1 0x1F
val not_intro  = th_1 0x20
val beta_thm   = th_1 0x34
val eq_imp_rule1 = th_1 0x37
val eq_imp_rule2 = th_1 0x38

val alpha      = th_2 0x11
val eq_mp      = th_2 0x14
val mp         = th_2 0x15
val trans      = th_2 0x17
val conj       = th_2 0x18
val disch      = th_2 0x1B
val disj1      = th_2 0x1C
val disj2      = th_2 0x1D
val ccontr     = th_2 0x21
val gen        = th_2 0x24
val spec       = th_2 0x25
val specialize = th_2 0x26
val abs_thm    = th_2 0x30
val ap_term    = th_2 0x31
val ap_thm     = th_2 0x32
val mk_comb    = th_2 0x33
val mk_abs_thm = th_2 0x35
val deductAntisym = th_2 0x3C

val exists     = th_3 0x22
val choose     = th_3 0x23
val mk_comb_thm = th_3 0x36

val disj_cases = th_3 0x1E

(* --- Variable-length theorem rules --------------------------------------- *)

(* GENL id th tms *)
fun genl out id th tms =
    (bOpcode out 0x27; bVarint out id; bVarint out th;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* ABSL id th tms *)
fun absl out id th tms =
    (bOpcode out 0x28; bVarint out id; bVarint out th;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* GEN_ABS id th tm tms *)
fun gen_abs out id th c tms =
    (bOpcode out 0x29; bVarint out id; bVarint out th; bVarint out c;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* INST id th subst *)
fun inst out id th pairs =
    (bOpcode out 0x39; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* INST_TYPE id th subst *)
fun inst_type out id th pairs =
    (bOpcode out 0x3A; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* SUBST id template th subst *)
fun subst out id template th pairs =
    (bOpcode out 0x3B; bVarint out id; bVarint out template; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (t,h) => (bVarint out t; bVarint out h)) pairs)

(* --- Definitions --------------------------------------------------------- *)

fun def_tyop out id th name =
    (bOpcode out 0x40; bVarint out id; bVarint out th; bString out name)

fun def_spec out id th names =
    (bOpcode out 0x41; bVarint out id; bVarint out th;
     bVarint out (length names);
     List.app (bString out) names)

fun def_spec_gen out id th names =
    (bOpcode out 0x42; bVarint out id; bVarint out th;
     bVarint out (length names);
     List.app (bString out) names)

(* --- Computation --------------------------------------------------------- *)

fun compute_init out id ty1 ty2 char_eqns cval_terms =
    (bOpcode out 0x43; bVarint out id; bVarint out ty1; bVarint out ty2;
     bVarint out (length char_eqns);
     List.app (fn (n,th) => (bString out n; bVarint out th)) char_eqns;
     bVarint out (length cval_terms);
     List.app (fn (n,tm) => (bString out n; bVarint out tm)) cval_terms)

fun compute out id ci tm ths =
    (bOpcode out 0x44; bVarint out id; bVarint out ci; bVarint out tm;
     bVarint out (length ths);
     List.app (bVarint out) ths)

end (* structure HOL4 *)

(* --- Candle ruleset ------------------------------------------------------ *)

structure Candle = struct

(* Core inference rules *)
val refl                = th_1 0x10
val beta                = th_1 0x14
val assume              = th_1 0x15
val sym                 = th_1 0x20

val trans               = th_2 0x11
val mk_comb             = th_2 0x12
val abs_thm             = th_2 0x13
val eq_mp               = th_2 0x16
val deduct_antisym_rule = th_2 0x17
val prove_hyp           = th_2 0x21

(* new_specification: id th names *)
fun new_specification out id th names =
    (bOpcode out 0x30; bVarint out id; bVarint out th;
     bVarint out (length names);
     List.app (bString out) names)

(* INST id th subst *)
fun inst out id th pairs =
    (bOpcode out 0x18; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* INST_TYPE id th subst *)
fun inst_type out id th pairs =
    (bOpcode out 0x19; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* new_type_definition id th tyname absname repname *)
fun new_type_definition out id th tyname absname repname =
    (bOpcode out 0x31; bVarint out id; bVarint out th;
     bString out tyname; bString out absname; bString out repname)

(* COMPUTE id ci tm ths *)
fun compute out id ci tm ths =
    (bOpcode out 0x41; bVarint out id; bVarint out ci; bVarint out tm;
     bVarint out (length ths);
     List.app (bVarint out) ths)

(* COMPUTE_INIT id ths *)
fun compute_init out id ths =
    (bOpcode out 0x40; bVarint out id;
     bVarint out (length ths);
     List.app (bVarint out) ths)

end (* structure Candle *)

(* --- Deletion ------------------------------------------------------------ *)

val del_opcodes = [("ty",0xE0),("tm",0xE1),("th",0xE2),("ci",0xE3)]
val del_range_opcodes = [("ty",0xF0),("tm",0xF1),("th",0xF2),("ci",0xF3)]

fun lookup_opc table ns =
  case List.find (fn (k,_) => k = ns) table of
    SOME (_,opc) => opc
  | NONE => raise Fail ("PFTWriter.del: bad namespace " ^ ns)

fun del out ns id =
    (bOpcode out (lookup_opc del_opcodes ns); bVarint out id)

fun del_range out ns lo hi =
    (bOpcode out (lookup_opc del_range_opcodes ns); bVarint out lo; bVarint out hi)

(* --- Save / Load --------------------------------------------------------- *)

fun save out name th_id =
    (bOpcode out 0x50; bString out name; bVarint out th_id)

fun load out id name =
    (bOpcode out 0x51; bVarint out id; bString out name)

(* --- Generic ruleset-command write --------------------------------------- *)

fun write_raw out {opcode, desc: PFTOpcodes.opcode_desc, result, args} =
  let
    open PFTOpcodes
    fun shape_vs_val (AId _,          VId _)         = true
      | shape_vs_val (AVal,           VVal _)        = true
      | shape_vs_val (AIdList _,      VIdList _)     = true
      | shape_vs_val (AIdPairs _,     VIdPairs _)    = true
      | shape_vs_val (AStrIdPairs _,  VStrIdPairs _) = true
      | shape_vs_val (AName,          VName _)       = true
      | shape_vs_val (ANameList,      VNameList _)   = true
      | shape_vs_val _                               = false
    val () =
      if length (#args desc) <> length args then
        raise Fail ("PFTWriter.write_raw: arity mismatch for " ^ #tag desc)
      else ()
    val () =
      ListPair.appEq (fn (s, v) =>
        if shape_vs_val (#shape s, v) then ()
        else raise Fail ("PFTWriter.write_raw: shape mismatch for " ^
                         #tag desc ^ "." ^ #label s))
        (#args desc, args)
    val () = bOpcode out opcode
    val () = bVarint out result
    fun emit v =
      case v of
        VId n         => bVarint out n
      | VVal n        => bVarint out n
      | VIdList ns    => (bVarint out (length ns);
                          List.app (bVarint out) ns)
      | VIdPairs ps   => (bVarint out (length ps);
                          List.app (fn (a,b) => (bVarint out a;
                                                 bVarint out b)) ps)
      | VStrIdPairs es => (bVarint out (length es);
                           List.app (fn (n,v) => (bString out n;
                                                  bVarint out v)) es)
      | VName s       => bString out s
      | VNameList ss  => (bVarint out (length ss);
                          List.app (bString out) ss)
  in List.app emit args
  end

(* --- Expect -------------------------------------------------------------- *)

fun expect out th hyps concl =
    (bOpcode out 0xEF; bVarint out th;
     bVarint out (List.length hyps);
     List.app (bVarint out) hyps;
     bVarint out concl)

end
