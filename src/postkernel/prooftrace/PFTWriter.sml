structure PFTWriter :> PFTWriter = struct

(* --- Low-level output ---------------------------------------------------- *)

datatype pft_out =
    TextOut of TextIO.outstream
  | BinOut of BinIO.outstream

fun closeOut (TextOut s) = TextIO.closeOut s
  | closeOut (BinOut s) = BinIO.closeOut s

fun openOut {file, binary} =
  if binary then BinOut (BinIO.openOut file)
  else TextOut (TextIO.openOut file)

(* Text output helpers *)

fun tWrite (TextOut s) t = TextIO.output (s, t)
  | tWrite _ _ = raise Fail "tWrite on binary stream"

fun tInt out n = tWrite out (Int.toString n)

(* Name escaping for text format.  The decoder interprets:
     "\ "  as a literal space
     "\\"  as a literal backslash
     "\x"  (any other x) as the two literal characters \ and x
     "\_"  as the whole-token encoding of the empty string
   We escape minimally: a backslash is only escaped when followed by space or
   backslash or end of string (the only pairs the decoder treats specially).
   Spaces are always escaped. The token "\_" is reserved for the empty string,
   so the name "\_" is written as "\\_". *)
fun escapeName "" = "\\_"
  | escapeName "\\_" = "\\\\_"
  | escapeName s = let
      val n = String.size s
      fun esc i acc = if i >= n then List.rev acc
        else let val c = String.sub(s, i) in
          if c = #" " orelse (
             c = #"\\" andalso (
               let val c2 = String.sub(s, i+1)
               in c2 = #" " orelse c2 = #"\\"
               end handle Subscript => true ))
          then esc (i+1) (c :: #"\\" :: acc)
          else esc (i+1) (c :: acc)
        end
    in String.implode (esc 0 []) end

fun tName out s = tWrite out (escapeName s)

fun tSp out = tWrite out " "
fun tNl out = tWrite out "\n"

(* Binary output helpers *)

fun bByte (BinOut s) b = BinIO.output1 (s, b)
  | bByte _ _ = raise Fail "bByte on text stream"

fun bBytes (BinOut s) v = BinIO.output (s, v)
  | bBytes _ _ = raise Fail "bBytes on text stream"

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

(* --- Header -------------------------------------------------------------- *)

fun header (out as TextOut _) {version, ruleset, n_ty, n_tm, n_th, n_ci} =
    (tWrite out "PFT "; tInt out version;
     tSp out; tName out ruleset;
     tSp out; tInt out n_ty;
     tSp out; tInt out n_tm;
     tSp out; tInt out n_th;
     tSp out; tInt out n_ci;
     tNl out)
  | header (out as BinOut _) {version, ruleset, n_ty, n_tm, n_th, n_ci} =
    (bBytes out (Byte.stringToBytes "PFT\000");
     bVarint out version;
     bString out ruleset;
     bVarint out n_ty;
     bVarint out n_tm;
     bVarint out n_th;
     bVarint out n_ci)

(* --- Text command helpers ------------------------------------------------ *)

(* Emit: COMMAND id args... \n *)
fun tCmd out cmd id = (tWrite out cmd; tSp out; tInt out id)
fun tArg out n = (tSp out; tInt out n)

(* --- Type commands ------------------------------------------------------- *)

fun tyvar (out as TextOut _) id name =
    (tCmd out "TYVAR" id; tSp out; tName out name; tNl out)
  | tyvar out id name =
    (bOpcode out 0x01; bVarint out id; bString out name)

fun tyop (out as TextOut _) id name args =
    (tCmd out "TYOP" id; tSp out; tName out name;
     List.app (tArg out) args; tNl out)
  | tyop out id name args =
    (bOpcode out 0x02; bVarint out id; bString out name;
     bVarint out (length args);
     List.app (bVarint out) args)

(* --- Term commands ------------------------------------------------------- *)

fun var (out as TextOut _) id name ty_id =
    (tCmd out "VAR" id; tSp out; tName out name; tArg out ty_id; tNl out)
  | var out id name ty_id =
    (bOpcode out 0x03; bVarint out id; bString out name; bVarint out ty_id)

fun const (out as TextOut _) id name ty_id =
    (tCmd out "CONST" id; tSp out; tName out name; tArg out ty_id; tNl out)
  | const out id name ty_id =
    (bOpcode out 0x04; bVarint out id; bString out name; bVarint out ty_id)

fun comb (out as TextOut _) id tm1 tm2 =
    (tCmd out "COMB" id; tArg out tm1; tArg out tm2; tNl out)
  | comb out id tm1 tm2 =
    (bOpcode out 0x05; bVarint out id; bVarint out tm1; bVarint out tm2)

fun abs (out as TextOut _) id tm1 tm2 =
    (tCmd out "ABS" id; tArg out tm1; tArg out tm2; tNl out)
  | abs out id tm1 tm2 =
    (bOpcode out 0x06; bVarint out id; bVarint out tm1; bVarint out tm2)

(* --- Theorem commands: helpers for common patterns ----------------------- *)

(* th_1: RULE id arg *)
fun th_1 cmd opc out id a = case out of
    TextOut _ => (tCmd out cmd id; tArg out a; tNl out)
  | BinOut _ => (bOpcode out opc; bVarint out id; bVarint out a)

(* th_2: RULE id arg1 arg2 *)
fun th_2 cmd opc out id a b = case out of
    TextOut _ => (tCmd out cmd id; tArg out a; tArg out b; tNl out)
  | BinOut _ => (bOpcode out opc; bVarint out id; bVarint out a; bVarint out b)

(* th_3: RULE id arg1 arg2 arg3 *)
fun th_3 cmd opc out id a b c = case out of
    TextOut _ => (tCmd out cmd id; tArg out a; tArg out b; tArg out c; tNl out)
  | BinOut _ => (bOpcode out opc; bVarint out id;
                 bVarint out a; bVarint out b; bVarint out c)

(* --- Basic theorem rules ------------------------------------------------- *)

val refl       = th_1 "REFL"       0x10
val assume     = th_1 "ASSUME"     0x12
val beta_conv  = th_1 "BETA_CONV"  0x13
val sym        = th_1 "SYM"        0x16
val conjunct1  = th_1 "CONJUNCT1"  0x19
val conjunct2  = th_1 "CONJUNCT2"  0x1A
val not_elim   = th_1 "NOT_ELIM"   0x1F
val not_intro  = th_1 "NOT_INTRO"  0x20
val beta_thm   = th_1 "Beta"       0x34
val eq_imp_rule1 = th_1 "EQ_IMP_RULE1" 0x37
val eq_imp_rule2 = th_1 "EQ_IMP_RULE2" 0x38

val alpha      = th_2 "ALPHA"      0x11
val eq_mp      = th_2 "EQ_MP"      0x14
val mp         = th_2 "MP"         0x15
val trans      = th_2 "TRANS"      0x17
val conj       = th_2 "CONJ"       0x18
val disch      = th_2 "DISCH"      0x1B
val disj1      = th_2 "DISJ1"      0x1C
val disj2      = th_2 "DISJ2"      0x1D
val ccontr     = th_2 "CCONTR"     0x21
val gen        = th_2 "GEN"        0x24
val spec       = th_2 "SPEC"       0x25
val specialize = th_2 "Specialize" 0x26
val abs_thm    = th_2 "ABS_THM"    0x30
val ap_term    = th_2 "AP_TERM"    0x31
val ap_thm     = th_2 "AP_THM"     0x32
val mk_comb    = th_2 "MK_COMB"    0x33
val mk_abs_thm = th_2 "Mk_abs"    0x35
val deductAntisym = th_2 "deductAntisym" 0x3C

val exists     = th_3 "EXISTS"     0x22
val choose     = th_3 "CHOOSE"     0x23
val mk_comb_thm = th_3 "Mk_comb"  0x36

val disj_cases = th_3 "DISJ_CASES" 0x1E

(* --- Variable-length theorem rules --------------------------------------- *)

(* GENL id th tm... *)
fun genl (out as TextOut _) id th tms =
    (tCmd out "GENL" id; tArg out th;
     List.app (tArg out) tms; tNl out)
  | genl out id th tms =
    (bOpcode out 0x27; bVarint out id; bVarint out th;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* ABSL id th tm... *)
fun absl (out as TextOut _) id th tms =
    (tCmd out "ABSL" id; tArg out th;
     List.app (tArg out) tms; tNl out)
  | absl out id th tms =
    (bOpcode out 0x28; bVarint out id; bVarint out th;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* GEN_ABS id th tm tm... *)
fun gen_abs (out as TextOut _) id th c tms =
    (tCmd out "GEN_ABS" id; tArg out th; tArg out c;
     List.app (tArg out) tms; tNl out)
  | gen_abs out id th c tms =
    (bOpcode out 0x29; bVarint out id; bVarint out th; bVarint out c;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* INST id th (tm tm)... *)
fun inst (out as TextOut _) id th pairs =
    (tCmd out "INST" id; tArg out th;
     List.app (fn (a,b) => (tArg out a; tArg out b)) pairs; tNl out)
  | inst out id th pairs =
    (bOpcode out 0x39; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* INST_TYPE id th (ty ty)... *)
fun inst_type (out as TextOut _) id th pairs =
    (tCmd out "INST_TYPE" id; tArg out th;
     List.app (fn (a,b) => (tArg out a; tArg out b)) pairs; tNl out)
  | inst_type out id th pairs =
    (bOpcode out 0x3A; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* SUBST id tm th (tm th)... *)
fun subst (out as TextOut _) id template th pairs =
    (tCmd out "SUBST" id; tArg out template; tArg out th;
     List.app (fn (t,h) => (tArg out t; tArg out h)) pairs; tNl out)
  | subst out id template th pairs =
    (bOpcode out 0x3B; bVarint out id; bVarint out template; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (t,h) => (bVarint out t; bVarint out h)) pairs)

(* --- Axioms and definitions ---------------------------------------------- *)

fun axiom (out as TextOut _) id tm nameOpt =
    (tCmd out "AXIOM" id; tArg out tm;
     case nameOpt of SOME n => (tSp out; tName out n) | NONE => ();
     tNl out)
  | axiom out id tm nameOpt =
    (bOpcode out 0x40; bVarint out id; bVarint out tm;
     bString out (case nameOpt of SOME n => n | NONE => ""))

fun def_spec (out as TextOut _) id th names =
    (tCmd out "DEF_SPEC" id; tArg out th;
     List.app (fn n => (tSp out; tName out n)) names; tNl out)
  | def_spec out id th names =
    (bOpcode out 0x41; bVarint out id; bVarint out th;
     bVarint out (length names);
     List.app (bString out) names)

fun def_tyop (out as TextOut _) id th name =
    (tCmd out "DEF_TYOP" id; tArg out th; tSp out; tName out name; tNl out)
  | def_tyop out id th name =
    (bOpcode out 0x42; bVarint out id; bVarint out th; bString out name)

(* --- Computation --------------------------------------------------------- *)

fun compute (out as TextOut _) id ci tm ths =
    (tCmd out "COMPUTE" id; tArg out ci; tArg out tm;
     List.app (tArg out) ths; tNl out)
  | compute out id ci tm ths =
    (bOpcode out 0x43; bVarint out id; bVarint out ci; bVarint out tm;
     bVarint out (length ths);
     List.app (bVarint out) ths)

fun compute_init (out as TextOut _) id ty1 ty2 char_eqns cval_terms =
    (tCmd out "COMPUTE_INIT" id; tArg out ty1; tArg out ty2; tNl out;
     tWrite out " ";
     List.app (fn (n,th) => (tSp out; tName out n; tArg out th)) char_eqns;
     tNl out;
     tWrite out " ";
     List.app (fn (n,tm) => (tSp out; tName out n; tArg out tm)) cval_terms;
     tNl out)
  | compute_init out id ty1 ty2 char_eqns cval_terms =
    (bOpcode out 0x44; bVarint out id; bVarint out ty1; bVarint out ty2;
     bVarint out (length char_eqns);
     List.app (fn (n,th) => (bString out n; bVarint out th)) char_eqns;
     bVarint out (length cval_terms);
     List.app (fn (n,tm) => (bString out n; bVarint out tm)) cval_terms)

(* --- Deletion ------------------------------------------------------------ *)

val del_opcodes = [("ty",0xE0),("tm",0xE1),("th",0xE2),("ci",0xE3)]
val del_range_opcodes = [("ty",0xF0),("tm",0xF1),("th",0xF2),("ci",0xF3)]

fun lookup_opc table ns =
  case List.find (fn (k,_) => k = ns) table of
    SOME (_,opc) => opc
  | NONE => raise Fail ("PFTWriter.del: bad namespace " ^ ns)

fun del (out as TextOut _) ns id =
    (tWrite out "DEL "; tWrite out ns; tSp out; tInt out id; tNl out)
  | del out ns id =
    (bOpcode out (lookup_opc del_opcodes ns); bVarint out id)

fun del_range (out as TextOut _) ns lo hi =
    (tWrite out "DEL "; tWrite out ns; tSp out; tInt out lo;
     tSp out; tInt out hi; tNl out)
  | del_range out ns lo hi =
    (bOpcode out (lookup_opc del_range_opcodes ns); bVarint out lo; bVarint out hi)

(* --- Save / Load --------------------------------------------------------- *)

fun save (out as TextOut _) name th_id =
    (tWrite out "SAVE "; tName out name; tArg out th_id; tNl out)
  | save out name th_id =
    (bOpcode out 0x50; bString out name; bVarint out th_id)

fun load (out as TextOut _) id name =
    (tWrite out "LOAD "; tInt out id; tSp out; tName out name; tNl out)
  | load out id name =
    (bOpcode out 0x51; bVarint out id; bString out name)

(* --- Comment ------------------------------------------------------------- *)

fun comment (TextOut s) text = (TextIO.output (s, "# ");
                                TextIO.output (s, text);
                                TextIO.output (s, "\n"))
  | comment (BinOut _) _ = ()

end
