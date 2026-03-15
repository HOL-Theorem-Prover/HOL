structure PFTWriter :> PFTWriter = struct

(* --- Low-level output ---------------------------------------------------- *)

datatype pft_out =
    TextOut of TextIO.outstream
  | BinOut of BinIO.outstream

(* --- JSON text output helpers -------------------------------------------- *)

fun tWrite (TextOut s) t = TextIO.output (s, t)
  | tWrite _ _ = raise Fail "tWrite on binary stream"

(* JSON string escaping: handle \, ", and control characters *)
fun jsonEscape s = let
  val n = String.size s
  fun esc i acc = if i >= n then String.concat (List.rev acc)
    else let val c = String.sub(s, i) in
      if c = #"\"" then esc (i+1) ("\\\"" :: acc)
      else if c = #"\\" then esc (i+1) ("\\\\" :: acc)
      else if c = #"\n" then esc (i+1) ("\\n" :: acc)
      else if c = #"\r" then esc (i+1) ("\\r" :: acc)
      else if c = #"\t" then esc (i+1) ("\\t" :: acc)
      else if Char.ord c < 32 then
        esc (i+1) ("\\u00"
                    ^ (if Char.ord c < 16 then "0" else "1")
                    ^ str (String.sub("0123456789abcdef",
                                      Char.ord c mod 16))
                    :: acc)
      else esc (i+1) (str c :: acc)
    end
in esc 0 [] end

(* Begin a JSON object: {"cmd":"NAME" *)
fun jBegin out cmd =
  tWrite out ("{\"cmd\":\"" ^ cmd ^ "\"")

(* Emit ,"key":int *)
fun jInt out key n =
  tWrite out (",\"" ^ key ^ "\":" ^ Int.toString n)

(* Emit ,"key":"value" *)
fun jStr out key v =
  tWrite out (",\"" ^ key ^ "\":\"" ^ jsonEscape v ^ "\"")

(* Emit ,"key":[i1,i2,...] *)
fun jIntList out key ns =
  tWrite out (",\"" ^ key ^ "\":["
              ^ String.concatWith "," (List.map Int.toString ns) ^ "]")

(* Emit ,"key":["s1","s2",...] *)
fun jStrList out key ss =
  tWrite out (",\"" ^ key ^ "\":["
              ^ String.concatWith ","
                  (List.map (fn s => "\"" ^ jsonEscape s ^ "\"") ss) ^ "]")

(* Emit ,"key":[{"redex":r1,"residue":r2},...] *)
fun jSubstList out key pairs =
  let fun one (r, s) = "{\"redex\":" ^ Int.toString r
                        ^ ",\"residue\":" ^ Int.toString s ^ "}"
  in tWrite out (",\"" ^ key ^ "\":["
                 ^ String.concatWith "," (List.map one pairs) ^ "]")
  end

(* Emit ,"key":{"n1":v1,"n2":v2,...} for named int maps *)
fun jNamedIntMap out key entries =
  let fun one (n, v) = "\"" ^ jsonEscape n ^ "\":" ^ Int.toString v
  in tWrite out (",\"" ^ key ^ "\":{"
                 ^ String.concatWith "," (List.map one entries) ^ "}")
  end

(* End a JSON object: }\n *)
fun jEnd out = tWrite out "}\n"

(* --- Binary output helpers ----------------------------------------------- *)

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

(* --- Header and footer ---------------------------------------------------- *)

fun openOut {file, binary, version, ruleset} =
  if binary then let
    val s = BinIO.openOut file
    val out = BinOut s
  in bBytes out (Byte.stringToBytes "PFT\000");
     bVarint out version;
     bString out ruleset;
     out
  end
  else let
    val s = TextIO.openOut file
    val out = TextOut s
  in jBegin out "PFT";
     jInt out "version" version;
     jStr out "ruleset" ruleset;
     jEnd out;
     out
  end

fun closeOut (out as TextOut s) {n_ty, n_tm, n_th, n_ci} =
    (jBegin out "FOOTER";
     jInt out "n_ty" n_ty;
     jInt out "n_tm" n_tm;
     jInt out "n_th" n_th;
     jInt out "n_ci" n_ci;
     jEnd out;
     TextIO.closeOut s)
  | closeOut (out as BinOut s) {n_ty, n_tm, n_th, n_ci} = let
    fun varint_size n = if n < 128 then 1 else 1 + varint_size (n div 128)
    val footer_len = varint_size n_ty + varint_size n_tm
                   + varint_size n_th + varint_size n_ci
    val () = bVarint out n_ty
    val () = bVarint out n_tm
    val () = bVarint out n_th
    val () = bVarint out n_ci
    val lo = Word8.fromInt (footer_len mod 256)
    val hi = Word8.fromInt (footer_len div 256)
  in bByte out lo; bByte out hi;
     BinIO.closeOut s
  end

(* --- Type commands ------------------------------------------------------- *)

fun tyvar (out as TextOut _) id name =
    (jBegin out "TYVAR"; jInt out "id" id;
     jStr out "name" name; jEnd out)
  | tyvar out id name =
    (bOpcode out 0x01; bVarint out id; bString out name)

fun tyop (out as TextOut _) id name args =
    (jBegin out "TYOP"; jInt out "id" id;
     jStr out "name" name; jIntList out "args" args; jEnd out)
  | tyop out id name args =
    (bOpcode out 0x02; bVarint out id; bString out name;
     bVarint out (length args);
     List.app (bVarint out) args)

(* --- Term commands ------------------------------------------------------- *)

fun var (out as TextOut _) id name ty_id =
    (jBegin out "VAR"; jInt out "id" id;
     jStr out "name" name; jInt out "ty" ty_id; jEnd out)
  | var out id name ty_id =
    (bOpcode out 0x03; bVarint out id; bString out name; bVarint out ty_id)

fun const (out as TextOut _) id name ty_id =
    (jBegin out "CONST"; jInt out "id" id;
     jStr out "name" name; jInt out "ty" ty_id; jEnd out)
  | const out id name ty_id =
    (bOpcode out 0x04; bVarint out id; bString out name; bVarint out ty_id)

fun comb (out as TextOut _) id tm1 tm2 =
    (jBegin out "COMB"; jInt out "id" id;
     jInt out "rator" tm1; jInt out "rand" tm2; jEnd out)
  | comb out id tm1 tm2 =
    (bOpcode out 0x05; bVarint out id; bVarint out tm1; bVarint out tm2)

fun abs (out as TextOut _) id tm1 tm2 =
    (jBegin out "ABS"; jInt out "id" id;
     jInt out "var" tm1; jInt out "body" tm2; jEnd out)
  | abs out id tm1 tm2 =
    (bOpcode out 0x06; bVarint out id; bVarint out tm1; bVarint out tm2)

(* --- Theorem commands: helpers for common patterns ----------------------- *)

(* th_1: RULE id arg — one key *)
fun th_1 cmd opc k1 out id a = case out of
    TextOut _ => (jBegin out cmd; jInt out "id" id;
                  jInt out k1 a; jEnd out)
  | BinOut _ => (bOpcode out opc; bVarint out id; bVarint out a)

(* th_2: RULE id arg1 arg2 — two keys *)
fun th_2 cmd opc k1 k2 out id a b = case out of
    TextOut _ => (jBegin out cmd; jInt out "id" id;
                  jInt out k1 a; jInt out k2 b; jEnd out)
  | BinOut _ => (bOpcode out opc; bVarint out id;
                 bVarint out a; bVarint out b)

(* th_3: RULE id arg1 arg2 arg3 — three keys *)
fun th_3 cmd opc k1 k2 k3 out id a b c = case out of
    TextOut _ => (jBegin out cmd; jInt out "id" id;
                  jInt out k1 a; jInt out k2 b; jInt out k3 c; jEnd out)
  | BinOut _ => (bOpcode out opc; bVarint out id;
                 bVarint out a; bVarint out b; bVarint out c)

(* --- Basic theorem rules ------------------------------------------------- *)

val refl       = th_1 "REFL"       0x10 "tm"
val assume     = th_1 "ASSUME"     0x12 "tm"
val beta_conv  = th_1 "BETA_CONV"  0x13 "tm"
val sym        = th_1 "SYM"        0x16 "th"
val conjunct1  = th_1 "CONJUNCT1"  0x19 "th"
val conjunct2  = th_1 "CONJUNCT2"  0x1A "th"
val not_elim   = th_1 "NOT_ELIM"   0x1F "th"
val not_intro  = th_1 "NOT_INTRO"  0x20 "th"
val beta_thm   = th_1 "Beta"       0x34 "th"
val eq_imp_rule1 = th_1 "EQ_IMP_RULE1" 0x37 "th"
val eq_imp_rule2 = th_1 "EQ_IMP_RULE2" 0x38 "th"

val alpha      = th_2 "ALPHA"      0x11 "tm1" "tm2"
val eq_mp      = th_2 "EQ_MP"      0x14 "eq" "th"
val mp         = th_2 "MP"         0x15 "imp" "ant"
val trans      = th_2 "TRANS"      0x17 "th1" "th2"
val conj       = th_2 "CONJ"       0x18 "th1" "th2"
val disch      = th_2 "DISCH"      0x1B "tm" "th"
val disj1      = th_2 "DISJ1"      0x1C "th" "tm"
val disj2      = th_2 "DISJ2"      0x1D "tm" "th"
val ccontr     = th_2 "CCONTR"     0x21 "tm" "th"
val gen        = th_2 "GEN"        0x24 "tm" "th"
val spec       = th_2 "SPEC"       0x25 "tm" "th"
val specialize = th_2 "Specialize" 0x26 "tm" "th"
val abs_thm    = th_2 "ABS_THM"    0x30 "tm" "th"
val ap_term    = th_2 "AP_TERM"    0x31 "tm" "th"
val ap_thm     = th_2 "AP_THM"     0x32 "th" "tm"
val mk_comb    = th_2 "MK_COMB"    0x33 "th1" "th2"
val mk_abs_thm = th_2 "Mk_abs"    0x35 "eq" "body"
val deductAntisym = th_2 "deductAntisym" 0x3C "th1" "th2"

val exists     = th_3 "EXISTS"     0x22 "tm1" "tm2" "th"
val choose     = th_3 "CHOOSE"     0x23 "var" "existence" "body"
val mk_comb_thm = th_3 "Mk_comb"  0x36 "eq" "rator" "rand"

val disj_cases = th_3 "DISJ_CASES" 0x1E "disj" "left" "right"

(* --- Variable-length theorem rules --------------------------------------- *)

(* GENL id th tms *)
fun genl (out as TextOut _) id th tms =
    (jBegin out "GENL"; jInt out "id" id;
     jInt out "th" th; jIntList out "tms" tms; jEnd out)
  | genl out id th tms =
    (bOpcode out 0x27; bVarint out id; bVarint out th;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* ABSL id th tms *)
fun absl (out as TextOut _) id th tms =
    (jBegin out "ABSL"; jInt out "id" id;
     jInt out "th" th; jIntList out "tms" tms; jEnd out)
  | absl out id th tms =
    (bOpcode out 0x28; bVarint out id; bVarint out th;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* GEN_ABS id th tm tms *)
fun gen_abs (out as TextOut _) id th c tms =
    (jBegin out "GEN_ABS"; jInt out "id" id;
     jInt out "th" th; jInt out "tm" c;
     jIntList out "tms" tms; jEnd out)
  | gen_abs out id th c tms =
    (bOpcode out 0x29; bVarint out id; bVarint out th; bVarint out c;
     bVarint out (length tms);
     List.app (bVarint out) tms)

(* INST id th subst *)
fun inst (out as TextOut _) id th pairs =
    (jBegin out "INST"; jInt out "id" id;
     jInt out "th" th; jSubstList out "subst" pairs; jEnd out)
  | inst out id th pairs =
    (bOpcode out 0x39; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* INST_TYPE id th subst *)
fun inst_type (out as TextOut _) id th pairs =
    (jBegin out "INST_TYPE"; jInt out "id" id;
     jInt out "th" th; jSubstList out "subst" pairs; jEnd out)
  | inst_type out id th pairs =
    (bOpcode out 0x3A; bVarint out id; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (a,b) => (bVarint out a; bVarint out b)) pairs)

(* SUBST id template th subst *)
fun subst (out as TextOut _) id template th pairs =
    (jBegin out "SUBST"; jInt out "id" id;
     jInt out "template" template; jInt out "th" th;
     jSubstList out "subst" pairs; jEnd out)
  | subst out id template th pairs =
    (bOpcode out 0x3B; bVarint out id; bVarint out template; bVarint out th;
     bVarint out (length pairs);
     List.app (fn (t,h) => (bVarint out t; bVarint out h)) pairs)

(* --- Axioms and definitions ---------------------------------------------- *)

fun axiom (out as TextOut _) id tm nameOpt =
    (jBegin out "AXIOM"; jInt out "id" id; jInt out "tm" tm;
     case nameOpt of SOME n => jStr out "name" n | NONE => ();
     jEnd out)
  | axiom out id tm nameOpt =
    (bOpcode out 0x40; bVarint out id; bVarint out tm;
     bString out (case nameOpt of SOME n => n | NONE => ""))

fun def_spec (out as TextOut _) id th names =
    (jBegin out "DEF_SPEC"; jInt out "id" id;
     jInt out "th" th; jStrList out "names" names; jEnd out)
  | def_spec out id th names =
    (bOpcode out 0x41; bVarint out id; bVarint out th;
     bVarint out (length names);
     List.app (bString out) names)

fun def_tyop (out as TextOut _) id th name =
    (jBegin out "DEF_TYOP"; jInt out "id" id;
     jInt out "th" th; jStr out "name" name; jEnd out)
  | def_tyop out id th name =
    (bOpcode out 0x42; bVarint out id; bVarint out th; bString out name)

(* --- Computation --------------------------------------------------------- *)

fun compute (out as TextOut _) id ci tm ths =
    (jBegin out "COMPUTE"; jInt out "id" id;
     jInt out "ci" ci; jInt out "tm" tm;
     jIntList out "ths" ths; jEnd out)
  | compute out id ci tm ths =
    (bOpcode out 0x43; bVarint out id; bVarint out ci; bVarint out tm;
     bVarint out (length ths);
     List.app (bVarint out) ths)

fun compute_init (out as TextOut _) id ty1 ty2 char_eqns cval_terms =
    (jBegin out "COMPUTE_INIT"; jInt out "id" id;
     jInt out "num_ty" ty1; jInt out "cval_ty" ty2;
     jNamedIntMap out "char_eqns" char_eqns;
     jNamedIntMap out "cval_terms" cval_terms;
     jEnd out)
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
    (jBegin out "DEL"; jStr out "ns" ns;
     jInt out "id" id; jEnd out)
  | del out ns id =
    (bOpcode out (lookup_opc del_opcodes ns); bVarint out id)

fun del_range (out as TextOut _) ns lo hi =
    (jBegin out "DEL"; jStr out "ns" ns;
     jInt out "id" lo; jInt out "upto" hi; jEnd out)
  | del_range out ns lo hi =
    (bOpcode out (lookup_opc del_range_opcodes ns); bVarint out lo; bVarint out hi)

(* --- Save / Load --------------------------------------------------------- *)

fun save (out as TextOut _) name th_id =
    (jBegin out "SAVE"; jStr out "name" name;
     jInt out "th" th_id; jEnd out)
  | save out name th_id =
    (bOpcode out 0x50; bString out name; bVarint out th_id)

fun load (out as TextOut _) id name =
    (jBegin out "LOAD"; jInt out "id" id;
     jStr out "name" name; jEnd out)
  | load out id name =
    (bOpcode out 0x51; bVarint out id; bString out name)

end
