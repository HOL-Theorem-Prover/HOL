(*===========================================================================*)
(* Simple theory of bytes.                                                   *)
(*===========================================================================*)

(* Interactive mode:
  app load ["word8Lib", "word8CasesTheory"];
  quietdec := true;
  open word8Lib word8Theory word8CasesTheory;
  quietdec := false;
*)
structure word8CasesLib :> word8CasesLib = struct
open HolKernel Parse boolLib bossLib word8Lib word8Theory word8CasesTheory

val ERR = mk_HOL_ERR "word8CasesLib";
val WARN = HOL_WARNING "word8CasesLib";

val n2w_tm         = prim_mk_const{Name="n2w",Thy="word8"};
val word8_cases_tm = prim_mk_const{Name="word8_cases",Thy="word8Cases"};

fun mk_n2w i = mk_comb(n2w_tm,numSyntax.term_of_int i);
fun dest_atom tm = dest_const tm handle HOL_ERR _ => dest_var tm;


datatype clause = Var of term * term
                | Num of int * term

fun cvt_param (arg, res) =
  if is_var arg then
    Var (arg, res)
  else if is_comb arg then
    let val (n2w, nums) = strip_comb arg in
      if term_eq n2w_tm n2w andalso
         length nums = 1 andalso
         numSyntax.is_numeral (hd nums) then
        Num (numSyntax.int_of_term (hd nums) mod 256, res)
      else
        raise ERR "cvt_param" "bad syntax in word constant"
    end
  else
    raise ERR "cvt_param"
              "argument must be a syntactic variable or word constant"

fun to_first_var [] acc = (acc, NONE)
  | to_first_var [Var x] acc = (acc, SOME x)
  | to_first_var [Num x] acc = (x :: acc, NONE)
  | to_first_var (Var x :: t) acc = 
      (WARN "to_first_var"
            "ignoring cases after variable parameter case";
       (rev acc, SOME x))
  | to_first_var (Num x :: t) acc = 
      to_first_var t (x :: acc)

fun fill_results_helper next i j r default warn = 
  let val first_pad_amt  = i - next 
      val second_pad_amt = j - i - 1
  in
    if first_pad_amt > 0 orelse second_pad_amt > 0 then
      warn ()
    else ();
    (List.tabulate (first_pad_amt, default next) @ [(i, r)] @
      List.tabulate (second_pad_amt, default (i + first_pad_amt)),
     next + 1 + first_pad_amt + second_pad_amt)
  end

fun fill_results [] default warn next =
      if next = 256 then
        []
      else
       (warn ();
        List.tabulate (256 - next, default next))
  | fill_results [(i, r)] default warn next =
      #1 (fill_results_helper next i 256 r default warn)
  | fill_results ((i, r1) :: (j, r2) :: t) default warn next = 
      if i = j then
        raise ERR "fill_results"
                 ("duplicate definitions for " ^ int_to_string i ^ "w")
      else 
        let val (rs, next_next) = 
                fill_results_helper next i j r1 default warn
        in 
          rs @ fill_results ((j, r2) :: t) default warn next_next
        end

fun default (SOME var) res start i = 
      (start + i, subst [var |-> mk_n2w (start + i)] res)
  | default NONE res start i = 
      (start + i, res)

local val th = SPEC_ALL COND_CLAUSES
in
val COND_T_THM = CONJUNCT1 th
val COND_F_THM = CONJUNCT2 th
val COND_T_CONV = REWR_CONV COND_T_THM
val COND_F_CONV = REWR_CONV COND_F_THM
end

fun TEST_CONV c = 
     (RATOR_CONV o RATOR_CONV o RAND_CONV) c THENC 
     (COND_T_CONV ORELSEC COND_F_CONV);

fun word8Define q = 
  let val absyn = Parse.Absyn q
      val (def_term,fn_names) = Defn.parse_defn absyn
      val clauses = strip_conj def_term
      val atom = #1 (strip_comb (#1 (dest_eq (hd clauses))))
      val name = fst (dest_atom atom)
      val params = map (hd o #2 o strip_comb o #1 o dest_eq) clauses
      val results = map (#2 o dest_eq) clauses
      val (num_params, var_param) =
        to_first_var (map cvt_param (zip params results)) []
      val s_num_params = sort (fn (x, _) => fn (y, _) => x < y) num_params
      val result_type = type_of (hd results)
      val results_no_gaps = 
        fill_results s_num_params
                     (case var_param of
                        SOME (var, res) => default (SOME var) res
                      | NONE => default NONE (mk_arb result_type))
                     (case var_param of
                        SOME (var, res) => K ()
                      | NONE => (fn () => WARN "word8Define" 
                                               "cases not exhaustive"))
                     0
      val defeqn = mk_eq (atom,
         list_mk_comb (inst [alpha |-> result_type] word8_cases_tm,
                       map snd results_no_gaps))
      val def = SPEC_ALL (new_definition(name^"_prim_def",defeqn))
      val const = lhs(concl def)
      val simp_def = WORD_RULE (PURE_ONCE_REWRITE_RULE [word8_cases_def] def)
      val for_eqns =
        case var_param of
          SOME _ => results_no_gaps
        | NONE => s_num_params

      val fargs = map (fn (num,_) => mk_comb(const,mk_n2w num)) for_eqns
      val CONV = RATOR_CONV (REWR_CONV simp_def) THENC BETA_CONV 
                 THENC REPEATC (TEST_CONV WORD_CONV)
      val thms = map CONV fargs
  in
    save_thm (name^"_def", LIST_CONJ thms)
  end
  handle e => Raise (wrap_exn "word8CasesLib" "word8Define" e);

fun word8Cases_on var = STRIP_ASSUME_TAC (Q.SPEC var word8Nchotomy) ;

fun word8GenTable f eval_case = 
LIST_CONJ (map (fn n => eval_case (mk_comb (f, mk_n2w n)))
               (upto 0 255))

fun word8GenCases f eval_case = 
let val table_thm = word8GenTable (Term f) eval_case
    val thm = (REWRITE_RULE [table_thm, COND_ID] o
               Q.ISPEC f o
               BETA_RULE o 
               PURE_ONCE_REWRITE_RULE [FUN_EQ_THM] o
               PURE_ONCE_REWRITE_RULE [word8_cases_def])
              word8Cases
in
  (thm, table_thm)
end

end

(*
time word8Define `f (x:word8) = 1`;
time word8Define `f (_:word8) = 1`;
time word8Define `f x = 1`;
time word8Define `f (x:word8) = x`;
time word8Define `f 1w = 1`;
time word8Define `(f 1w = 1) /\ (f x = 2)`;
time word8Define `(f 0w = 1) /\ (f x = 2) /\ (f 0w = 3)`;
time word8Define `(f 0w = 1) /\ (f 2w = 2) /\ (f 4w = 3)`;
time word8Define `(f 1w = 1) /\ (f 3w = 2) /\ (f 5w = 3)`;
time word8Define `(f 0w = 1) /\ (f 256w = 1)`;
time word8Define `(f 0 = 1)`;
time word8Define `(f (a b) = 1)`;
time word8Define 
 `(Sbox 0x0w = 0x63w)  /\ (Sbox 0x1w = 0x7Cw) /\ (Sbox 0x2w = 0x77w) /\
  (Sbox 0x3w = 0x7Bw) /\  (Sbox 0x4w = 0xF2w) /\ (Sbox 0x5w = 0x6Bw) /\
  (Sbox 0x6w = 0x6Fw) /\  (Sbox 0x7w = 0xC5w) /\ (Sbox 0x8w = 0x30w) /\
  (Sbox 0x9w = 0x1w) /\  (Sbox 0xAw = 0x67w) /\ (Sbox 0xBw = 0x2Bw) /\
  (Sbox 0xCw = 0xFEw) /\  (Sbox 0xDw = 0xD7w) /\ (Sbox 0xEw = 0xABw) /\
  (Sbox 0xFw = 0x76w) /\  (Sbox 0x10w = 0xCAw) /\ (Sbox 0x11w = 0x82w) /\
  (Sbox 0x12w = 0xC9w) /\  (Sbox 0x13w = 0x7Dw) /\ (Sbox 0x14w = 0xFAw) /\
  (Sbox 0x15w = 0x59w) /\  (Sbox 0x16w = 0x47w) /\ (Sbox 0x17w = 0xF0w) /\
  (Sbox 0x18w = 0xADw) /\  (Sbox 0x19w = 0xD4w) /\ (Sbox 0x1Aw = 0xA2w) /\
  (Sbox 0x1Bw = 0xAFw) /\  (Sbox 0x1Cw = 0x9Cw) /\ (Sbox 0x1Dw = 0xA4w) /\
  (Sbox 0x1Ew = 0x72w) /\  (Sbox 0x1Fw = 0xC0w) /\ (Sbox 0x20w = 0xB7w) /\
  (Sbox 0x21w = 0xFDw) /\  (Sbox 0x22w = 0x93w) /\ (Sbox 0x23w = 0x26w) /\
  (Sbox 0x24w = 0x36w) /\  (Sbox 0x25w = 0x3Fw) /\ (Sbox 0x26w = 0xF7w) /\
  (Sbox 0x27w = 0xCCw) /\  (Sbox 0x28w = 0x34w) /\ (Sbox 0x29w = 0xA5w) /\
  (Sbox 0x2Aw = 0xE5w) /\  (Sbox 0x2Bw = 0xF1w) /\ (Sbox 0x2Cw = 0x71w) /\
  (Sbox 0x2Dw = 0xD8w) /\  (Sbox 0x2Ew = 0x31w) /\ (Sbox 0x2Fw = 0x15w) /\
  (Sbox 0x30w = 0x4w) /\  (Sbox 0x31w = 0xC7w) /\ (Sbox 0x32w = 0x23w) /\
  (Sbox 0x33w = 0xC3w) /\  (Sbox 0x34w = 0x18w) /\ (Sbox 0x35w = 0x96w) /\
  (Sbox 0x36w = 0x5w) /\  (Sbox 0x37w = 0x9Aw) /\ (Sbox 0x38w = 0x7w) /\
  (Sbox 0x39w = 0x12w) /\  (Sbox 0x3Aw = 0x80w) /\ (Sbox 0x3Bw = 0xE2w) /\
  (Sbox 0x3Cw = 0xEBw) /\  (Sbox 0x3Dw = 0x27w) /\ (Sbox 0x3Ew = 0xB2w) /\
  (Sbox 0x3Fw = 0x75w) /\  (Sbox 0x40w = 0x9w) /\ (Sbox 0x41w = 0x83w) /\
  (Sbox 0x42w = 0x2Cw) /\  (Sbox 0x43w = 0x1Aw) /\ (Sbox 0x44w = 0x1Bw) /\
  (Sbox 0x45w = 0x6Ew) /\  (Sbox 0x46w = 0x5Aw) /\ (Sbox 0x47w = 0xA0w) /\
  (Sbox 0x48w = 0x52w) /\  (Sbox 0x49w = 0x3Bw) /\ (Sbox 0x4Aw = 0xD6w) /\
  (Sbox 0x4Bw = 0xB3w) /\  (Sbox 0x4Cw = 0x29w) /\ (Sbox 0x4Dw = 0xE3w) /\
  (Sbox 0x4Ew = 0x2Fw) /\  (Sbox 0x4Fw = 0x84w) /\ (Sbox 0x50w = 0x53w) /\
  (Sbox 0x51w = 0xD1w) /\  (Sbox 0x52w = 0x0w) /\ (Sbox 0x53w = 0xEDw) /\
  (Sbox 0x54w = 0x20w) /\  (Sbox 0x55w = 0xFCw) /\ (Sbox 0x56w = 0xB1w) /\
  (Sbox 0x57w = 0x5Bw) /\  (Sbox 0x58w = 0x6Aw) /\ (Sbox 0x59w = 0xCBw) /\
  (Sbox 0x5Aw = 0xBEw) /\  (Sbox 0x5Bw = 0x39w) /\ (Sbox 0x5Cw = 0x4Aw) /\
  (Sbox 0x5Dw = 0x4Cw) /\  (Sbox 0x5Ew = 0x58w) /\ (Sbox 0x5Fw = 0xCFw) /\
  (Sbox 0x60w = 0xD0w) /\  (Sbox 0x61w = 0xEFw) /\ (Sbox 0x62w = 0xAAw) /\
  (Sbox 0x63w = 0xFBw) /\  (Sbox 0x64w = 0x43w) /\ (Sbox 0x65w = 0x4Dw) /\
  (Sbox 0x66w = 0x33w) /\  (Sbox 0x67w = 0x85w) /\ (Sbox 0x68w = 0x45w) /\
  (Sbox 0x69w = 0xF9w) /\  (Sbox 0x6Aw = 0x2w) /\ (Sbox 0x6Bw = 0x7Fw) /\
  (Sbox 0x6Cw = 0x50w) /\  (Sbox 0x6Dw = 0x3Cw) /\ (Sbox 0x6Ew = 0x9Fw) /\
  (Sbox 0x6Fw = 0xA8w) /\  (Sbox 0x70w = 0x51w) /\ (Sbox 0x71w = 0xA3w) /\
  (Sbox 0x72w = 0x40w) /\  (Sbox 0x73w = 0x8Fw) /\ (Sbox 0x74w = 0x92w) /\
  (Sbox 0x75w = 0x9Dw) /\  (Sbox 0x76w = 0x38w) /\ (Sbox 0x77w = 0xF5w) /\
  (Sbox 0x78w = 0xBCw) /\  (Sbox 0x79w = 0xB6w) /\ (Sbox 0x7Aw = 0xDAw) /\
  (Sbox 0x7Bw = 0x21w) /\  (Sbox 0x7Cw = 0x10w) /\ (Sbox 0x7Dw = 0xFFw) /\
  (Sbox 0x7Ew = 0xF3w) /\  (Sbox 0x7Fw = 0xD2w) /\ (Sbox 0x80w = 0xCDw) /\
  (Sbox 0x81w = 0xCw) /\  (Sbox 0x82w = 0x13w) /\ (Sbox 0x83w = 0xECw) /\
  (Sbox 0x84w = 0x5Fw) /\  (Sbox 0x85w = 0x97w) /\ (Sbox 0x86w = 0x44w) /\
  (Sbox 0x87w = 0x17w) /\  (Sbox 0x88w = 0xC4w) /\ (Sbox 0x89w = 0xA7w) /\
  (Sbox 0x8Aw = 0x7Ew) /\  (Sbox 0x8Bw = 0x3Dw) /\ (Sbox 0x8Cw = 0x64w) /\
  (Sbox 0x8Dw = 0x5Dw) /\  (Sbox 0x8Ew = 0x19w) /\ (Sbox 0x8Fw = 0x73w) /\
  (Sbox 0x90w = 0x60w) /\  (Sbox 0x91w = 0x81w) /\ (Sbox 0x92w = 0x4Fw) /\
  (Sbox 0x93w = 0xDCw) /\  (Sbox 0x94w = 0x22w) /\ (Sbox 0x95w = 0x2Aw) /\
  (Sbox 0x96w = 0x90w) /\  (Sbox 0x97w = 0x88w) /\ (Sbox 0x98w = 0x46w) /\
  (Sbox 0x99w = 0xEEw) /\  (Sbox 0x9Aw = 0xB8w) /\ (Sbox 0x9Bw = 0x14w) /\
  (Sbox 0x9Cw = 0xDEw) /\  (Sbox 0x9Dw = 0x5Ew) /\ (Sbox 0x9Ew = 0xBw) /\
  (Sbox 0x9Fw = 0xDBw) /\  (Sbox 0xA0w = 0xE0w) /\ (Sbox 0xA1w = 0x32w) /\
  (Sbox 0xA2w = 0x3Aw) /\  (Sbox 0xA3w = 0xAw) /\ (Sbox 0xA4w = 0x49w) /\
  (Sbox 0xA5w = 0x6w) /\  (Sbox 0xA6w = 0x24w) /\ (Sbox 0xA7w = 0x5Cw) /\
  (Sbox 0xA8w = 0xC2w) /\  (Sbox 0xA9w = 0xD3w) /\ (Sbox 0xAAw = 0xACw) /\
  (Sbox 0xABw = 0x62w) /\  (Sbox 0xACw = 0x91w) /\ (Sbox 0xADw = 0x95w) /\
  (Sbox 0xAEw = 0xE4w) /\  (Sbox 0xAFw = 0x79w) /\ (Sbox 0xB0w = 0xE7w) /\
  (Sbox 0xB1w = 0xC8w) /\  (Sbox 0xB2w = 0x37w) /\ (Sbox 0xB3w = 0x6Dw) /\
  (Sbox 0xB4w = 0x8Dw) /\  (Sbox 0xB5w = 0xD5w) /\ (Sbox 0xB6w = 0x4Ew) /\
  (Sbox 0xB7w = 0xA9w) /\  (Sbox 0xB8w = 0x6Cw) /\ (Sbox 0xB9w = 0x56w) /\
  (Sbox 0xBAw = 0xF4w) /\  (Sbox 0xBBw = 0xEAw) /\ (Sbox 0xBCw = 0x65w) /\
  (Sbox 0xBDw = 0x7Aw) /\  (Sbox 0xBEw = 0xAEw) /\ (Sbox 0xBFw = 0x8w) /\
  (Sbox 0xC0w = 0xBAw) /\  (Sbox 0xC1w = 0x78w) /\ (Sbox 0xC2w = 0x25w) /\
  (Sbox 0xC3w = 0x2Ew) /\  (Sbox 0xC4w = 0x1Cw) /\ (Sbox 0xC5w = 0xA6w) /\
  (Sbox 0xC6w = 0xB4w) /\  (Sbox 0xC7w = 0xC6w) /\ (Sbox 0xC8w = 0xE8w) /\
  (Sbox 0xC9w = 0xDDw) /\  (Sbox 0xCAw = 0x74w) /\ (Sbox 0xCBw = 0x1Fw) /\
  (Sbox 0xCCw = 0x4Bw) /\  (Sbox 0xCDw = 0xBDw) /\ (Sbox 0xCEw = 0x8Bw) /\
  (Sbox 0xCFw = 0x8Aw) /\  (Sbox 0xD0w = 0x70w) /\ (Sbox 0xD1w = 0x3Ew) /\
  (Sbox 0xD2w = 0xB5w) /\  (Sbox 0xD3w = 0x66w) /\ (Sbox 0xD4w = 0x48w) /\
  (Sbox 0xD5w = 0x3w) /\  (Sbox 0xD6w = 0xF6w) /\ (Sbox 0xD7w = 0xEw) /\
  (Sbox 0xD8w = 0x61w) /\  (Sbox 0xD9w = 0x35w) /\ (Sbox 0xDAw = 0x57w) /\
  (Sbox 0xDBw = 0xB9w) /\  (Sbox 0xDCw = 0x86w) /\ (Sbox 0xDDw = 0xC1w) /\
  (Sbox 0xDEw = 0x1Dw) /\  (Sbox 0xDFw = 0x9Ew) /\ (Sbox 0xE0w = 0xE1w) /\
  (Sbox 0xE1w = 0xF8w) /\  (Sbox 0xE2w = 0x98w) /\ (Sbox 0xE3w = 0x11w) /\
  (Sbox 0xE4w = 0x69w) /\  (Sbox 0xE5w = 0xD9w) /\ (Sbox 0xE6w = 0x8Ew) /\
  (Sbox 0xE7w = 0x94w) /\  (Sbox 0xE8w = 0x9Bw) /\ (Sbox 0xE9w = 0x1Ew) /\
  (Sbox 0xEAw = 0x87w) /\  (Sbox 0xEBw = 0xE9w) /\ (Sbox 0xECw = 0xCEw) /\
  (Sbox 0xEDw = 0x55w) /\  (Sbox 0xEEw = 0x28w) /\ (Sbox 0xEFw = 0xDFw) /\
  (Sbox 0xF0w = 0x8Cw) /\  (Sbox 0xF1w = 0xA1w) /\ (Sbox 0xF2w = 0x89w) /\
  (Sbox 0xF3w = 0xDw) /\  (Sbox 0xF4w = 0xBFw) /\ (Sbox 0xF5w = 0xE6w) /\
  (Sbox 0xF6w = 0x42w) /\  (Sbox 0xF7w = 0x68w) /\ (Sbox 0xF8w = 0x41w) /\
  (Sbox 0xF9w = 0x99w) /\  (Sbox 0xFAw = 0x2Dw) /\ (Sbox 0xFBw = 0xFw) /\
  (Sbox 0xFCw = 0xB0w) /\  (Sbox 0xFDw = 0x54w) /\ (Sbox 0xFEw = 0xBBw) /\
  (Sbox 0xFFw = 0x16w)`;
*)

