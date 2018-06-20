
open HolKernel Parse boolLib bossLib;
open realTheory finite_mapTheory machine_ieeeTheory;

val _ = new_theory "daisy";

val _ = Datatype ` X = Var string | Const string `
val _ = Datatype ` F = Add F F | Sub F F | Uminus F
                     | Mul F F | Div F F | Sqrt F | X X `
val _ = Datatype ` C = LessEq F F | Less F F
                     | GreaterEq F F | Greater F F `
val _ = Datatype ` B = Let string F B | Exp F `
val _ = Datatype ` D = If C D D | Simple B) `
val _ = Datatype ` S = Conj S S | Disj S S | Not S | Cons C `
val _ = Datatype ` A = Err string string | Assert S `
val _ = Datatype ` L = Rec B | NonRec D`
val _ = Datatype ` P = Func (string list) (* inputs/outputs *)
                            (A list) (* requires *)
                            L (* body *)`

val _ = Datatype ` ops = <| less : 'a -> 'a -> bool
                          ; less_eq : 'a -> 'a -> bool
                          ; greater : 'a -> 'a -> bool
                          ; greater_eq : 'a -> 'a -> bool
                          ; add : 'a -> 'a -> 'a
                          ; uminus : 'a -> 'a
                          ; sub : 'a -> 'a -> 'a
                          ; mul : 'a -> 'a -> 'a
                          ; div : 'a -> 'a -> 'a
                          ; sqrt : 'a -> 'a
                          ; to_real : 'a -> float_value
                          ; from_real : real -> 'a option
                          ; parse : string -> 'a
                          |>`

val eval_X_def = Define `
  (eval_X c env (Var v) = env ' v) /\
  (eval_X c env (Const str) = c.parse str)`

val eval_F_def = Define `
  (eval_F c env (X x) = eval_X c env x) /\
  (eval_F c env (Add f1 f2) = c.add (eval_F c env f1) (eval_F c env f2)) /\
  (eval_F c env (Div f1 f2) = c.div (eval_F c env f1) (eval_F c env f2))`

val eval_C_def = Define `
  (eval_C c env (LessEq f1 f2) = c.less_eq (eval_F c env f1) (eval_F c env f2))`

val eval_B_def = Define `
  (eval_B c env (Let v f b) = eval_B c (env |+ (v,eval_F c env f)) b) /\
  (eval_B c env (Exp f) = (eval_F c env f,env))`

val eval_D_def = Define `
  (eval_D c env (Simple b) = eval_B c env b)`

val eval_S_def = Define `
  (eval_S c env (Cons x) = eval_C c env x)`

val eval_A_def = Define `
  (eval_A c env (Err _ _) = T (* checked elsewhere *)) /\
  (eval_A c env (Assert s) = eval_S c env s)`

val has_lower_bound_def = Define `
  (has_lower_bound v (Assert (Cons (LessEq (X (Const r)) (X (Var w))))::rest) =
     ((w = v) \/ has_lower_bound v rest)) /\
  (has_lower_bound v (Assert (Cons (Less (X (Const r)) (X (Var w))))::rest) =
     ((w = v) \/ has_lower_bound v rest)) /\
  (has_lower_bound v _ = F) (* not complete *)`

val has_upper_bound_def = Define `
  (has_upper_bound v [] = F) /\
  (has_upper_bound v (Assert (Cons (LessEq (X (Var w)) (X (Const r))))::rest) =
     ((w = v) \/ has_upper_bound v rest)) /\
  (has_upper_bound v (Assert (Cons (Less (X (Var w)) (X (Const r))))::rest) =
     ((w = v) \/ has_upper_bound v rest)) /\
  (has_upper_bound v _ = F) (* not complete *)`

val req_holds_def = Define `
  req_holds reqs env <=>
    FEVERY (\(v,r). has_lower_bound v reqs /\ has_upper_bound v reqs) env`

val eval_P_def = Define `
  eval_P c inputs (Func args requires body) (n:num) =
    if req_holds requires inputs then
      case body of
      | NonRec d => SOME [FST (eval_D c inputs d)]
      | Rec b  =>
          if n = 0 then
            SOME (MAP (\v. inputs ' v) args)
          else
            let (_,env) = eval_B c inputs b in
              eval_P c env (Func args requires body) (n-1)
    else NONE`

(* real configuration *)

val real_conf = Define `
  real_conf = <| less := (<):real -> real -> bool
               ; less_eq := (<=)
               ; add := (+)
               ; uminus := (\r. 0-r)
               ; sub := (-)
               ; mul := $*
               ; div := (/)
               ; sqrt := sqrt
               ; to_real := Float  (* unnecessary *)
               ; from_real := SOME (* unnecessary *)
               ; parse := ARB |>`

(* floating pointt configurations *)

val fp32_conf = Define `
  fp32_conf = <| less := fp32_lessThan
               ; less_eq := fp32_lessEqual
               ; greater := fp32_greaterThan
               ; greater_eq := fp32_greaterEqual
               ; add := fp32_add roundTiesToEven
               ; uminus := fp32_negate
               ; sub := fp32_sub roundTiesToEven
               ; mul := fp32_mul roundTiesToEven
               ; div := fp32_div roundTiesToEven
               ; sqrt := fp32_sqrt roundTiesToEven
               ; parse := ARB
               ; to_real := fp32_to_real
               ; from_real := \r. let w = real_to_fp32 roundTiesToEven r in
                                    case fp32_to_real w of
                                    | Float _ => SOME w
                                    | _ => NONE |>`

val fp64_conf = Define `
  fp64_conf = <| less := fp64_lessThan
               ; less_eq := fp64_lessEqual
               ; greater := fp64_greaterThan
               ; greater_eq := fp64_greaterEqual
               ; add := fp64_add roundTiesToEven
               ; uminus := fp64_negate
               ; sub := fp64_sub roundTiesToEven
               ; mul := fp64_mul roundTiesToEven
               ; div := fp64_div roundTiesToEven
               ; sqrt := fp64_sqrt roundTiesToEven
               ; parse := ARB
               ; to_real := fp64_to_real
               ; from_real := \r. let w = real_to_fp64 roundTiesToEven r in
                                    case fp64_to_real w of
                                    | Float _ => SOME w
                                    | _ => NONE |>`

(* correctness provided by Rosa *)

val inputs_ok_def = Define `
  inputs_ok c inputs fp_inputs reqs =
    (FDOM inputs = FDOM fp_inputs) /\
    EVERY (eval_A real_conf inputs) reqs /\
    (* each Err requirement must be satisfied *)
    (∀v i. MEM (Err v i) reqs ==>
           ∃fp r r'. (FLOOKUP inputs v = SOME r) /\
                     (FLOOKUP fp_inputs v = SOME fp) /\
                     (c.to_real fp = Float r') /\
                     abs (r - r') <= real_conf.parse i) /\
    (* each variable without an Err-requirement must be the closes fp *)
    ∀v r. (FLOOKUP inputs v = SOME r) /\ (∀i. ~(MEM (Err v i) reqs)) ==>
          ∃fp. (FLOOKUP fp_inputs v = SOME fp) /\
               (c.from_real r = SOME fp)`

val distance_def = Define `
  distance c r fp (i,b,e) <=>
    ∃r'. (c.to_real fp = Float r') /\
         abs (r - r') <= real_conf.parse i /\
         real_conf.parse b <= r' /\ r' <= real_conf.parse e`

val every3_def = Define `
  (every3 p [] [] [] = T) /\
  (every3 p (x::xs) (y::ys) (z::zs) = p x y z /\ every3 p xs ys zs)`;

val rosa_correctness_def = Define `
  rosa_correctness fp_conf func limit ensures =
    case func of Func args reqs _ =>
      ∀inputs res fp_inputs.
        (eval_P real_conf inputs func limit = SOME res) /\
        inputs_ok fp_conf inputs fp_inputs reqs  ==>
        ∃fp_res.
          (eval_P fp_conf fp_inputs func limit = SOME fp_res) /\
          every3 (distance fp_conf) res fp_res ensures`

(* pretty printing used by daisyLib *)

val _ = Define `
  (x_str (Var str) = str) /\ (x_str (Const str) = str) `

val _ = Define `
  (f_str (Add f1 f2) = "(" ++ f_str f1 ++ " + " ++ f_str f2 ++ ")") /\
  (f_str (X x) = x_str x)`

val _ = Define `
  (c_str (LessEq f1 f2) = "(" ++ f_str f1 ++ " <= " ++ f_str f2 ++ ")") `

val _ = Define `
  (b_str (Let v f b) = "val " ++ v ++ " = " ++ f_str f ++ "\n") /\
  (b_str (Exp f) = f_str f ++ "\n")`

val _ = Define `
  (d_str (Simple b) = b_str b)`

val _ = Define `
  (s_str (Conj s1 s2) = "(" ++ s_str s1 ++ " && " ++ s_str s2 ++ ")") /\
  (s_str (Not s1) = "!(" ++ s_str s1 ++ ")") /\
  (s_str (Cons c) = "(" ++ c_str c ++ ")")`

val _ = Define `
  (a_str (Err v i) = "(" ++ v ++ " +/- " ++ i ++ ")") /\
  (a_str (Assert s) = "(" ++ s_str s ++ ")")`

val _ = Define `
  (l_str (NonRec d) = d_str d)`

val sep_str_def = Define `
  (sep_str sep [] = "") /\
  (sep_str sep [x] = x) /\
  (sep_str sep (x::xs) = x ++ sep ++ sep_str sep xs) `

val _ = Define `
  (p_str name (Func args reqs l) =
     "import daisy.lang._\n" ++
     "import Real._\n" ++
     "object Program {\n" ++
     "def " ++ name ++ "(" ++
     sep_str ", " (MAP (\v. v ++ ": Real") args) ++ "):Real = {\n" ++
     "require(" ++ sep_str " && " (MAP a_str reqs) ++ ")\n" ++
     l_str l ++ "}\n}")`

val _ = export_theory();
