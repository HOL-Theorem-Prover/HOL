(*===========================================================================*)
(* Exercise the automatic termination prover                                 *)
(*===========================================================================*)

open HolKernel boolLib bossLib listTheory Defn TotalDefn;

open arithmeticTheory;

local open stringLib in end

val _ = new_theory "termination_prover";

Definition encode_num_def:
  encode_num (n:num) =
    if n = 0 then [T; T]
    else if EVEN n then F :: encode_num ((n - 2) DIV 2)
    else T :: F :: encode_num ((n - 1) DIV 2)
End

Definition n2l_def:
  n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b)
End

local open numpairTheory nlistTheory in end

Definition nlistrec_def:
  nlistrec n f l = if l = 0 then n
                   else f (nfst (l - 1)) (nsnd (l - 1))
                          (nlistrec n f (nsnd (l - 1)))
Termination
  WF_REL_TAC `measure (SND o SND)` >> strip_tac >>
  ASSUME_TAC (Q.INST [`n` |-> `l - 1`] numpairTheory.nsnd_le) >> simp[]
End

(*---------------------------------------------------------------------------*)
(* Should be automatic                                                       *)
(*---------------------------------------------------------------------------*)

Definition test_def:
  test (l,n) s = if n = 0 then l else test (s::l,n - 1) s
Termination
  WF_REL_TAC ‘measure (SND o FST)’
End

Definition ramana_bug_def:
  bug a b x y u v =
  if a = 0 then x else let
    q = b DIV a;
    r = b MOD a;
    m = x - (u * q);
    n = y - (v * q);
    b = a; a = r; x = u; y = v; u = m; v = n in
      bug a b x y u v
End

(*---------------------------------------------------------------------------*)
(* From src/finite_maps/patriciaScript.sml                                   *)
(*---------------------------------------------------------------------------*)

Datatype:
 ptree = Empty | Leaf num 'a | Branch num num ptree ptree
End

Definition BRANCHING_BIT_def:
  BRANCHING_BIT p0 p1 =
    if (ODD p0 = EVEN p1) \/ (p0 = p1) then 0
    else SUC (BRANCHING_BIT (DIV2 p0) (DIV2 p1))
Termination
 WF_REL_TAC `measure (\(x,y). x + y)` \\ rw[]
   \\ Cases_on `ODD p0` \\ FULL_SIMP_TAC bool_ss []
   \\ FULL_SIMP_TAC bool_ss [GSYM ODD_EVEN, GSYM EVEN_ODD]
   \\ IMP_RES_TAC EVEN_ODD_EXISTS
   \\ SRW_TAC [ARITH_ss] [ADD1,
         ONCE_REWRITE_RULE [MULT_COMM] (CONJ ADD_DIV_ADD_DIV MULT_DIV)]
End

(*---------------------------------------------------------------------------*)
(* Illustrates need for case splitting on if-then-else in termination prover *)
(*---------------------------------------------------------------------------*)

local open bitTheory in end

Definition PEEK_def:
  PEEK Empty k = NONE /\
  PEEK (Leaf j d) k = (if k = j then SOME d else NONE) /\
  PEEK (Branch p m l r) k = PEEK (if BIT m k then l else r) k
End

Definition JOIN_def:
  JOIN (p0,t0,p1,t1) =
    let m = BRANCHING_BIT p0 p1 in
      if BIT m p0 then
        Branch (MOD_2EXP m p0) m t0 t1
      else
        Branch (MOD_2EXP m p0) m t1 t0
End

Definition ADD_def:
  (ADD Empty (k,e) = Leaf k e) /\
  (ADD (Leaf j d) (k,e) = (if j = k then Leaf k e
                          else JOIN (k, Leaf k e, j, Leaf j d))) ∧
  (ADD (Branch p m l r) (k,e) =
         if MOD_2EXP_EQ m k p then
           if BIT m k then
                Branch p m (ADD l (k,e)) r
              else
                Branch p m l (ADD r (k,e))
         else
           JOIN (k, Leaf k e, p, Branch p m l r))
End

(*---------------------------------------------------------------------------*)
(* Recursion in monads. From src/monad/more_monads/errorStateMonadScript.sml *)
(*---------------------------------------------------------------------------*)

Type M[local] = “:'state -> ('a # 'state) option”

Definition UNIT_DEF:
  UNIT (x:'b) : ('b,'a) M = \(s:'a). SOME (x, s)
End

Definition BIND_DEF:
  BIND (g: ('b, 'a) M) (f: 'b -> ('c, 'a) M) (s0:'a) =
    case g s0 of
      NONE => NONE
    | SOME (b,s) => f b s
End

Definition FOR_def:
 (FOR : num # num # (num -> (unit, 'state) M) -> (unit, 'state) M)
      (i, j, a) =
    if i = j then
        a i
     else
        BIND (a i) (\u. FOR (if i < j then i + 1 else i - 1, j, a))
Termination
  WF_REL_TAC `measure (\(i, j, a). if i < j then j - i else i - j)`
End

(*---------------------------------------------------------------------------*)
(* Functions over datatypes with nesting under type operators                *)
(*---------------------------------------------------------------------------*)

Datatype:
  term = Var num
       | Fnapp num (term list)
End

Definition vars_of_def:
  vars_of (Var n) = [n] ∧
  vars_of (Fnapp c ts) = FLAT (MAP vars_of ts)
End

Datatype:
  exp = VarExp string
      | ConstExp num
      | MonopExp exp
      | BinopExp (exp # exp)
      | FncallExp string (exp list)
End

Definition exp_vars_def:
 exp_vars (VarExp s) = {s} ∧
 exp_vars (ConstExp _) = {} ∧
 exp_vars (MonopExp e) = exp_vars e ∧
 exp_vars (BinopExp (e1,e2)) = exp_vars e1 UNION exp_vars e2 ∧
 exp_vars (FncallExp s elist) = FOLDR (λe s. exp_vars e UNION s) {} elist
End

Datatype:
  expr = VarExpr string
       | ConstExpr num
       | MonopExpr num expr
       | BinopExpr num (expr # expr)
       | CondExpr bexpr expr expr
       | FncallExpr string (expr list option)
  ;
  bexpr = BoolVarExpr string
        | BoolAndExpr (bexpr#bexpr)
        | BoolOrExpr (bexpr#bexpr)
        | BoolNotExpr bexpr
        | EqualExpr expr expr
End

Definition expr_bexpr_vars_def:
 expr_vars (VarExpr s) = {s} ∧
 expr_vars (ConstExpr _) = {} ∧
 expr_vars (MonopExpr _ e) = expr_vars e ∧
 expr_vars (BinopExpr _ (e1,e2)) = expr_vars e1 UNION expr_vars e2 ∧
 expr_vars (CondExpr b e1 e2) = bexpr_vars b UNION expr_vars e1 UNION expr_vars e2 ∧
 expr_vars (FncallExpr _ NONE) = {} ∧
 expr_vars (FncallExpr _ (SOME elist)) = FOLDR (λe s. expr_vars e UNION s) {} elist
 ∧
 bexpr_vars (BoolVarExpr s) = {s} ∧
 bexpr_vars (BoolAndExpr (b1,b2)) = bexpr_vars b1 UNION bexpr_vars b2 ∧
 bexpr_vars (BoolOrExpr (b1,b2)) = bexpr_vars b1 UNION bexpr_vars b2 ∧
 bexpr_vars (BoolNotExpr b) = bexpr_vars b ∧
 bexpr_vars (EqualExpr e1 e2) = expr_vars e1 UNION expr_vars e2
End

(*---------------------------------------------------------------------------*)
(* Mutual recursion example pinched from

  https://github.com/verifereum/verifereum/blob/main/util/contractABIScript.sml#L66

  Modifications: IntV (int) --> IntV(num)
               : byte --> word8
*)

local open wordsLib in end

Datatype:
  abi_type
  = Uint num
  | Int num
  | Address
  | Bool
  | Fixed num num
  | Ufixed num num
  | Bytes (num option)
  | String
  | Array (num option) abi_type
  | Tuple (abi_type list)
End

Datatype:
  abi_value
  = NumV num
  | IntV num
  | BoolV bool
  | BytesV (word8 list)
  | ListV (abi_value list)
End

Definition valid_int_bound_def:
  valid_int_bound n = (0 < n ∧ n ≤ 256 ∧ n MOD 8 = 0)
End

Definition valid_fixed_bounds_def:
  valid_fixed_bounds n m =
  (8 ≤ m ∧ m ≤ 256 ∧ m MOD 8 = 0 ∧
   0n < n ∧ n ≤ 80)
End

Definition valid_length_def[simp]:
  valid_length NONE _ = T ∧
  valid_length (SOME n) ls = (LENGTH ls = n)
End

Definition valid_bytes_bound_def[simp]:
  valid_bytes_bound NONE = T ∧
  valid_bytes_bound (SOME m) = (0 < m ∧ m ≤ 32)
End

Definition int_bits_bound_def:
  int_bits_bound i n ⇔ i < 2 ** PRE n
End

(* NB: the invocation of LIST_REL needs an eta-expanded has_type,
   otherwise ugly failure. *)

Definition has_type_def:
  has_type (Uint n)     (NumV v)    = (v < 2 ** n ∧ valid_int_bound n) ∧
  has_type (Int n)      (IntV i)    = (int_bits_bound i n ∧ valid_int_bound n) ∧
  has_type Address      (NumV v)    = (v < 2 ** 160) ∧
  has_type Bool         (NumV v)    = (v < 2) ∧
  has_type (Fixed n m)  (IntV i)    = (int_bits_bound i m ∧ valid_fixed_bounds n m) ∧
  has_type (Ufixed n m) (NumV v)    = (v < 2 ** m ∧ valid_fixed_bounds n m) ∧
  has_type (Bytes b)    (BytesV bs) = (valid_bytes_bound b ∧ valid_length b bs) ∧
  has_type String       (BytesV bs) = T ∧
  has_type (Array b t)  (ListV vs)  = EVERY (has_type t) vs ∧
  has_type (Tuple ts)   (ListV vs)  = LIST_REL (λty v. has_type ty v) ts vs ∧
  has_type  other         wise      = F
End

val _ = export_theory();
