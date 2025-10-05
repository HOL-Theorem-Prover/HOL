Theory lisp_semantics
Ancestors
  string finite_map pred_set list sum

(*****************************************************************************)
(* Relational semantics for Pure LISP as formalised by Mike Gordon           *)
(* for the 2006 ACL2 workshop.                                               *)
(*****************************************************************************)


(*****************************************************************************)
(* An atom is Nil or a number or a string                                    *)
(*****************************************************************************)

val _ =
 Hol_datatype
  `atom = Nil | Number of num | String of string`;

(*****************************************************************************)
(* An S-expression is an atom or a dotted pair (cons-cell)                   *)
(*****************************************************************************)

val _ =
 Hol_datatype
  `sexpression = A of atom | Cons of sexpression => sexpression`;

(*****************************************************************************)
(* Syntax of Pure Lisp                                                       *)
(*****************************************************************************)

val _ =
 Hol_datatype
  `term = Con of sexpression
        | Var of string
        | App of func => term list
        | Ite of (term # term)list;

   func = FunCon of string
        | FunVar of string
        | Lambda of string list => term
        | Label  of string => func`;

(*****************************************************************************)
(* Some utility values and functions                                         *)
(*****************************************************************************)

Definition False_def:
   False = A Nil
End

Definition isTrue_def:
   isTrue s <=> ~(s = False) /\ ~(s = A (String "nil"))
End

Definition True_def:
   True = A(String "t")
End

Definition Car_def:
   Car(Cons s1 s2) = s1
End

Definition Cdr_def:
   Cdr(Cons s1 s2) = s2
End

Definition delete_Nil_aux_def:
  (delete_Nil_aux Nil = String "nil") /\
  (delete_Nil_aux (Number n) = Number n) /\
  (delete_Nil_aux (String s) = String s)
End

Definition delete_Nil_def:
  (delete_Nil (A a) = A (delete_Nil_aux a)) /\
  (delete_Nil (Cons s t) = Cons (delete_Nil s) (delete_Nil t))
End

Definition Equal_def:
   Equal (x,y) = if delete_Nil x = delete_Nil y:sexpression then True else False
End

Definition Atomp_def:
   (Atomp (A a) = True)
   /\
   (Atomp _ = False)
End

Definition Consp_def:
   (Consp (A a) = False)
   /\
   (Consp _ = True)
End

Definition Numberp_def:
   (Numberp (A (Number n)) = True)
   /\
   (Numberp _ = False)
End

Definition Symbolp_def:
   (Symbolp (A (String s)) = True)
   /\
   (Symbolp (A Nil) = True)
   /\
   (Symbolp _ = False)
End

Definition Add_def:
   Add (A(Number m)) (A(Number n)) = A(Number(m+n))
End

Definition Sub_def:
   Sub ((A(Number m)),(A(Number n))) = A(Number(m-n))
End

Definition Mult_def:
   Mult (A(Number m)) (A(Number n)) = A(Number(m*n))
End

Definition Div_def:
   Div ((A(Number m)),(A(Number n))) = A(Number(m DIV n))
End

Definition Mod_def:
   Mod ((A(Number m)),(A(Number n))) = A(Number(m MOD n))
End

Definition Less_def:
   Less ((A(Number m)),(A(Number n))) = if m < n then True else False
End

Definition FunConSem_def:
   FunConSem s sl =
    if s = "car"     then Car(EL 0 sl)                else
    if s = "cdr"     then Cdr(EL 0 sl)                else
    if s = "cons"    then Cons(EL 0 sl) (EL 1 sl)     else
    if s = "+"       then FOLDL Add (A(Number 0)) sl  else
    if s = "*"       then FOLDL Mult (A(Number 1)) sl else
    if s = "-"       then Sub(EL 0 sl,EL 1 sl)        else
    if s = "div"     then Div(EL 0 sl,EL 1 sl)        else
    if s = "mod"     then Mod(EL 0 sl,EL 1 sl)        else
    if s = "<"       then Less(EL 0 sl,EL 1 sl)       else
    if s = "equal"   then Equal(EL 0 sl,EL 1 sl)      else
    if s = "atomp"   then Atomp(EL 0 sl)              else
    if s = "consp"   then Consp(EL 0 sl)              else
    if s = "numberp" then Numberp(EL 0 sl)            else
    if s = "symbolp" then Symbolp(EL 0 sl)            else
    ARB
End

Definition FunConSemOK_def:
   FunConSemOK s sl =
    if s = "car"     then ?u v. sl = [Cons u v]   else
    if s = "cdr"     then ?u v. sl = [Cons u v]   else
    if s = "cons"    then ?u v. sl = [u; v]       else
    if s = "+"       then (!x. MEM x sl ==> ?n. x = A (Number n)) else
    if s = "-"       then ?m n. sl = [A (Number m); A (Number n)] else
    if s = "*"       then (!x. MEM x sl ==> ?n. x = A (Number n)) else
    if s = "div"     then ?m n. sl = [A (Number m); A (Number n)] else
    if s = "mod"     then ?m n. sl = [A (Number m); A (Number n)] else
    if s = "<"       then ?m n. sl = [A (Number m); A (Number n)] else
    if s = "equal"   then ?u v. sl = [u; v]       else
    if s = "atomp"   then ?u.   sl = [u]          else
    if s = "consp"   then ?u.   sl = [u]          else
    if s = "numberp" then ?u.   sl = [u]          else
    if s = "symbolp" then ?u.   sl = [u]          else
    F
End

(*****************************************************************************)
(* An environment (alist) is a finite function from names (strings) to       *)
(* values of type ``:sexpression + func`` (so variables and                  *)
(* Label-defined functions share the same namespace).                        *)
(*****************************************************************************)

(*****************************************************************************)
(* VarBind a xl sl extends a by binding each string in xl to the             *)
(* S-expression at the corresponding position in sl. If xl is shorter than   *)
(* sl, then only the first n elements of sl are used, where n is the         *)
(* length of x. If xl is longer than sl, than sl is padded with NILs.        *)
(*                                                                           *)
(* Subtle point: with the semantics in which clock timeout returns NONE      *)
(* having VarBind  only partially specified is no problem, but               *)
(* with the semantics in which timeout returns an S-expression it is         *)
(* tricky to distinguish the arbitrary value returned when VarBind is        *)
(* applied to lists of different lists from a real value.                    *)
(* We thus totalise VarBind as described above.                              *)
(*****************************************************************************)

Definition VarBind_def:
   (VarBind a [] sl = (a : (string |-> sexpression + func)))
   /\
   (VarBind a (x::xl) [] = (VarBind (a |+ (x, INL(A Nil))) xl []))
   /\
   (VarBind a (x::xl) (s::sl) = (VarBind (a |+ (x, INL s)) xl sl))
End

(*****************************************************************************)
(* 55FunBind a f fn extends a by binding fn to f                               *)
(*****************************************************************************)

Definition FunBind_def:
   FunBind (a:string|->sexpression+func) f fn = a |+ (f, INR fn)
End

(*****************************************************************************)
(* Operational semantics of Pure Lisp using three inductive relations:       *)
(*                                                                           *)
(*  R_ap (fn,args,a) s - fn applied to args evaluates to s with alist a      *)
(*  R_ev (e,a) s        - term e evaluates to S-expression s with alist a    *)
(*  R_evl (el,a) sl     - term list el evaluates to S-expression list sl     *)
(*                                                                           *)
(* The names R_evl_rules, R_evl_ind, R_evl_cases are the ones                *)
(* automatically generated to name the theorems in the theory.               *)
(*                                                                           *)
(*****************************************************************************)

val (R_ap_rules,R_ap_ind,R_ap_cases) =
 Hol_reln
 `(!s a.
    R_ev (Con s, a) s)
  /\
  (!x a.
    x IN FDOM a /\ ISL (a ' x) ==>
    R_ev (Var x, a) (OUTL(a ' x)))
  /\
  (!fc args a.
    FunConSemOK fc args ==>
    R_ap (FunCon fc,args,a) (FunConSem fc args))
  /\
  (!fn el args s a.
    R_evl (el,a) args /\ R_ap (fn,args,a) s /\ (LENGTH args = LENGTH el)
    ==> R_ev (App fn el,a) s)
  /\
  (!a.
    R_ev (Ite [], a) False)
  /\
  (!e1 e2 el s a.
    R_ev (e1,a) False /\ R_ev (Ite el,a) s
    ==> R_ev (Ite ((e1,e2)::el),a) s)
  /\
  (!e1 e2 el s1 s a.
    R_ev (e1,a) s1 /\ isTrue s1 /\ R_ev (e2,a) s
    ==>
    R_ev (Ite ((e1,e2)::el),a) s)
  /\
  (!x fn args s a.
    R_ap (fn,args,FunBind a x fn) s ==> R_ap(Label x fn,args,a) s)
  /\
  (!fv args s a.
    fv NOTIN {"quote";"cond";"car";"cdr";"cons";"+";"-";"*";"div";"mod";"<";
              "equal";"atomp";"consp";"symbolp";"numberp"} /\
    fv IN FDOM a /\ ISR (a ' fv) /\
    R_ap (OUTR(a ' fv),args,a) s ==> R_ap (FunVar fv,args,a) s)
  /\
  (!xl e args s a.
    (LENGTH args = LENGTH xl) /\ R_ev (e,VarBind a xl args) s
    ==> R_ap (Lambda xl e,args,a) s)
  /\
  (!a.
    R_evl ([],a) [])
  /\
  (!e el s sl a.
    R_ev (e,a) s /\ R_evl (el,a) sl
    ==> R_evl (e::el,a) (s::sl))`;

