(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

structure CCSSyntax :> CCSSyntax =
struct

open HolKernel Parse boolLib bossLib;
open PFset_conv computeLib;
open CCSLib CCSTheory;

structure Parse = struct
  open Parse
  val (Type, Term) = parse_from_grammars CCSTheory.CCS_grammars
end
open Parse

(******************************************************************************)
(*                                                                            *)
(*          Auxiliary ML functions for dealing with CCS syntax                *)
(*                                                                            *)
(******************************************************************************)

val name   = prim_mk_const {Name="name",   Thy="CCS"};
val coname = prim_mk_const {Name="coname", Thy="CCS"};
val tau    = prim_mk_const {Name="NONE",   Thy="option"};
val NIL    = prim_mk_const {Name="nil",    Thy="CCS"};
val restr  = prim_mk_const {Name="restr",  Thy="CCS"};

(* Define the destructors related to the constructors of the type Label. *)
fun args_label l = let
    val (opn, s) = dest_comb l
in
    if same_const opn name orelse
       same_const opn coname
    then (opn, s)
    else failwith "term not a CCS label"
end;

val (_, _, arg_name, _)         = HolKernel.syntax_fns1 "CCS" "name";
val (_, _, arg_coname, _)       = HolKernel.syntax_fns1 "CCS" "coname";
val (_, _, arg_action, _)       = HolKernel.syntax_fns1 "option" "SOME";
val (_, _, arg_compl, _)        = HolKernel.syntax_fns1 "CCS" "COMPL_ACT";
val (_, _, arg_relabelling, _)  = HolKernel.syntax_fns1 "CCS" "RELAB";
val (_, _, arg_ccs_var, _)      = HolKernel.syntax_fns1 "CCS" "var";
val (_, _, args_prefix, _)      = HolKernel.syntax_fns2 "CCS" "prefix";
val (_, _, args_sum, _)         = HolKernel.syntax_fns2 "CCS" "sum";
val (_, _, args_par, _)         = HolKernel.syntax_fns2 "CCS" "par";
val (_, _, args_restr, _)       = HolKernel.syntax_fns2 "CCS" "restr";

fun args_restr tm = let
    val (opn, [lset, P]) = strip_comb tm
in
    if same_const opn restr then
        (P, lset)
    else
        failwith "term not CCS restriction"
end;

val (_, _, args_relab, _)       = HolKernel.syntax_fns2 "CCS" "relab";
val (_, _, args_rec, _)         = HolKernel.syntax_fns2 "CCS" "rec";

(* Define predicates related to the destructors above. *)
val is_name             = can arg_name;
val is_coname           = can arg_coname;
val is_label            = can arg_action;
fun is_tau u            = same_const u tau;
val is_compl            = can arg_compl;
fun is_nil tm           = same_const tm NIL;
val is_ccs_var          = can arg_ccs_var;
val is_prefix           = can args_prefix;
val is_sum              = can args_sum;
val is_par              = can args_par;
val is_restr            = can args_restr;
val is_relab            = can args_relab;
val is_rec              = can args_rec;

(* Define construction of CCS terms. *)
fun mk_name    s        = ``name ^s``;
fun mk_coname  s        = ``coname ^s``;
fun mk_label   l        = ``label ^l``;
fun mk_ccs_var X        = ``var ^X``;
fun mk_prefix (u, P)    = ``prefix ^u ^P``;
fun mk_sum    (P1, P2)  = ``sum ^P1 ^P2``;
fun mk_par    (P1, P2)  = ``par ^P1 ^P2``;
fun mk_restr  (P, lset) = ``restr ^lset ^P``;
fun mk_relab  (P, f)    = ``relab ^P ^f``;
fun mk_rec    (X, E)    = ``rec ^X ^E``;

(* Define flattening of a CCS summation. *)
fun flat_sum tm =
  if not (is_sum tm) then [tm]
  else let val (t1, t2) = args_sum tm in
           append (flat_sum t1) (flat_sum t2)
       end;

fun ladd x l =
  if (null l) then [x] else [mk_sum (x, hd l)];

local
  fun helper (prima, mark, dopo, exp) =
    if exp ~~ mark then (prima, dopo)
    else if is_sum exp then
      let val (a, b) = args_sum exp
      in if b ~~ mark then ([a], dopo)
         else helper (prima, mark, (ladd b dopo), a)
      end
    else
      failwith "FIND_SMD"
in
    fun FIND_SMD prima mark dopo exp = helper (prima, mark, dopo, exp)
end;

(* Given a list of terms, the function build_sum builds a CCS term which is
   the summation of the terms in the list (associating to the right). *)
local
    fun helper (nil, typ)  = mk_const ("nil", typ)
      | helper ([t], typ)  = t
      | helper (t::l, typ) = mk_sum (t, helper (l, typ));
in
  fun build_sum ls =
    if null ls then
        failwith "can't determine the type"
    else
        helper (ls, type_of (hd ls))
end;

(* Given a list of summands sumL and an instance ARBtm of the term ARB': CCS,
   the function sum_to_fun sumL ARBtm n returns a function which associates
   each summand to its index, starting from index n. *)
fun sum_to_fun [] ARBtm n = ARBtm
  | sum_to_fun sumL ARBtm n =
    ``if (x = ^n) then ^(hd sumL) else ^(sum_to_fun (tl sumL) ARBtm ``SUM ^n``)``;

(******************************************************************************)
(*                                                                            *)
(*          Auxiliary ML functions for dealing with CCS syntax                *)
(*                                                                            *)
(******************************************************************************)

(* Conversion that implements a decision procedure for equality of labels. *)
fun Label_EQ_CONV lab_eq = let
    val (l1, l2) = dest_eq lab_eq;
    val (op1, s1) = args_label l1
    and (op2, s2) = args_label l2
in
    if op1 ~~ op2 then
        let val thm = EVAL_CONV ``^s1 = ^s2`` in
            if same_const op1 name then
                TRANS (ISPECL [s1, s2] (CONJUNCT1 Label_11)) thm
            else
                TRANS (ISPECL [s1, s2] (CONJUNCT2 Label_11)) thm
        end
    else if same_const op1 name andalso
            same_const op2 coname then (* not (op1 = op2) *)
        ISPECL [s1, s2] Label_not_eq (* (op1 = "coname") & (op2 = "name") *)
    else
        ISPECL [s1, s2] Label_not_eq'
end;

(* Conversion that proves/disproves membership of a label to a set of labels. *)
fun Label_IN_CONV l L = IN_CONV Label_EQ_CONV ``^l IN ^L``;

(* Conversion that implements a decision procedure for equality of actions. *)
fun Action_EQ_CONV act_eq = let
    val (u1, u2) = dest_eq act_eq
in
    if (is_tau u1 andalso is_tau u2) then
        EQT_INTRO (REFL u1)
    else if (is_tau u1 andalso is_label u2) then
        EQF_INTRO (ISPEC (arg_action u2) Action_distinct)
    else if (is_label u1 andalso is_tau u2) then
        EQF_INTRO (ISPEC (arg_action u1) Action_distinct_label)
    else
        let val l1 = arg_action u1 (* u1, u2 are both labels *)
            and l2 = arg_action u2;
            val (op1, s1) = args_label l1
            and (op2, s2) = args_label l2
            and thm = Label_EQ_CONV ``^l1 = ^l2``
        in
            if op1 ~~ op2 then
                if same_const op1 name then
                    TRANS (ISPECL [``name ^s1``, ``name ^s2``] Action_11) thm
                else
                    TRANS (ISPECL [``coname ^s1``, ``coname ^s2``] Action_11) thm
            else if same_const op1 name andalso
                    same_const op2 coname then (* not (op1 = op2) *)
                TRANS (ISPECL [``name ^s1``, ``coname ^s2``] Action_11)
                      (ISPECL [s1, s2] Label_not_eq)
            else (* (op1 = "coname") & (op2 = "name") *)
                TRANS (ISPECL [``coname ^s1``, ``name ^s2``] Action_11)
                      (ISPECL [s1, s2] Label_not_eq')
        end
end;

(* Conversion that proves/disproves membership of an action to a set of actions. *)
fun Action_IN_CONV u A = IN_CONV Action_EQ_CONV ``^u IN ^A``;

(* Conversion for evaluating a relabelling function fc (in conditional form). *)
fun RELAB_EVAL_CONV fc = let
    val c = snd (dest_comb fc)
in
    if is_cond c then
        let val (b, l, r) = dest_cond c;
            val (s1, s2) = dest_eq b;
            val thm = EVAL_CONV ``^s1 = ^s2``;
            val thm' = REWRITE_RHS_RULE [thm] (REFL fc)
        in
            TRANS thm' (RELAB_EVAL_CONV (rconcl thm'))
        end
    else
        REFL fc
end;

end (* struct *)
