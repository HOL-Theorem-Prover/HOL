structure SALGen :> SALGen =
struct

open HolKernel Parse boolLib pairLib pairSyntax bossLib 
     PairRules numSyntax basic SALTheory;

(* --------------------------------------------------------------------*)
(* Generate SAL code for a FIL program                                 *)
(* --------------------------------------------------------------------*)

structure M = Binarymap
structure S = Binaryset
val N = numSyntax.num;

(* --------------------------------------------------------------------*)
(* Datatypes, Commonly-used variables and functions                    *)
(* --------------------------------------------------------------------*)

val nop = Term `NOP`;
val reduce = Term `Reduce`;
val union = Term `UNION`;

fun get_output exp =
  if is_plet exp then
     let val (v, M, N) = dest_plet exp
     in
         get_output N
     end
  else
     exp

(* --------------------------------------------------------------------*)
(* Auxiliary functions manipulating labels                             *)
(* --------------------------------------------------------------------*)

(* Generate the next label *)

val label_index = ref 0;

fun next_label () = 
  let val _ = label_index := !label_index + 1;
      val l = mk_comb (Term `L`, term_of_int (!label_index)); 
  in  
      l
  end;

(* Obtain the entry label and exit label of a structure *)

fun get_entry_label s = 
  let 
    val (combinator, args) = strip_comb s;
    val comb_str = #1 (dest_const combinator);    
  in
    if comb_str = "UNION" then     
      get_entry_label (hd args)  (* from the first sub-structure of the union *)
    else   (* ASG, IFGOTO, GOTO *)
      hd args
  end;

fun get_exit_label s = 
  let 
    val (combinator, args) = strip_comb s;
    val comb_str = #1 (dest_const combinator);    
  in
    if comb_str = "UNION" then     
      get_exit_label (hd (tl args))  (* from the second sub-structure of the union *)
    else if comb_str = "ASG" orelse comb_str = "GOTO" then
      last args
    else
      raise Fail "Cannot get the exit label of an IFGOTO structure"
  end;

(* --------------------------------------------------------------------*)
(* Code generation for conditional structures                          *)
(* --------------------------------------------------------------------*)

fun gen_cnd_f t =
  mk_pabs (hd (free_vars t), t)
  handle e => (print "mk_cnd_f: errors occur while generating the condition function"; Raise e);

(*
fun gen_conditional (c, s1, s2) = 
  let 
     val (l2,l4) = (get_entry_label s1, get_exit_label s1);
     val (l1,l2) = (next_label(), next_label());
         val stm1 = list_mk_comb (inst [alpha |-> type_of v] (Term`ASG`), [l1, v, M, l2]);
    val ifgoto_stm = mk_comb
*)

(* --------------------------------------------------------------------*)
(* Code generation                                                     *)
(* --------------------------------------------------------------------*)

fun gen_code (entry_l, t, exit_l) =
   if is_atom t then
      nop

   else if is_let t then                        (*  exp = LET (\v. N) M  *)
     let 
         val (v,M,N) = dest_plet t
         val union = inst [alpha |-> type_of v] (Term `UNION`);
         val new_l = next_label();
         val stm1 = list_mk_comb (inst [alpha |-> type_of v] (Term`ASG`), [entry_l, v, M, new_l]);
         val stm2 = gen_code (new_l, N, exit_l);
         val stm3 = if stm2 = nop then stm1
                    else list_mk_comb(union, [stm1, stm2])
     in
         stm3
     end

    else if is_pair t then                        (*  exp = (M,N) *)
      raise Fail "unimplemented SAL code generation for tuples"

    (*
    else if is_cond t then                        (*  exp = if P then M else N *)
      let
         val (J,M,N) = dest_cond t
      in 
         if is_atom_cond J then
           let 
              val (op0, xL) = strip_comb J 
              val (P,Q) = (hd xL, hd (tl xL))
              val (lem0, lem1, lem2, lem3) = 
           in
              th4
           end
      end
     *)

   else if is_comb t then
      let val (operator, operands) = strip_comb t
      in

        if is_binop operator then (* Arithmetic and Logical Operations *)
	   raise Fail "No need of generating code for data operations"

        else (* Application *)
	   raise Fail "unimplemented SAL code generation for function applications"

      end

    else
      nop
  ;

fun gen_spec s = 
  let
    val (l1,l2) = (get_entry_label s, get_exit_label s);
  in 
    list_mk_pair [l1, s, l2]
  end


(* --------------------------------------------------------------------*)
(* Mechanism for mechanical reasoning                                  *)
(* --------------------------------------------------------------------*)

(* Single assignment instruction *)

fun mk_instr_spec instr =
  let
    val (_, args) = strip_comb instr;
    val (entry_l, dst, src, exit_l) = (hd args, hd (tl args), hd (tl (tl args)),  hd (tl (tl (tl args))));
    val v = mk_pair (src, dst);
    val s' = list_mk_pair [get_entry_label instr, instr, get_exit_label instr];
    val spec = list_mk_comb(inst [alpha |-> N] reduce, [s', v]);
  in
    prove(spec, SIMP_TAC std_ss [inst_rule])
  end

(* Union of two structures (i.e. sequential composition *)

fun mk_union_spec spec1 spec2 =
  let val (_, [s1, v1]) = strip_comb (concl spec1);
      val (_, [s2, v2]) = strip_comb (concl spec2);
      val [entry_l1, s1', exit_l1] = strip_pair s1;
      val [entry_l2, s2', exit_l2] = strip_pair s2;
      val (e1, x1) = dest_pair v1;
      val (e2, x2) = dest_pair v2;

      (*  s1 |+ s2 *)
      val t0 = list_mk_comb(inst [alpha |-> N] union, [s1', s2']);
      val t1 = list_mk_pair [entry_l1, t0, exit_l2];
      val v = mk_plet (x1, e1,
                      mk_plet (x2, e2, x2));
      val v' = mk_pair(v,x2);
      val t2 = list_mk_comb(inst [alpha |-> N] reduce, [t1, v']);

      val th =  prove (t2,   (* set_goal ([], t2) *)
		       ASSUME_TAC spec1 THEN
                       ASSUME_TAC spec2 THEN
                       IMP_RES_TAC seq_rule THEN
                       FULL_SIMP_TAC std_ss [LET_THM]
                )
              (*
                       MATCH_MP_TAC seq_rule THEN
                       EXISTS_TAC post_p1 THEN EXISTS_TAC out_f1 THEN
                       SIMP_TAC std_ss [spec1, spec2]
              *)
  in
      th
  end

(* --------------------------------------------------------------------*)
(* Certifing Code Generation                                           *)
(* --------------------------------------------------------------------*)

fun forward_reason s = 
  let
    val (combinator, sL) = strip_comb s;
    val comb_str = #1 (dest_const combinator);
  in
    if comb_str = "UNION" then
       mk_union_spec (forward_reason (hd sL)) 
                     (forward_reason (hd (tl sL)))
    else if comb_str = "ASG" then 
       mk_instr_spec s
    else
       raise Fail "unimplemented for this structure!"
  end;


fun certified_gen def =
  let
    val (fname, fbody) = dest_eq (concl (SPEC_ALL def))
    (* val (args,body) = dest_pabs fbody *)
    val s = gen_code (next_label(), fbody, next_label());
    (*
    val spec = gen_spec s;
    val v = mk_pair (fbody, get_output fbody);
    val t0 = list_mk_comb(inst [alpha |-> N] reduce, [spec, v]);
    *)
  in
    forward_reason s
  end

(* --------------------------------------------------------------------*)
(* Test Cases                                                          *)
(* --------------------------------------------------------------------*)

(*
val f1_def = Define `
    f1 x = let y = x + 1 in let z = x - y in z`;

   certified_gen f1_def;
val f2_def = Define `
    f2 x = 
      if x = 0 then x 
      else let y = x * x in y`;

   certified_gen f1_def;

*)
(* --------------------------------------------------------------------*)

end (* struct *)

