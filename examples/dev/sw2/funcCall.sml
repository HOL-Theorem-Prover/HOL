structure funcCall (* :> funcCall *) =
struct

(* app load ["NormalTheory", "basic", "regAlloc"] *)

open HolKernel Parse boolLib bossLib;
open pairLib pairSyntax PairRules NormalTheory basic;

val atom_tm = prim_mk_const{Name="atom",Thy="Normal"}
fun mk_atom tm = mk_comb (inst [alpha |-> type_of tm] atom_tm,tm)

(*----------------------------------------------------------------------------------------------*)
(*                                                                                              *)
(*----------------------------------------------------------------------------------------------*)

structure M = Binarymap
structure S = Binaryset
val VarType = ref (Type `:word32`) (* numSyntax.num *)

(*----------------------------------------------------------------------------------------------*)
(* Pre-defined variables and functions                                                          *)
(*----------------------------------------------------------------------------------------------*)

fun is_reg x = (String.sub (term_to_string x,0) = #"r")
fun is_mem x = (String.sub (term_to_string x,0) = #"m")

fun tvarOrder (t1:term,t2:term) =
  let val (s1,s2) = (term_to_string t1, term_to_string t2) in
    if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS
  end;

(* Is an expression a function application? *)
 
fun is_fun exp = 
  not (is_comb exp) andalso
  (#1 (dest_type (type_of exp)) = "fun")
  handle HOL_ERR _ => false;

(*----------------------------------------------------------------------------------------------*)
(* Function calls in a caller-save style.                                                       *)
(*----------------------------------------------------------------------------------------------*)

(* Traverse the function body to find all modified registers and the next available memory slot *)

fun process_body body =
 let

   fun traverse t (rS, wS) =
     if is_let t then
       let val (v,M,N) = dest_plet t
           val (rS1, wS1) = traverse M (rS, S.addList(wS, List.filter is_reg (strip_pair v)))
       in
           traverse N (rS1, wS1)
       end
     else if is_cond t then
       let val (J,M,N) = dest_cond t in
           ((traverse N) o (traverse M) o (traverse J)) (rS, wS)
       end
     else if is_pair t then
       let val (M,N) = dest_pair t in
           ((traverse N) o (traverse M)) (rS, wS)
       end
     else if is_pabs t then
       let val (M,N) = dest_pabs t in
           ((traverse N) o (traverse M)) (rS, wS)
       end
     else if is_comb t then
       let val (M,N) = dest_comb t in 
           ((traverse N) o (traverse M)) (rS, wS)
       end
     else if is_reg t orelse is_mem t then
       (S.add(rS, t), wS)
     else (rS, wS)

   val (rS', wS') = traverse body (S.empty tvarOrder, S.empty tvarOrder)
   val next_avail_slot = List.foldl  (* the first unused memory slot *)
                           (fn (v, i) => 
                              if is_mem v then
                                let val s = #1 (dest_var v)
                                    val j = valOf (Int.fromString (substring(s, 1, String.size s - 1)))
                                in if j > i then j else i
                                end
                              else i
                           )
                           0 (S.listItems rS')

 in
   (wS', next_avail_slot)
 end;

(* Find all modified registers and the next available memory slot for all functions *)

val fmap = ref (M.mkDict tvarOrder);

fun investigate_def def = 
   let
     val (fname, fbody) = dest_eq (concl (SPEC_ALL def))
     val (args,body) = dest_pabs fbody handle _ => (#2 (dest_comb fname), fbody)
     val fname = if is_pabs fbody then fname else #1 (dest_comb fname)
   in 
     fmap := M.insert(!fmap, fname, ((args, identify_output body), process_body body))
   end

(* Convert a function body into its call-save format *)

fun save (wS, next_slot) exp =
   #1 (List.foldl (fn (r, (e, slot)) => 
                     (mk_plet (mk_var("m" ^ Int.toString(slot) , !VarType), mk_atom r, e), slot + 1))
                  (exp, next_slot)
                  (S.listItems wS)
      )

fun restore (wS, next_slot) exp =
   #1 (List.foldr (fn (r, (e, slot)) => 
                     (mk_plet (r, mk_atom (mk_var("m" ^ Int.toString(slot), !VarType)), e), slot + 1))
                  (exp, next_slot)
                  (rev (S.listItems wS))
      )

(* 
  fmap := preprocess defs;
*)

val tr_f = ref (``T``);    (* the name of a recursive function *)

fun format_call (fname, dst, src, cont) =
  let val ((src0, dst0), (s, next_slot)) = M.find(!fmap, fname)
       (* handle NotFound => (investigate_def (DB.definition (#1 (dest_const fname) ^ "_def")); 
                             M.find(!fmap, fname))
       *)
      val s1 = S.addList (S.addList(s, strip_pair src0), strip_pair dst0)
      val s2 = S.difference(s1, S.addList(S.empty tvarOrder, strip_pair dst))

      val t1 = restore (s2, next_slot) cont
      val t2 = regAlloc.parallel_move dst dst0 t1
      val t3 = mk_plet(dst0, mk_comb(fname, src0), t2)
      val t4 = regAlloc.parallel_move src0 src t3
      val t5 = save (s2, next_slot) t4
  in
      t5
  end

fun caller_save t =
  if is_let t then
    let val (v,M,N) = dest_plet t in
      if is_comb M andalso not (is_atomic M) then
        let val (x,y) = dest_comb M in
           if is_fun x andalso not (x = !tr_f) then (* non-recursive function application *)
             let 
                 val (fname, dst, src, cont) = (x, v, y, caller_save N)
             in
                 format_call (fname, dst, src, cont)
             end
           else
             mk_plet(v, caller_save M, caller_save N)
        end
      else 
        mk_plet(v, caller_save M, caller_save N) (* not function application *)
    end
  else if is_cond t then
    let val (J,M,N) = dest_cond t in
        mk_cond (J, caller_save M, caller_save N)
    end
  else if is_pair t then
    let val (M,N) = dest_pair t in
        mk_pair (caller_save M, caller_save N)
    end
  else if is_pabs t then
    let val (M,N) = dest_pabs t in
        mk_pabs (caller_save M, caller_save N)
    end
  else if is_comb t then
    let val (M,N) = dest_comb t in
       mk_comb(caller_save M, caller_save N)
    end
  else t

(* Function "trav" traverses a term and adds pre-call saving and post-call saving instructions 
   for each function call; it also make the outputs of the two branches of a conditional 
   statement match, i.e. both branches have the same outputs.
*)

fun trav t output =
  if is_let t then
    let val (v,M,N) = dest_plet t
        val (M', _) =  trav M NONE
    in
      if is_comb M andalso not (is_atomic M) then
        let val (x,y) = dest_comb M in
           if is_fun x andalso not (x = !tr_f) then (* non-recursive function application *)
             let 
                 val (N', output') = trav N output
                 val (fname, dst, src, cont) = (x, v, y, N')
                 val t' = format_call (fname, dst, src, cont)
             in
                 (t', output')
             end
           else
             let val (N', output') = trav N output
             in (mk_plet(v, M', N'), output') end
        end
      else 
        let val (N', output') = trav N output
        in (mk_plet(v, M', N'), output') end (* not function application *)
    end
  else if is_cond t then
    let val (J,M1,M2) = dest_cond t
        val (M1', output1) = trav M1 output
        val (M2', output2) = trav M2 output1
    in  
        (mk_cond(J, M1', M2'), output1)
    end
  else if is_pair t orelse is_atomic t then
    case output of 
         NONE => (t, SOME t)
      |  SOME x => (regAlloc.parallel_move x t x, output)
  else if is_pabs t then
    let val (M,N) = dest_pabs t
        val (N', _) = trav N NONE
    in
        (mk_pabs (M, N'), output)
    end
  else (t, output)

(* Process function calls in a caller-save style *)

fun caller_save_call def =
    let val (fname, fbody) = dest_eq (concl (SPEC_ALL def))
        val (args,body) = dest_pabs fbody handle _ => (#2 (dest_comb fname), fbody)
        val (sane,var_type) = pre_check(args,body)
        val fname = if is_pabs fbody then fname else #1 (dest_comb fname)
        val _ = (VarType := var_type; tr_f := fname)
        val _ = investigate_def def   (* store the information of the current function into !fmap *)
    in if sane then
        let
          val (body', _) = trav body NONE
          val th0 = SYM (QCONV(SIMP_CONV pure_ss [LET_ATOM]) body')
          val (r,t) = dest_eq(concl th0)
          val lem1 = ALPHA body r
          val th1 = TRANS lem1 th0
          val th2 = REWRITE_RULE [Once th1] def
          val th3 = REWRITE_RULE [ATOM_ID] th2
        in SIMP_RULE bool_ss [ELIM_USELESS_LET] th3
        end
       else def
    end

(*
fun callerSave defs =
 let
   fun one_fun def = 
    let val (fname, fbody) = dest_eq (concl (SPEC_ALL def))
        val (args,body) = dest_pabs fbody handle _ => (#2 (dest_comb fname), fbody)
        val (sane,var_type) = pre_check(args,body)
        val fname = if is_pabs fbody then fname else #1 (dest_comb fname)
        val _ = (VarType := var_type; tr_f := fname)
    in if sane then
        let
          val body' = caller_save body
          val th0 = SYM (QCONV(SIMP_CONV pure_ss [LET_ATOM]) body')
          val th1 = REWRITE_RULE [ELIM_USELESS_LET] th0
          val th2 = REWRITE_RULE [Once th1] def
          val th3 = REWRITE_RULE [ATOM_ID] th2
        in th3
        end
       else def
    end
 in
   List.map one_fun defs
 end
*)

(*----------------------------------------------------------------------------------------------*)
(* For debugging                                                                                *)
(*----------------------------------------------------------------------------------------------*)

fun mm () =
  List.map (fn (fname, ((src, dst), (wS, slot))) => (fname, (src, dst, S.listItems wS, slot))) (M.listItems (!fmap))


end
