structure monomorphisation (* :> monomorphisation *) =
struct


(*
app load ["basic"]; 
*)

open HolKernel Parse boolLib pairLib PairRules bossLib pairSyntax ParseDatatype TypeBase;

(*-----------------------------------------------------------------------------------------*)
(* This transformation eliminates polymorphism and produces a simply-typed intermediate    *)
(* form that enables good data representations.                                            *)
(* The basic idea is to duplicate a datatype declaration at each type used and a function  *)
(* declaration at each type used, resulting in multiple monomorphic clones of this datatype*)
(* and function.                                                                           *)
(*-----------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------------*)
(* Map and set operation functions.                                                        *)
(*-----------------------------------------------------------------------------------------*)

structure M = Binarymap
structure S = Binaryset

(*-----------------------------------------------------------------------------------------*)
(* Auxiliary functions.                                                                    *)
(*-----------------------------------------------------------------------------------------*)

fun strOrder (s1:string,s2:string) =   (* order of strings *)
  if s1 > s2 then GREATER
    else if s1 = s2 then EQUAL
    else LESS
  ;

fun tvarOrder (t1:term,t2:term) =      (* order of terms *)
  strOrder (term_to_string t1, term_to_string t2)

fun tvarWithTypeOrder (t1:term,t2:term) =      (* order of typed terms *)
  strOrder (term_to_string t1 ^ (type_to_string o type_of) t1, term_to_string t2 ^ (type_to_string o type_of) t2)

fun typeOrder (t1:hol_type,t2:hol_type) =  (* order of types *)
  strOrder(type_to_string t1, type_to_string t2)
  ;

fun is_fun t =   (* the term is a function? *)
  #1 (Type.dest_type (type_of t)) = "fun"
  handle e => false

fun get_fname f = 
  #1 (strip_comb (#1 (dest_eq f)))

(*-----------------------------------------------------------------------------------------*)
(* Data structures.                                                                        *)
(*-----------------------------------------------------------------------------------------*)

(*
val Imap = ref (M.mkDict tvarOrder)         (* the instantiation map *)
                                            (* Format: [function's name |-> [type |-> instantiation set] ] *)

val MonoFunc = ref (M.mkDict tvarOrder)     (* monomorphistic functions *)
                                            (* Format: [function's name |-> a set of new defitions] *)
*)

fun smap m = List.map (fn (tp, s) => (tp, S.listItems s)) (M.listItems m)

fun Smap imap = List.map (fn (f,m) => (f, smap m)) (M.listItems imap)

(*
val map1 = M.insert(M.mkDict typeOrder, ``:'c``, S.addList(S.empty typeOrder, [``:'num``, ``:'bool``]));
val map2 = M.insert(M.mkDict typeOrder, ``:'b``, S.addList(S.empty typeOrder, [``:'c``, ``:'d``]));
*)

(*-----------------------------------------------------------------------------------------*)
(* Union and composition of instantiation maps.                                            *)
(*-----------------------------------------------------------------------------------------*)

fun mk_map inst_rules = 
  List.foldl (fn (rule : {redex : hol_type, residue : hol_type}, m) => 
                M.insert(m, #redex rule, 
                  case M.peek(m, #redex rule) of 
                      NONE => S.add(S.empty typeOrder, #residue rule)
                    | SOME s => S.add(s, #residue rule)
                )
             )
             (M.mkDict typeOrder)
             inst_rules

fun union_map map1 map2 =
   List.foldl (fn ((tp, insts), m) => 
                 case M.peek(m, tp) of 
                      NONE => M.insert(m, tp, insts)
                    | SOME old_insts => M.insert(m, tp, S.union(old_insts, insts))
              )
              map1
              (M.listItems map2)

fun compose_map map1 map2 =
  let 
    fun compose type_set = 
       List.foldl (fn (tp, s) =>
                     case M.peek(map2, tp) of 
                        NONE => S.add(S.empty typeOrder, tp)
                      | SOME s' => S.union(s, s')
                  )
                  (S.empty typeOrder)
                  (S.listItems type_set)
  in                     
   List.foldl (fn ((tp, type_set), m) => 
                M.insert(m, tp, compose type_set)
              )
              (M.mkDict typeOrder)
              (M.listItems map1)
  end

fun union_imap imap1 imap2 = 
   List.foldl (fn ((f, m), imap) => 
                 case M.peek(imap, f) of 
                      NONE => M.insert(imap, f, m)
                    | SOME old_m => M.insert(imap, f, union_map old_m  m)
              )
              imap1
              (M.listItems imap2)

fun compose_imap imap map = 
   List.foldl (fn ((f, m), imap') => 
                M.insert(imap', f, compose_map m map)
              )
              (M.mkDict strOrder)
              (M.listItems imap)

(*-----------------------------------------------------------------------------------------*)
(* Examine the type and build an instantiation map.                                        *)
(*-----------------------------------------------------------------------------------------*)

fun strip_type tp =
  let val (t1, t2) = dest_prod tp
  in (strip_type t1) @ (strip_type t2)
  end
  handle _ => 
    let val (t1, t2) = dom_rng tp
    in (strip_type t1) @ (strip_type t2)
    end
    handle _ => [tp]

fun examine_type tp = 
  List.foldl (fn (t,imap) => 
      let val original_t = (TypeBasePure.ty_of o valOf o TypeBase.fetch) t
          val pstr = #1 (dest_type t)
          val inst_rules = match_type original_t t
      in
        if null inst_rules then imap
        else
          case M.peek(imap, pstr) of
               NONE => M.insert(imap, pstr, mk_map inst_rules)
            |  SOME m => M.insert(imap, pstr, union_map (mk_map inst_rules) m)
      end
      handle _ => imap)
   (M.mkDict strOrder)
   (strip_type tp)

(*-----------------------------------------------------------------------------------------*)
(* Build the instantiation map.                                                            *)
(*-----------------------------------------------------------------------------------------*)

(* find the constant by its name (a string) *)

fun peek_fname f_str env = 
  case M.peek(env, f_str) of
      SOME x => SOME x
   |  NONE => SOME (hd (Term.decls f_str))
(* SOME (#1 ((strip_comb o lhs o concl o SPEC_ALL o DB.definition) (f_str ^ "_def")))  (* be a predefined function *) *)
      handle _ => NONE

(* traverse an expression and build the instantiation map *)

fun trav_exp t env =
  if basic.is_atomic t then
     examine_type (type_of t)
  else if is_let t then
    let val (v,M,N) = dest_plet t in
      if is_pabs M then       (* an embedded function *)
        let 
          val (arg, body) = dest_pabs M
          val f_str = #1 (dest_var v)
          val body_imap = trav_exp body env
          val env' = M.insert(M.mkDict strOrder, f_str, v)
          val N_imap = trav_exp N env'
          val body_imap' = compose_imap body_imap (M.find(N_imap, f_str))
                           handle _ => body_imap
        in
          union_imap body_imap' N_imap
        end
      else
         union_imap (trav_exp M env) (trav_exp N env)
    end
  else if is_cond t then
    let val (J,M,N) = dest_cond t in
        union_imap (trav_exp J env)
          (union_imap (trav_exp M env) (trav_exp N env))
    end
  else if is_pair t then
    let val (M,N) = dest_pair t in
        union_imap (trav_exp M env) (trav_exp N env)
    end
  else if is_pabs t then
    let val (M,N) = dest_pabs t in
        trav_exp N env
    end
  else if is_comb t then
    let val (M,N) = dest_comb t
    in 
       if is_constructor M then
         union_imap (examine_type (type_of M)) (trav_exp N env)
       else if is_fun M then    (* function application *)
         let val fstr = #1 (dest_const M) handle _ => #1 (dest_var M)
             val fname = valOf (peek_fname fstr env)
             val inst_rules = match_type (type_of fname) (type_of M)
             val imap = trav_exp N env
             val imap' = if null inst_rules then imap
                         else union_imap imap (M.insert(M.mkDict strOrder, fstr, mk_map inst_rules))
         in  union_imap imap' (examine_type (type_of M))
         end
       else
         union_imap (trav_exp M env) (trav_exp N env)
    end
    (* handle _ => M.mkDict strOrder      (* not function application *) *)
  else if is_fun t then
    M.mkDict strOrder
  else M.mkDict strOrder

(* val imap = M.mkDict strOrder; *)

fun build_imap defs =
  let
    fun compose (f_def,imap) = 
      let val env = M.mkDict strOrder
          val (f_lhs, f_body) = (dest_eq o concl o SPEC_ALL) f_def
          val f_str = #1 (dest_const (#1 (strip_comb f_lhs)))
          val body_imap = trav_exp f_body env
          val imap' = compose_imap body_imap (M.find(imap, f_str))
              handle _ => body_imap
      in  union_imap imap imap'
      end
  in
    List.foldr compose (M.mkDict strOrder) defs
  end

(*-----------------------------------------------------------------------------------------*)
(* Eliminate polymorphism by duplicating functions definitions.                            *)
(*-----------------------------------------------------------------------------------------*)

(* 
val Duplicated  = ref (M.mkDict tvarOrder)      (* definitions of the monomorphic functions  *)
                                                (* format: function name |-> new definition  *)
*)

(*-----------------------------------------------------------------------------------------*)
(* Redefine functions in HOL and prove the correctness of the translation.                 *)
(*-----------------------------------------------------------------------------------------*)

fun change_f_name f name =
  let val (f_lhs, f_rhs) = dest_eq f
      val (fname, argL) = (strip_comb f_lhs)
      val (_, f_type) = dest_const fname
      val new_fname = mk_var (name, f_type)
      val new_f_lhs = list_mk_comb(new_fname, argL)
  in
      mk_eq (new_f_lhs, f_rhs)
  end

val MonoFunc = ref (M.mkDict tvarWithTypeOrder)    (* a map from polymorphic function name to the names of its clones *)
val judgements = ref []             (* a list of judgements specifying the monomorphic functions are equivalent to their polymorphic functions *)

(* Create the clones of a function according to the instantiation information in the instantiation map *)

fun duplicate_func imap def = 
  let
    fun one_type tp [] rules = []
     |  one_type tp (x::xs) rules =
          (List.map (fn y => (tp |-> x) :: y) rules) @ one_type tp xs rules

    (* compute all the combinations of type instantiation rules *)
    fun mk_type_combination [(tp,type_set)] = List.map (fn x => [tp |-> x]) (S.listItems type_set)
     |  mk_type_combination ((tp,type_set)::xs) =
          one_type tp (S.listItems type_set) (mk_type_combination(xs))

    val f = (concl o SPEC_ALL) def
    val (f_lhs, f_rhs) = dest_eq f
    val fname = #1 (strip_comb (f_lhs))
    val (f_str, f_type) = dest_const fname
    val mono_rules = List.map (fn (old_name, new_name) => old_name |-> new_name) (M.listItems (!MonoFunc))

    val index = ref 0
    val insts = M.listItems(M.find(imap, f_str)) handle _ => []
    val new_fs = 
          if null insts then (* the function is already monomorphistic, no instantiations are needed *)
            (* However, we still need to rewrite its body if other monomorphic functions are called in this body *)
            let val f' = subst mono_rules f
                val new_f_str = f_str ^ Int.toString (!index)
                val new_fname = mk_var(new_f_str, f_type)
                val new_f = subst [fname |-> new_fname] f'
                val new_f_def = Define `^new_f`
                val _ = MonoFunc := M.insert(!MonoFunc, fname, mk_const(new_f_str, f_type))
                val _ = judgements := (mk_eq(mk_const(f_str, f_type), mk_const(new_f_str, f_type))) 
                                      :: (!judgements)
            in
                [new_f_def]
            end
          else  (* instantiate types and replace all polymorphic function calls with corresponding monomorphic calls *)
            let val rules = mk_type_combination insts
            in
              List.map (fn rule =>
                let val f' = inst rule f
                    val new_f = subst mono_rules f'
                    val _ = index := !index + 1
                    val new_f_str = f_str ^ Int.toString (!index)
                    val old_fname = get_fname new_f
                    val new_f_type = #2 (dest_const old_fname)
                    val new_fname = mk_var(new_f_str, new_f_type)
                    val f'' = subst [old_fname |-> new_fname] new_f
                    val new_f_def = Define `^f''`
                    val _ = MonoFunc := M.insert(!MonoFunc, old_fname, mk_const(new_f_str, new_f_type)) 
                    val _ = judgements := (mk_eq(mk_const(f_str, new_f_type), mk_const(new_f_str, new_f_type))) 
                                          :: (!judgements)
                in new_f_def
                end)
                rules
            end
  in
    new_fs
  end

fun build_clone defs =
  let
    val imap = build_imap defs
    val _ = MonoFunc := M.mkDict tvarWithTypeOrder
    val _ = judgements := []
    val new_defs = List.foldl (fn (def,fs) => 
                     fs @ (duplicate_func imap def))
                    [] defs
  in
    (new_defs, list_mk_conj (!judgements))
  end

(*-----------------------------------------------------------------------------------------*)
(* Mechanical proof.                                                                       *)
(*-----------------------------------------------------------------------------------------*)

fun elim_poly defs = 
  let
    val (newdefs, judgement) = build_clone defs
    val thm = prove (judgement, 
                SIMP_TAC std_ss [FUN_EQ_THM, pairTheory.FORALL_PROD] THEN
                SIMP_TAC std_ss (defs @ newdefs)
              )
  in
    (newdefs, thm)
  end

(*-----------------------------------------------------------------------------------------*)
(* Example 1.                                                                              *)
(*-----------------------------------------------------------------------------------------*)

(*
val _ = Hol_datatype `
  p = P of 'a # 'a`;

val f_def = Define `
  f = \x:'b. (P : 'b # 'b -> 'b p) (x, x)`;

val g_def = Define `
  g = \(y:'c,z:'d).
      let h = \w : 'c p. f z in
      let v = f y in
      h v
  `;

val a_def = Define `
  a = g (3, T)`;

val b_def = Define `
  b = g (F, 1)`;

val defs = [f_def, g_def, a_def, b_def];

val newdefs = elim_poly defs;

val (newdefs, thm) = elim_poly defs;

*)

(*-----------------------------------------------------------------------------------------*)
(* Example 2.                                                                              *)
(*-----------------------------------------------------------------------------------------*)

(*

Hol_datatype `dt1 = C of 'a # 'b`;

val f_def = Define `f (x:'a) = x`;
val g_def = Define `g (x : 'c, y : 'd) =
      let h = \z. C (f x, f z) in 
      h y`;
val j_def = Define `j = (g(1, F), g(F, T))`;

val defs = [f_def, g_def, j_def];

val (newdefs, thm) = elim_poly defs;

*)

(*-----------------------------------------------------------------------------------------*)

end (* struct *)