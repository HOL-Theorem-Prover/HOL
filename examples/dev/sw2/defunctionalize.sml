structure defunctionalize (* :> defunctionalize *) =
struct

open HolKernel Parse boolLib pairLib PairRules bossLib pairSyntax ParseDatatype TypeBase;

(*-----------------------------------------------------------------------------------------*)
(* We convert higher-order functions into equivalent first-order functions and hoist nested*)
(* functions to the top level through a type based closure conversion. After this conver-  *)
(* sion, no nested functions exist; and function call is made by dispatching on the closure*)
(* tag followed by a top-level call.                                                       *)
(* Function closures are represented as algebraic data types in a way that,for each func-  *)
(* tion definition, a constructor taking the free variables of this function is created.   *)
(* For each arrow type we create a dispatch function, which converts the definition of a   *)
(* function of this arrow type into a closure constructor application.                     *)
(* A nested function is hoisted to the top level with its free variables to be passed as   *)
(* extra arguments. After that, the calling to the original function is replaced by a      *)
(* calling to the relevant dispatch function passing a closure containing the values of    *)
(* this function's free variables. The dispatch function examines the closure tag and      *)
(* passes control to the appropriate hoisted function. Thus, higher order operations on    *)
(* functions are replaced by equivalent operations on first order closure values.          *)
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

fun typeOrder (t1:hol_type,t2:hol_type) =  (* order of types *)
  strOrder(type_to_string t1, type_to_string t2)
  ;

fun is_fun t =   (* the term is a function? *)
  #1 (Type.dest_type (type_of t)) = "fun"
  handle e => false

fun FunName f = 
  #1 (strip_comb (#1 (dest_eq f)))

(*-----------------------------------------------------------------------------------------*)
(* Data structures.                                                                        *)
(*-----------------------------------------------------------------------------------------*)

val Lifted = ref (M.mkDict tvarOrder)       (* the definitions of those embedded functions that should be lifted *)
                                            (* Format: [function's name |-> function's body] *)
val ClosFunc = ref (M.mkDict typeOrder)     (* the types and the higher order functions associating with them *)
                                            (* Format: [function's type |-> a set of function names] *)

val ClosInfo = ref (M.mkDict typeOrder)     (* A mapping from a type to the information of its datatype representing a closure *)
                                            (* Format: [type |-> datatype's info]  *)
val ClosName = ref (M.mkDict typeOrder)     (* A mapping from a type to the name of its datatype representing a closure *)
                                            (* Format: [type |-> datatype's name (a string)]  *)

val HOFunc = ref (M.mkDict tvarOrder)       (* higher order functions *)
                                            (* Format: [function's name |-> (new function's lhs, constructor)] *)

fun cF() = 
  (M.listItems (!Lifted),
   List.map (fn (tp, s) => (tp, S.listItems s)) (M.listItems (!ClosFunc)));

(*-----------------------------------------------------------------------------------------*)
(* Identify higher order functions (those functions used in arguments and returns;         *)
(* then build datatype for them.                                                           *)
(*-----------------------------------------------------------------------------------------*)

fun record_f fname =          (* store the name of a higher order function *)
  let val tp = type_of fname
  in 
    case M.peek(!ClosFunc, tp) of 
         NONE => 
             (* val _ = closure_index := !closure_index + 1; *)
             ClosFunc := M.insert(!ClosFunc, tp, S.add(S.empty tvarOrder, fname))
     |   SOME s =>
             ClosFunc := M.insert(!ClosFunc, tp, S.add(s, fname))
  end;

fun identify_f e =        (* Identify higher order functions in an expression and store them into the ClosFunc *)
 let 
   fun trav t =
       if is_let t then
           let val (v,M,N) = dest_plet t
               val _ = (trav M; trav N)
           in  if is_pabs M then        (* an embedded function, should be lifted *)
                 Lifted := M.insert(!Lifted, N, M)
               else
                 ()
           end
       else if is_pair t then
           let val (M,N) = dest_pair t
           in  (trav M; trav N)
           end
       else if is_cond t then
           let val (J,M,N) = dest_cond t
           in  (trav M; trav N)
           end
       else if is_comb t then
            let val (M,N) = dest_comb t
            in  if is_fun N then
                  (record_f t;
                   if is_comb M then trav M else ()
                  )
                else
                  if is_comb M then trav M else ()
            end
       else if is_pabs t then
            let val (M,N) = dest_pabs t
            in  trav N
            end
       else if is_fun t then
            record_f t
       else
            ()
  in
     trav e
  end

fun identify_closure defs =     (* Identify higher order functions in a list of function definitions *)
  let 
    fun mk_clos_data f =
      let val (fdecl, fbody) = dest_eq f
          val (fname, args) = dest_comb fdecl
          val _ = Lifted := M.insert(!Lifted, fname, mk_pabs(args,fbody))
      in
         identify_f fbody
      end
  in
    (ClosFunc := M.mkDict typeOrder;
     Lifted := M.mkDict tvarOrder;
     List.map (mk_clos_data o concl o SPEC_ALL) defs
    )
  end

(*-----------------------------------------------------------------------------------------*)
(* Build datatypes for closures.                                                           *)
(*-----------------------------------------------------------------------------------------*)

val closure_index = ref 0;
val constructor_index = ref 0;

fun register_type tyinfos_etc =            (* register the new datatype in HOL *)
  let
    val (tyinfos, etc) = unzip tyinfos_etc
    val tyinfos = TypeBase.write tyinfos
    val () = app computeLib.write_datatype_info tyinfos
  in
    Datatype.write_tyinfos tyinfos_etc
  end

fun build_type tp funcs =                 (* build a new datatype for a type *)
  let

    (* the arguments of a constructor, these arguments are the free variables of a function body *)
    fun build_type_args fv =
      if null fv then []
      else if length fv = 1 then
        [dTyop{Args = [], Thy = NONE, 
         Tyop = let val t = type_of (hd fv) in
                  M.find(!ClosName, t) 
                  handle e => #1 (Type.dest_type t)
                end}
        ]
      else 
        [dTyop{Args =
                 List.map (fn arg => 
                   dTyop{Args = [], Thy = NONE, 
                        Tyop = M.find(!ClosName, type_of arg)
                               handle e => #1 (Type.dest_type (type_of arg))})
                 fv,
               Thy = NONE, Tyop = "prod"}
        ]
     
    val clos_name = (* the name of the datatype representing a closure for the inputting type *)
        let val _ = closure_index := !closure_index + 1
            val x = "clos" ^ Int.toString (!closure_index)
            val _ = ClosName := M.insert(!ClosName, tp, x)
        in  x
        end

    val clos_tp_info = (* the type information of the datatype *)
         [(clos_name, 
           Constructors (
             List.map 
              (fn lifted_f =>
                let
                  val _ = constructor_index := !constructor_index + 1
                  val fv = free_vars (M.find (!Lifted, lifted_f))
                  val args = build_type_args fv 
                in
                  ("cons" ^ Int.toString(!constructor_index),
                   build_type_args fv
                  )
                end
               ) (S.listItems funcs)
            )
          )]

    val new_clos_type = Datatype.primHol_datatype_from_astl (TypeBase.theTypeBase()) clos_tp_info;
    val _ = register_type (#2 new_clos_type)
    val _ = ClosInfo := M.insert(!ClosInfo, tp, #1 (hd (#2 new_clos_type)))
  in
    new_clos_type
  end
  ;

fun build_types defs =           (* build datatypes for all higher order functions *)
  (closure_index := 0;
   constructor_index := 0;
   identify_closure defs;
   ClosName := M.mkDict typeOrder;
   List.map (fn (tp, fs) => build_type tp fs) (M.listItems (!ClosFunc))
  )

(*-----------------------------------------------------------------------------------------*)
(*  Conversions from original HOL types to closure types.                                  *)
(*-----------------------------------------------------------------------------------------*)

fun type2closure tp =    (* from an original type to its closure type *)
  TypeBasePure.ty_of(M.find(!ClosInfo, tp))
  handle _ => tp

fun term2closure t =     (* get the closure type for a term *)
  let val (name, tp) = dest_var t
  in  mk_var(name, type2closure tp)
  end
  handle _ => t

fun type2dispatch tp =   (* from an original type to its dispatch function *)
  let val tinfo = M.find(!ClosInfo, tp)
      val clos_type = TypeBasePure.ty_of tinfo
      val f_index = String.extract (#1 (Type.dest_type clos_type), 4, NONE) (* take the value of n from "closn" *)
      val (arg_type, return_type) = dom_rng tp
      val df_var = mk_const("dispatch" ^ f_index,     (* the dispatch function has been defined *)
                         mk_prod(clos_type, arg_type) --> return_type)
          handle e => mk_var("dispatch" ^ f_index,    (* the dispatch function has not been defined *)
                         mk_prod(clos_type, arg_type) --> return_type)
  in
     df_var
  end

(*-----------------------------------------------------------------------------------------*)
(* Build dispatch functions.                                                               *)
(* A dispatch function is in pattern-matching format.                                      *)
(*-----------------------------------------------------------------------------------------*)

fun mk_dispatch tp =
  let
    val tinfo = M.find(!ClosInfo, tp)
    val clos_type = TypeBasePure.ty_of tinfo
    (* val clos_case = TypeBasePure.case_const_of tinfo *)
    val clos_consL = TypeBasePure.constructors_of tinfo
    val f_index = String.extract (#1 (Type.dest_type clos_type), 4, NONE) (* take the value of n from "closn" *)

    val funL = S.listItems (M.find(!ClosFunc, tp))
    val (arg_type, return_type) = dom_rng tp

    val df_name = "dispatch" ^ f_index
    val df_type = mk_prod(clos_type, arg_type) --> return_type

    val df_var = mk_var(df_name, df_type)
(*   
    val _ = new_constant(df_name, df_type)
    val df_const = mk_const(df_name, df_type)
*)
    
    fun mk_clause (fname, constructor) =        (* construct a dispatching clause for the pattern matching pattern *)
        let val f_body = M.find(!Lifted, fname)
            val (f_arg, body) = dest_pabs f_body
            val fv = free_vars f_body
            val fv' = List.map term2closure fv
            val clos_arg = if null fv then constructor 
                           else mk_comb(constructor, list_mk_pair fv')
            val arg = mk_pair(clos_arg, f_arg)
            val lt = mk_comb(df_var, arg)
            val rt = let val (old_name, ftype) = dest_const fname handle _ => dest_var fname 
                         val new_arg = if null fv then f_arg else mk_pair(list_mk_pair fv', f_arg)
                         val new_name = old_name ^ "'"
                         val new_f_type = (type_of new_arg) --> return_type
                         (*
                         val _ = new_constant(new_name , new_f_type)
                         val new_fname = mk_const(new_name, new_f_type)
                         *)
                         val new_fname = mk_var(new_name, new_f_type)
                         val new_f = mk_comb (new_fname, new_arg)
                         val _ = HOFunc := M.insert(!HOFunc, fname, (new_f, clos_arg))
                     in
                         new_f
                     end
        in
            mk_eq(lt,rt)
        end

    val clauses = list_mk_conj (List.map mk_clause (zip funL clos_consL))
  in
    clauses
  end


val Dispatched = ref (M.mkDict typeOrder)      (* definitions of dispatch functions *)
                                               (* format: type |-> list of definitions *)

fun build_dispatch () =           (* build dispatch functions for all introduced datatypes *)
  (HOFunc := M.mkDict tvarOrder;
   List.map (fn tp => Dispatched := M.insert(!Dispatched, tp, mk_dispatch tp))
     (List.map fst (M.listItems (!ClosFunc)))
  )

(*-----------------------------------------------------------------------------------------*)
(* convert_exp translates expressions;                                                     *)
(* convert_fun translates functions;                                                       *)
(* TS translates top-level declarations;                                                   *)
(*-----------------------------------------------------------------------------------------*)

val Redefined  = ref (M.mkDict tvarOrder)       (* definitions of the functions after closure conversion *)
                                                (* format: function name |-> new definition              *) 
fun convert_exp t =
  if is_let t then
    let val (v,M,N) = dest_plet t in
      if is_pabs M then       (* an embedded function *)
        let 
          val (arg, body) = dest_pabs M
          val _ = convert_fun (mk_eq(mk_comb(v, arg), body))
(*          val M' =  #2 (M.find(!HOFunc, v))
          val v' = mk_var (#1 (dest_var v), type_of M')
        in
            mk_plet(v', M', convert_exp N)
        end
*)
        in
          convert_exp N
        end
      else
          mk_plet (v, convert_exp M, convert_exp N)
    end
  else if is_cond t then
    let val (J,M,N) = dest_cond t in
        mk_cond (J, convert_exp M, convert_exp N)
    end
  else if is_pair t then
    let val (M,N) = dest_pair t in
        mk_pair (convert_exp M, convert_exp N)
    end
  else if is_pabs t then
    let val (M,N) = dest_pabs t in
        mk_pabs (convert_exp M, convert_exp N)
    end
  else if is_comb t then
    let val (M,N) = dest_comb t
    in 
       if length (#2 (strip_comb t)) > 1 then t    (* binary expressions *)
       else if is_fun M then    (* function application *)
         if not (M.peek(!Redefined, M) = NONE) then     (* a pre-defined function *)
            let val fname_var = #1 (M.find(!Redefined, M))
                val (fname_str, f_tp) = dest_var fname_var
                val fname_const = mk_const (fname_str, f_tp)
                                  handle _ => fname_var    (* recursive function *)
            in  mk_comb(fname_const, convert_exp N)
            end
         else
            let
              val tp = type_of M
              val clos_var = 
                  mk_var(#1 (dest_const M) handle _ => #1 (dest_var M), 
                                    type2closure tp)
              val closure = mk_pair(clos_var, convert_exp N)
            in
              mk_comb (type2dispatch(tp), closure)
            end
       else
         mk_comb(convert_exp M, convert_exp N)
    end
    handle _ => t      (* not function application *)
  else if is_fun t then
    case M.peek(!HOFunc, t) of     (* Higher order function *)
         NONE => mk_var(#1 (dest_const t) handle _ => #1 (dest_var t), 
                        type2closure (type_of t)) |
         SOME (f_sig, constr) => constr
  else t

and

convert_fun f = 
  let
    val (fdecl, fbody) = dest_eq f
    val (fname, args) = dest_comb fdecl
    val (fname_str, f_tp) = dest_const fname handle _ => dest_var fname
    val new_fname_str = fname_str ^ "'"
  in
    if M.peek(!HOFunc, fname) = NONE then  (* not higher order function *)
      let val args1 = convert_exp args
          val new_f_tp = type_of args1 --> type2closure (type_of fdecl)

          val new_fname = mk_var(new_fname_str, new_f_tp)
          val _ = Redefined := M.insert(!Redefined, fname, (new_fname, ``T``))

          val fbody1 = convert_exp fbody
          val new_f = mk_eq(mk_comb (new_fname, args1), fbody1)
          val _ = Redefined := M.insert(!Redefined, fname, (new_fname, new_f))
      in
          new_f
      end
    else                                   (* a higher order function *)
      let val lt = #1 (M.find (!HOFunc, fname))
          val (new_fname, new_args) = dest_comb lt
          val _ = Redefined := M.insert(!Redefined, fname, (new_fname, ``T``))
          val fbody1 = convert_exp fbody
          val new_f = mk_eq(lt, fbody1)
          val _ = Redefined := M.insert(!Redefined, fname, (new_fname, new_f))
      in
          new_f
      end
  end
  handle _ => f

fun defunctionalize defs =
  let
    val _ = build_types defs
    val _ = build_dispatch ()
    
    fun process_type tp = 
      let val fs = S.listItems(M.find (!ClosFunc, tp))
          val fs' = List.map (fn fname => 
                       let val fbody = M.find(!Lifted, fname)
                           val (args,body) = dest_pabs fbody
                           val fdecl = mk_comb(fname, args)
                       in  convert_fun (mk_eq(fdecl, body))
                       end) fs
          val spec = list_mk_conj (strip_conj (M.find(!Dispatched, tp)) @ fs')
          val def = Defn.eqns_of (Defn.Hol_defn "x" `^spec`)
       in
          def
       end

    val _ = Redefined := M.mkDict tvarOrder
    val dispatch_spec = List.map process_type (List.map fst (M.listItems (!ClosFunc)))

    val remaining_funcs = 
          List.filter (fn f => M.peek(!Redefined, #1 (dest_comb (lhs f))) = NONE) 
          (List.map (concl o SPEC_ALL) defs)
    val new_spec = List.map (fn x => let val f = convert_fun x in Define `^f` end) remaining_funcs

  in
    (hd dispatch_spec) @ new_spec
  end

(*-----------------------------------------------------------------------------------------*)
(* Redefine functions in HOL and prove the correctness of the translation.                 *)
(*-----------------------------------------------------------------------------------------*)

(* Convert function arguments to closure arguments                                         *)

fun process_args args = 
  if is_pair args then
    let val (arg1, arg2) = dest_pair args
        val (assms1, arg1') = process_args arg1
        val (assms2, arg2') = process_args arg2
    in
        (assms1 @ assms2, mk_pair(arg1', arg2'))
    end
  else
    let
      val (arg_str, arg_tp) = dest_var args
      val new_arg_str = arg_str ^ "'"

      val new_args = if is_fun args then mk_var (new_arg_str, type2closure arg_tp)
                    else args
      val assms = if is_fun args then
                    let val input = mk_var("i", #1 (dom_rng arg_tp)) in
                        [mk_eq(mk_comb(args, input), mk_comb (type2dispatch arg_tp, mk_pair(new_args, input)))]
                    end
                else []
    in
      (assms, new_args)
    end

(* Build the equivalence statement for a function.                                       *)

fun var2const t = 
  if is_comb t then 
    let val (M,N) = dest_comb t
    in mk_comb(var2const M, N)
    end
  else 
    let val (v, tp) = dest_var t
    in mk_const(v, tp)
    end

fun build_judgement f = 
  let
    val (fdecl, fbody) = dest_eq f
    val (fname, args) = dest_comb fdecl
    val (assums, new_args) = process_args args
    val new_fname = var2const (#1 (M.find (!Redefined, fname))) handle _ => fname
    val new_fdecl = mk_comb (new_fname, new_args)
    val x = if not (is_fun fdecl) then mk_eq(fdecl, new_fdecl)
            else let val ftp = type_of fdecl
                     val input = mk_var("m", #1 (dom_rng ftp))
                     val new_fdecl' = mk_comb (type2dispatch ftp, mk_pair(new_fdecl, input))
                 in
                     mk_eq(mk_comb(fdecl, input), new_fdecl')
                 end
    val x' = gen_all x
    val judgement = if null assums then x' 
                    else mk_imp(list_mk_conj assums, x')
  in
    judgement
  end

(* 
  (build_judgement o concl o SPEC_ALL) (List.nth(defs,2))
  val def = List.nth(defs,2)
  val f = concl (SPEC_ALL def)
*)

fun elim_hof defs = 
  let
    val newdefs = defunctionalize defs
    val judgements = List.map (build_judgement o concl o SPEC_ALL) defs
  in
    (newdefs, judgements)
  end

(*-----------------------------------------------------------------------------------------*)
(* Example 1.                                                                              *)
(*-----------------------------------------------------------------------------------------*)

val empty_def = Define `
  empty (x : num) = F`;

val member_def = Define `
  member (s : num -> bool, x : num) = s x`;

val insert_def = Define `
  insert(s : num -> bool, x : num) =
    let s1 y = if x = y then T else s x
    in s1
  `;

val upto_def = Define `
  upto(n : num) =
    if n = 0 then empty else insert(upto(n-1),n)
  `;

val main_def = Define `
  main (n : num) = (upto n, 100)`;

val defs = [empty_def, member_def, insert_def, upto_def];

(*
val (newdefs, judgements) = elim_hof defs;

val defs1 = List.take(defs, 3);
val defs2 = List.drop(defs, 3);
val newdefs1 = List.take(newdefs, 6);
val newdefs2 = List.drop(newdefs, 6);

set_goal ([], List.nth(judgements, 3))      (* set_goal ([], ``!m. dispatch1(upto' n, j) = upto n m``)  *)

Induct_on `n` THENL [
  ONCE_REWRITE_TAC (defs2 @ newdefs2) THEN
    expandf (RW_TAC arith_ss (defs1 @ newdefs1)),
  
  ONCE_REWRITE_TAC (defs2 @ newdefs2) THEN
    RW_TAC arith_ss [LET_THM] THEN
    expandf (RW_TAC arith_ss (defs1 @ newdefs1)) THEN
    Q.UNABBREV_TAC `s1` THEN 
    RW_TAC std_ss []
]

*)

(*-----------------------------------------------------------------------------------------*)
(* Example 2.                                                                              *)
(*-----------------------------------------------------------------------------------------*)

val f_def = Define `
  f x = x * 2 < x + 10`;

val g_def = Define `
  g (s, x) = 
    let h1 = \y. y + x in
        if s x then h1 else let h2 = \y. h1 y * x in h2`;

val k_def = Define `
  k x = if x = 0 then 1 else (g (f,x)) (k(x-1))`

val defs = [f_def, g_def, k_def];

(*-----------------------------------------------------------------------------------------*)

end (* struct *)

