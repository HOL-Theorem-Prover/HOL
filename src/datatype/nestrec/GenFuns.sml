(* =====================================================================*)
(* FILE          : gen_funs.sig                                         *)
(* DESCRIPTION   : This is a collection of ad_hoc functions and         *)
(*                 theorems that are useful in the package for          *)
(*                 nested recursive types.                              *)
(*                                                                      *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories               *)
(* DATE          : 94.03.13                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure GenFuns :> GenFuns =
    struct

open NestedRecMask HolKernel Parse basicHol90Lib;
infix THEN THENL THENC;

 type hol_type = Type.hol_type
 type term = Term.term
 type thm = Thm.thm
 type conv = Abbrev.conv

        fun dom_cod_ty (ty:hol_type) =
            let
                val {Tyop, Args} = dest_type ty
                val {Domain, Codomain} =
                    if Tyop = "fun" then
                        (case Args
                             of [Domain, Codomain] => {Domain = Domain,
                                                       Codomain = Codomain}
                           | _ => raise HOL_ERR {message= "bad argument list",
                                                 origin_function =  "dom_cod",
                                                 origin_structure = "GenFuns"})
                    else raise HOL_ERR {message= "operator not a function",
                                        origin_function =  "dom_cod_ty",
                                        origin_structure = "GenFuns"}
            in
                {dom = Domain, cod = Codomain}
            end handle HOL_ERR _ =>
                raise HOL_ERR {origin_structure = "GenFuns",
                               origin_function = "dom_cod_ty",
                               message = "not a type operator"};
                    
        fun dom_cod (t:term) = dom_cod_ty (type_of t);


        fun forall_map f thm =
        let val xs = #1(strip_forall(concl thm))
        in GENL xs (f (SPECL xs thm)) end


        val disj_map_lemma = 
        prove((--`!A1 A2 B1 B2.((A1 \/ A2) /\ (A1 ==> B1) /\ (A2 ==> B2)) ==>
                   (B1 \/ B2)`--),
        REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);

        fun disj_map f thm =
            let val {disj1, disj2} = dest_disj (concl thm)
                val A1 = ASSUME disj1
                val A2 = ASSUME disj2
                val B1 = disj_map f A1
                val B2 = disj_map f A2
                val A1impB1 = DISCH disj1 B1
                val A2impB2 = DISCH disj2 B2
            in
                MP (SPECL [disj1, disj2, (concl B1), (concl B2)]
                          disj_map_lemma)
                   (CONJ thm (CONJ A1impB1 A2impB2))
            end
            handle (HOL_ERR {origin_function = "dest_disj",...}) => f thm


        fun conj_map f th =
            let
                val conj1 = CONJUNCT1 th
                val conj2 = CONJUNCT2 th
            in
                CONJ (conj_map f conj1) (conj_map f conj2)
            end handle HOL_ERR _ => f th;



        fun conj_map_term f t =
            let
                val {conj1, conj2} = dest_conj t
            in
                (conj_map_term f conj1) @ (conj_map_term f conj2)
            end handle HOL_ERR _ => [f t]
                
        fun mk_poly_comb {Rator:term, Rand:term} =
            let
                val {dom, cod} = dom_cod Rator
                val poly_match = match_type dom (type_of Rand)
                val new_Rator = inst poly_match Rator
            in
                mk_comb {Rator = new_Rator, Rand = Rand}
            end handle HOL_ERR {message = s, ...} =>
                raise HOL_ERR {message = s,
                               origin_function = "mk_poly_comb",
                               origin_structure = "GenFuns"};
                    
        fun get_quant_term dest_quant t =
            let
                val {Body, Bvar} = dest_quant t
                val {vars, base_t} = get_quant_term dest_quant Body
            in
                {vars = Bvar::vars, base_t = base_t}
            end
        handle HOL_ERR _ => {vars = [], base_t = t};
            
        val get_forall_term = get_quant_term dest_forall;
        val get_exists_term = get_quant_term dest_exists;
            
        fun dest_exists_unique t =
            let
                val {Rand, ...} = dest_comb t
            in
                dest_abs Rand
            end;
            
        val get_exists_unique_term = get_quant_term dest_exists_unique;
            
        fun curry_to_list ty =
            let
                val {dom, cod} = dom_cod_ty ty
                val {arg_types, cod_type} = curry_to_list cod
            in
                {arg_types = dom::arg_types, cod_type = cod_type}
            end handle HOL_ERR {origin_function =  "dom_cod_ty", ...} =>
                {arg_types = [], cod_type = ty};
                
        fun list_to_curry {arg_types = [], cod_type} = cod_type
          | list_to_curry {arg_types = arg_ty::arg_tys, cod_type} =
            let
                val ty = list_to_curry {arg_types = arg_tys,
					cod_type = cod_type}
            in
                mk_type {Tyop = "fun", Args = [arg_ty, ty]}
            end;
            
        fun applist [] t = t
          | applist (v::l) t = applist l (mk_poly_comb {Rator = t, Rand = v});
            
        fun abslist [] t = t
          | abslist (v::l) t = mk_abs {Bvar = v, Body = abslist l t};
            
        fun dest_appln appln =
            let
                val {Rator, Rand} = dest_comb appln
                val {func, args} = dest_appln Rator
            in
                {func = func, args = args @ [Rand]}
            end handle HOL_ERR _ => {func = appln, args = []}


        fun present_strings [] = ""
          | present_strings (s::[]) = s
          | present_strings (s::s'::[]) = s ^ " and " ^ s'
          | present_strings (s::l) = s ^ ", " ^ present_strings l

        val one_one_lemma = prove((--`!(f:'a -> 'b) g.(!x. f (g x) = x) ==>
                                  (!x1 x2. (g x1 = g x2) = (x1 = x2))`--),
        REPEAT STRIP_TAC THEN EQ_TAC THENL
        [(DISCH_THEN (fn th1 =>
          FIRST_ASSUM (fn th2 =>
          PURE_ONCE_REWRITE_TAC [SYM (SPEC_ALL th2)]) THEN
          REWRITE_TAC [AP_TERM (--`f:'a -> 'b`--) th1])),
         (DISCH_TAC THEN ASM_REWRITE_TAC[])])

        val CURRY_LEMMA = 
            prove((--`((A /\ B) ==> C) = (A ==> B ==> C)`--),
                  EQ_TAC THEN REPEAT STRIP_TAC THEN REPEAT RES_TAC)

        val UNCURRY_LEMMA = SYM CURRY_LEMMA

(* Not used
        local
            val A = (--`A:bool`--)
            val B = (--`B:bool`--)
            val C = (--`C:bool`--)
        in
            fun CURRY_CONV tm =
                let val {ant,conseq} = dest_imp tm
                    val {conj1,conj2} = dest_conj ant
                in INST [{redex = A, residue = conj1},
                         {redex = B, residue = conj2},
                         {redex = C, residue = conseq}] CURRY_LEMMA
                end
        end
*)

        fun REPEAT_UNDISCH thm =
            let fun REP_UND (info as {thm, hyps}) =
                let val SOME_h = SOME (#ant(dest_imp (concl thm)))
                    handle HOL_ERR _ => NONE
                in case SOME_h of NONE => info
                         | SOME h => 
                               REP_UND {thm = UNDISCH thm, hyps = h :: hyps}
                end
            in
                REP_UND {thm = thm, hyps = []}
            end



        (*
         * LIST_EXISTS_IMP_CONV :
         * |- (? x1 ... xn. P x1 ... xn ==> Q) =
         *    ((!x1 ... xn. P x1 ... xn) ==> Q)
         *)

        fun LIST_EXISTS_IMP_CONV tm =
            if is_exists tm
                then (RAND_CONV (ABS_CONV LIST_EXISTS_IMP_CONV) THENC
                      EXISTS_IMP_CONV) tm
            else REFL tm


        (*
         * LEFT_IMP_LIST_FORALL_CONV :
         * |- ((!x1 ...  xn.P x1 ...  xn) ==> Q) =
         *    (? x1 ... xn. P x1 ... xn ==> Q)
         *)

        fun LEFT_IMP_LIST_FORALL_CONV tm =
            if is_forall(#ant(dest_imp tm))
                then (LEFT_IMP_FORALL_CONV THENC
                      RAND_CONV (ABS_CONV LEFT_IMP_LIST_FORALL_CONV)) tm
            else REFL tm

    end (* structure GenFuns *)
