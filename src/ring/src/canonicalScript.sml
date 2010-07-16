(*
load "abs_tools";
load "semi_ringTheory";
load "quoteTheory";
load "prelimTheory";
load "BasicProvers";
load "Datatype";
*)
open HolKernel Parse boolLib;
open BasicProvers Datatype;
open abs_tools;

val _ = new_theory "canonical";

open prelimTheory quoteTheory;

val sr = --`sr:'a semi_ring`--;
val _ = set_assums [ --`is_semi_ring ^sr`-- ];
val _ = app (C add_impl_param [sr]) ["SR0","SR1","SRP","SRM"];

val { plus_sym, plus_assoc, mult_sym, mult_assoc, distr_left,
      plus_permute, plus_rotate, mult_permute, mult_rotate, distr_right,
      plus_zero_left, plus_zero_right, mult_one_left, mult_one_right,
      mult_zero_left, mult_zero_right,... } =
  semi_ringTheory.IMPORT
    { Vals = [sr],
      Inst = map ASSUME (get_assums()),
      Rule = REWRITE_RULE[semi_ringTheory.semi_ring_accessors],
      Rename = K NONE }
;


(* useful tacs *)
val APP_DIFF = REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC);
fun ARW_TAC l = BasicProvers.RW_TAC bool_ss
    ([ mult_one_left, mult_one_right,
       plus_zero_left, plus_zero_right,
       mult_zero_left, mult_zero_right, compare_def]@l);



val _ = Hol_datatype
 ` canonical_sum =
     Nil_monom
   | Cons_monom of 'a => index list => canonical_sum
   | Cons_varlist of index list => canonical_sum `;


val canonical_sum_merge_def = Define `
  (canonical_sum_merge (Cons_monom c1 l1 t1) (Cons_monom c2 l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_monom c1 l1 (canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
        (Cons_monom (SRP c1 c2) l1 (canonical_sum_merge t1 t2))
        (Cons_monom c2 l2 (canonical_sum_merge (Cons_monom c1 l1 t1) t2)))
/\ (canonical_sum_merge (Cons_monom c1 l1 t1) (Cons_varlist l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_monom c1 l1 (canonical_sum_merge t1 (Cons_varlist l2 t2)))
        (Cons_monom (SRP c1 SR1) l1 (canonical_sum_merge t1 t2))
        (Cons_varlist l2 (canonical_sum_merge (Cons_monom c1 l1 t1) t2)))
/\ (canonical_sum_merge (Cons_varlist l1 t1) (Cons_monom c2 l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_varlist l1 (canonical_sum_merge t1 (Cons_monom c2 l2 t2)))
        (Cons_monom (SRP SR1 c2) l1 (canonical_sum_merge t1 t2))
        (Cons_monom c2 l2 (canonical_sum_merge (Cons_varlist l1 t1) t2)))
/\ (canonical_sum_merge (Cons_varlist l1 t1) (Cons_varlist l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_varlist l1 (canonical_sum_merge t1 (Cons_varlist l2 t2)))
        (Cons_monom (SRP SR1 SR1) l1 (canonical_sum_merge t1 t2))
        (Cons_varlist l2 (canonical_sum_merge (Cons_varlist l1 t1) t2)))
/\ (canonical_sum_merge s1 Nil_monom = s1)
/\ (canonical_sum_merge Nil_monom s2 = s2) `;


val monom_insert_def = Define `
   (monom_insert c1 l1 (Cons_monom c2 l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_monom c1 l1 (Cons_monom c2 l2 t2))
        (Cons_monom (SRP c1 c2) l1 t2)
        (Cons_monom c2 l2 (monom_insert c1 l1 t2)))
/\ (monom_insert c1 l1 (Cons_varlist l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_monom c1 l1 (Cons_varlist l2 t2))
        (Cons_monom (SRP c1 SR1) l1 t2)
        (Cons_varlist l2 (monom_insert c1 l1 t2)))
/\ (monom_insert c1 l1 s = Cons_monom c1 l1 s) `;


val varlist_insert_def = Define `
   (varlist_insert l1 (Cons_monom c2 l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_varlist l1 (Cons_monom c2 l2 t2))
        (Cons_monom (SRP SR1 c2) l1 t2)
        (Cons_monom c2 l2 (varlist_insert  l1 t2)))
/\ (varlist_insert l1 (Cons_varlist l2 t2) =
      compare (list_compare index_compare l1 l2)
        (Cons_varlist l1 (Cons_varlist l2 t2))
        (Cons_monom (SRP SR1 SR1) l1 t2)
        (Cons_varlist l2 (varlist_insert l1 t2)))
/\ (varlist_insert l1 s = Cons_varlist l1 s) `;


val canonical_sum_scalar_def = Define `
   (canonical_sum_scalar c0 (Cons_monom c l t) =
	Cons_monom (SRM c0 c) l (canonical_sum_scalar c0 t))
/\ (canonical_sum_scalar c0 (Cons_varlist l t) =
	Cons_monom c0 l (canonical_sum_scalar c0 t))
/\ (canonical_sum_scalar c0 Nil_monom = Nil_monom) `;


val canonical_sum_scalar2_def = Define `
   (canonical_sum_scalar2 l0 (Cons_monom c l t) =
	monom_insert c (list_merge index_lt l0 l)
	   (canonical_sum_scalar2 l0 t))
/\ (canonical_sum_scalar2 l0 (Cons_varlist l t) =
	varlist_insert (list_merge index_lt l0 l)
	   (canonical_sum_scalar2 l0 t))
/\ (canonical_sum_scalar2 l0 Nil_monom = Nil_monom) `;


val canonical_sum_scalar3_def = Define `
   (canonical_sum_scalar3 c0 l0 (Cons_monom c l t) =
	monom_insert (SRM c0 c) (list_merge index_lt l0 l)
	   (canonical_sum_scalar3 c0 l0 t))
/\ (canonical_sum_scalar3 c0 l0 (Cons_varlist l t) =
	monom_insert c0 (list_merge index_lt l0 l)
	   (canonical_sum_scalar3 c0 l0 t))
/\ (canonical_sum_scalar3 c0 l0 Nil_monom = Nil_monom) `;


val canonical_sum_prod_def = Define `
   (canonical_sum_prod (Cons_monom c1 l1 t1) s2 =
	canonical_sum_merge (canonical_sum_scalar3 c1 l1 s2)
			    (canonical_sum_prod t1 s2))
/\ (canonical_sum_prod (Cons_varlist l1 t1) s2 =
	canonical_sum_merge (canonical_sum_scalar2 l1 s2)
                            (canonical_sum_prod t1 s2))
/\ (canonical_sum_prod Nil_monom s2 = Nil_monom) `;


(* We require decidability of equality on our ring *)
val canonical_sum_simplify_def = Define `
   (canonical_sum_simplify (Cons_monom c l t) =
     if c = SR0 then canonical_sum_simplify t
     else if c = SR1 then Cons_varlist l (canonical_sum_simplify t)
     else Cons_monom c l (canonical_sum_simplify t))
/\ (canonical_sum_simplify (Cons_varlist l t) =
     Cons_varlist l (canonical_sum_simplify t))
/\ (canonical_sum_simplify Nil_monom = Nil_monom) `;


val ivl_aux_def = Define `
   (ivl_aux vm x [] = varmap_find x vm)
/\ (ivl_aux vm x (CONS x' t') =
     SRM (varmap_find x vm) (ivl_aux vm x' t')) `;

val interp_vl_def = Define `
   (interp_vl vm [] = SR1)
/\ (interp_vl vm (CONS x t) = ivl_aux vm x t) `;

val interp_m_def = Define `
   (interp_m vm c [] = c)
/\ (interp_m vm c (CONS x t) = SRM c (ivl_aux vm x t)) `;

val ics_aux_def = Define `
   (ics_aux vm a Nil_monom = a)
/\ (ics_aux vm a (Cons_varlist l t) =
	      SRP a (ics_aux vm (interp_vl vm l) t))
/\ (ics_aux vm a (Cons_monom c l t) =
	      SRP a (ics_aux vm (interp_m vm c l) t))
`;

val interp_cs_def = Define `
   (interp_cs vm Nil_monom = SR0)
/\ (interp_cs vm (Cons_varlist l t) =
		ics_aux vm (interp_vl vm l) t)
/\ (interp_cs vm (Cons_monom c l t) =
		ics_aux vm (interp_m vm c l) t)
`;


val ivl_aux_ok = asm_store_thm
    ("ivl_aux_ok",
     Term`!vm v i. ivl_aux vm i v
		   = SRM (varmap_find i vm) (interp_vl vm v)`,
REPEAT GEN_TAC THEN Induct_on `v` THEN
ARW_TAC [ivl_aux_def, interp_vl_def ]);



val varlist_merge_ok = asm_store_thm
    ("varlist_merge_ok",
     Term` !vm x y.
           interp_vl vm (list_merge index_lt x y)
            = SRM (interp_vl vm x) (interp_vl vm y)`,
Induct_on `x` THEN Induct_on `y` THEN REPEAT GEN_TAC THEN
ARW_TAC [ ivl_aux_def, ivl_aux_ok, interp_vl_def, mult_assoc,
	  list_merge_def, index_lt_def] THEN
APP_DIFF THEN
SUBST1_TAC (SPECL [Term`varmap_find h vm`,Term`varmap_find h' vm`,
		    Term`interp_vl vm x`] mult_rotate) THEN
REFL_TAC);


val ics_aux_ok = asm_store_thm
    ("ics_aux_ok",
     Term` !vm x s. ics_aux vm x s = SRP x (interp_cs vm s) `,
REPEAT GEN_TAC THEN Induct_on `s` THEN
ARW_TAC [ ics_aux_def, interp_cs_def]);


val interp_m_ok = asm_store_thm
    ("interp_m_ok",
     Term` !vm x l. interp_m vm x l = SRM x (interp_vl vm l) `,
Induct_on `l` THEN ARW_TAC [ interp_vl_def, interp_m_def ]);



val canonical_sum_merge_ok = asm_store_thm
    ("canonical_sum_merge_ok",
     Term` !vm x y. interp_cs vm (canonical_sum_merge x y)
                  = SRP (interp_cs vm x) (interp_cs vm y) `,
Induct_on `x` THEN Induct_on `y` THEN REPEAT GEN_TAC THEN
Cases_on `list_compare index_compare l' l` THEN
ARW_TAC [ interp_m_def, interp_cs_def, canonical_sum_merge_def,
	  ics_aux_ok, interp_m_ok, distr_left,mult_assoc, plus_assoc ] THEN
TRY (POP_ASSUM (SUBST1_TAC o REWRITE_RULE[compare_list_index])) THEN
APP_DIFF THEN
PROVE_TAC[plus_permute,plus_rotate]);



val monom_insert_ok = asm_store_thm
    ("monom_insert_ok",
     Term` !vm a l s. interp_cs vm (monom_insert a l s)
                  = SRP (SRM a (interp_vl vm l)) (interp_cs vm s) `,
Induct_on `s` THEN REPEAT GEN_TAC THEN
Cases_on `list_compare index_compare l' l` THEN
ARW_TAC [ interp_cs_def, ics_aux_ok, interp_m_ok, distr_left, plus_assoc,
	  monom_insert_def ] THEN APP_DIFF THEN
PROVE_TAC [plus_sym, compare_list_index]);


val varlist_insert_ok = asm_store_thm
    ("varlist_insert_ok",
     Term` !vm l s. interp_cs vm (varlist_insert l s)
                  = SRP (interp_vl vm l) (interp_cs vm s) `,
Induct_on `s` THEN REPEAT GEN_TAC THEN
Cases_on `list_compare index_compare l' l` THEN
ARW_TAC [ interp_cs_def, ics_aux_ok, interp_m_ok, distr_left, plus_assoc,
	  varlist_insert_def ] THEN APP_DIFF THEN
PROVE_TAC [plus_sym, compare_list_index]);


val canonical_sum_scalar_ok =asm_store_thm
    ("canonical_sum_scalar_ok",
     Term` !vm a s.  interp_cs vm (canonical_sum_scalar a s)
                   = SRM a (interp_cs vm s) `,
Induct_on `s` THEN REPEAT GEN_TAC THEN
ARW_TAC [ interp_cs_def, interp_m_ok, mult_assoc, distr_right, ics_aux_ok,
	  canonical_sum_scalar_def ] THEN APP_DIFF);


val canonical_sum_scalar2_ok =asm_store_thm
    ("canonical_sum_scalar2_ok",
     Term` !vm l s.  interp_cs vm (canonical_sum_scalar2 l s)
                   = SRM (interp_vl vm l)  (interp_cs vm s) `,
Induct_on `s` THEN REPEAT GEN_TAC THEN
ARW_TAC [ interp_cs_def, interp_m_ok, mult_assoc, distr_right, ics_aux_ok,
	  monom_insert_ok, varlist_merge_ok, varlist_insert_ok,
	  canonical_sum_scalar2_def ] THEN APP_DIFF THEN
PROVE_TAC[mult_sym]);


val canonical_sum_scalar3_ok =asm_store_thm
    ("canonical_sum_scalar3_ok",
     Term` !vm c l s.  interp_cs vm (canonical_sum_scalar3 c l s)
                 = SRM (SRM c (interp_vl vm l))  (interp_cs vm s) `,
Induct_on `s` THEN REPEAT GEN_TAC THEN
ARW_TAC [ interp_cs_def, interp_m_ok, mult_assoc, distr_right, ics_aux_ok,
	  monom_insert_ok, varlist_merge_ok, varlist_insert_ok,
	  canonical_sum_scalar3_def ] THEN APP_DIFF THEN
PROVE_TAC[mult_permute]);



val canonical_sum_prod_ok = asm_store_thm
    ("canonical_sum_prod_ok",
     Term` ! vm x y.
       interp_cs vm (canonical_sum_prod x y)
       = SRM (interp_cs vm x) (interp_cs vm y) `,
Induct_on `x` THEN
ARW_TAC [ interp_cs_def, mult_assoc, distr_left, ics_aux_ok, interp_m_ok,
	  canonical_sum_prod_def, canonical_sum_scalar2_ok,
	  canonical_sum_scalar3_ok, canonical_sum_merge_ok]);



val canonical_sum_simplify_ok = asm_store_thm
    ("canonical_sum_simplify_ok",
     Term` !vm s. interp_cs vm (canonical_sum_simplify s)
			      = interp_cs vm s `,
Induct_on `s` THEN REPEAT GEN_TAC THEN
ARW_TAC [ canonical_sum_simplify_def,
	  interp_cs_def, ics_aux_ok,
	  canonical_sum_merge_ok, canonical_sum_prod_ok,
 	  interp_m_ok, interp_vl_def, ivl_aux_def ]);


(* semi-ring normalization *)

val _ = Hol_datatype
 ` spolynom =
     SPvar of index
   | SPconst of 'a
   | SPplus of spolynom => spolynom
   | SPmult of spolynom => spolynom `;

val spolynom_normalize_def = Define `
   (spolynom_normalize (SPvar i) = (Cons_varlist [i] Nil_monom))
/\ (spolynom_normalize (SPconst c) = (Cons_monom c [] Nil_monom))
/\ (spolynom_normalize (SPplus l r) =
      (canonical_sum_merge (spolynom_normalize l)
      	                      (spolynom_normalize r)))
/\ (spolynom_normalize (SPmult l r) =
      (canonical_sum_prod (spolynom_normalize l)
      	                     (spolynom_normalize r))) `;


val spolynom_simplify_def = Define `
  spolynom_simplify x =
    canonical_sum_simplify (spolynom_normalize x) `;



val interp_sp_def = Define `
   (interp_sp vm (SPconst c) = c)
/\ (interp_sp vm (SPvar i) = varmap_find i vm)
/\ (interp_sp vm (SPplus p1 p2) =
      SRP (interp_sp vm p1) (interp_sp vm p2))
/\ (interp_sp vm (SPmult p1 p2) =
      SRM (interp_sp vm p1) (interp_sp vm p2)) `;


val spolynomial_normalize_ok = asm_store_thm
    ("spolynomial_normalize_ok",
     Term` !vm p. interp_cs vm (spolynom_normalize p)
			      = interp_sp vm p `,
Induct_on `p` THEN REPEAT GEN_TAC THEN
ARW_TAC [ spolynom_normalize_def, interp_cs_def, interp_sp_def,
	  ics_aux_def, canonical_sum_merge_ok, canonical_sum_prod_ok,
 	  interp_m_def, interp_vl_def, ivl_aux_def]);


val spolynomial_simplify_ok = asm_store_thm
    ("spolynomial_simplify_ok",
     Term` !vm p. interp_cs vm (spolynom_simplify p)
			      = interp_sp vm p `,
ARW_TAC [ spolynom_simplify_def,
	  canonical_sum_simplify_ok,
	  spolynomial_normalize_ok ]);


val _ = export_param_theory();
