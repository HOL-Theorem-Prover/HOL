(*
load "abs_tools";
load "quoteTheory";
load "prelimTheory";
load "canonicalTheory";
load "ringTheory";
*)

open HolKernel Parse boolLib abs_tools;
open BasicProvers Datatype;

val _ = new_theory "EVAL_ringNorm";

open EVAL_ringTheory EVAL_canonicalTheory;

val r = “r:'a ring”;
val sr = “semi_ring_of r”;
val _ = set_assums [ “is_ring ^r” ];
val _ = app (C add_impl_param [r]) ["R0","R1","RP","RM","RN"];
val _ = app (fn s => temp_overload_on (s, Parse.Term [QUOTE ("ring_"^s)]))
            ["R0","R1","RP","RM","RN"];

val rth = IMPORT_THY
    { Vals = [r],
      Inst = map ASSUME (get_assums()),
      Rule = REWRITE_RULE[ring_accessors],
      Rename = K NONE }
    "EVAL_ring"
fun rTAB s = valOf $ Symtab.lookup rth s

val canontable =
  (* { canonical_sum_merge_ok, canonical_sum_prod_ok,
      canonical_sum_scalar3_ok, canonical_sum_simplify_ok,
      ics_aux_def, interp_cs_def, interp_m_def, interp_vl_def,
      ivl_aux_def, interp_sp_def, canonical_sum_merge_def,
      monom_insert_def, varlist_insert_def, canonical_sum_scalar_def,
      canonical_sum_scalar2_def, canonical_sum_scalar3_def,
      canonical_sum_prod_def, canonical_sum_simplify_def,
      spolynom_normalize_def, spolynom_simplify_def, ... } = *)
  IMPORT_THY
    { Vals = [sr],
      Inst = [rTAB "ring_is_semi_ring"],
      Rule = REWRITE_RULE[ semi_ring_of_def,
                           EVAL_semiringTheory.semi_ring_accessors ],
      Rename = fn x => SOME ("r_"^x) }
    "EVAL_canonical"

fun cTAB s = valOf $ Symtab.lookup canontable s
val interp_sp_def = cTAB "interp_sp_def"
val canonical_sum_merge_def = cTAB "canonical_sum_merge_def"
val monom_insert_def = cTAB "monom_insert_def"
val varlist_insert_def = cTAB "varlist_insert_def"
val canonical_sum_scalar3_def = cTAB "canonical_sum_scalar3_def"
val canonical_sum_scalar2_def = cTAB "canonical_sum_scalar2_def"
val canonical_sum_scalar_def = cTAB "canonical_sum_scalar_def"
val canonical_sum_prod_def = cTAB "canonical_sum_prod_def"
val canonical_sum_simplify_def = cTAB "canonical_sum_simplify_def"
val ivl_aux_def = cTAB "ivl_aux_def"
val interp_vl_def = cTAB "interp_vl_def"
val interp_m_def = cTAB "interp_m_def"
val ics_aux_def = cTAB "ics_aux_def"
val interp_cs_def = cTAB "interp_cs_def"
val spolynom_normalize_def = cTAB "spolynom_normalize_def"
val spolynom_simplify_def = cTAB "spolynom_simplify_def"
val canonical_sum_scalar3_ok = cTAB "canonical_sum_scalar3_ok"
val canonical_sum_prod_ok = cTAB "canonical_sum_prod_ok"
val canonical_sum_simplify_ok = cTAB "canonical_sum_simplify_ok"
val canonical_sum_merge_ok = cTAB "canonical_sum_merge_ok"

val _ = asm_save_thm("interp_sp_def", interp_sp_def);
val _ = asm_save_thm("canonical_sum_merge_def",
                     canonical_sum_merge_def);
val _ = asm_save_thm("monom_insert_def", monom_insert_def);
val _ = asm_save_thm("varlist_insert_def", varlist_insert_def);
val _ = asm_save_thm("canonical_sum_scalar_def", canonical_sum_scalar_def);
val _ = asm_save_thm("canonical_sum_scalar2_def", canonical_sum_scalar2_def);
val _ = asm_save_thm("canonical_sum_scalar3_def", canonical_sum_scalar3_def);
val _ = asm_save_thm("canonical_sum_prod_def", canonical_sum_prod_def);
val _ = asm_save_thm("canonical_sum_simplify_def",
                     canonical_sum_simplify_def);
val _ = asm_save_thm("ivl_aux_def", ivl_aux_def);
val _ = asm_save_thm("interp_vl_def", interp_vl_def);
val _ = asm_save_thm("interp_m_def", interp_m_def);
val _ = asm_save_thm("ics_aux_def", ics_aux_def);
val _ = asm_save_thm("interp_cs_def", interp_cs_def);
val _ = asm_save_thm("spolynom_normalize_def", spolynom_normalize_def);
val _ = asm_save_thm("spolynom_simplify_def", spolynom_simplify_def);



fun ARW_TAC l = RW_TAC bool_ss
    ([ rTAB "mult_one_left", rTAB "mult_one_right",
       rTAB "plus_zero_left", rTAB "plus_zero_right",
       rTAB "mult_zero_left", rTAB "mult_zero_right" ]@l);



(* ring normalization *)

val _ = Hol_datatype
 ` polynom =
     Pvar of index
   | Pconst of 'a
   | Pplus of polynom => polynom
   | Pmult of polynom => polynom
   | Popp of polynom `;

val polynom_normalize_def = Define `
   (polynom_normalize (Pvar i) = (Cons_varlist [i] Nil_monom))
/\ (polynom_normalize (Pconst c) = (Cons_monom c [] Nil_monom))
/\ (polynom_normalize (Pplus pl pr) =
      (r_canonical_sum_merge (polynom_normalize pl)
                               (polynom_normalize pr)))
/\ (polynom_normalize (Pmult pl pr) =
      (r_canonical_sum_prod (polynom_normalize pl)
                              (polynom_normalize pr)))
/\ (polynom_normalize (Popp p) =
      (r_canonical_sum_scalar3 (RN R1) [] (polynom_normalize p))) `;

val polynom_simplify_def = Define `
  polynom_simplify x =
       r_canonical_sum_simplify (polynom_normalize x) `;


val interp_p_def = Define `
   (interp_p vm (Pconst c) = c)
/\ (interp_p vm (Pvar i) = varmap_find i vm)
/\ (interp_p vm (Pplus p1 p2) = RP (interp_p vm p1) (interp_p vm p2))
/\ (interp_p vm (Pmult p1 p2) = RM (interp_p vm p1) (interp_p vm p2))
/\ (interp_p vm (Popp p1) = RN (interp_p vm p1)) `;


val polynom_normalize_ok = asm_store_thm
    ("polynom_normalize_ok",
     Term` !vm p. r_interp_cs vm (polynom_normalize p)
                              = interp_p vm p `,
Induct_on `p` THEN REPEAT GEN_TAC THEN
ARW_TAC [ polynom_normalize_def, interp_cs_def, interp_p_def,
          ics_aux_def, canonical_sum_merge_ok, canonical_sum_prod_ok,
          canonical_sum_scalar3_ok, interp_m_def, interp_vl_def,
          ivl_aux_def, rTAB "neg_mult" ]);


val polynom_simplify_ok = asm_store_thm
    ("polynom_simplify_ok",
     Term` !vm p. r_interp_cs vm (polynom_simplify p)
                              = interp_p vm p `,
ARW_TAC [ polynom_simplify_def,
          canonical_sum_simplify_ok,
          polynom_normalize_ok ]);


val _ = record_terms (
  map rator [
    “interp_p”, “polynom_simplify”, “polynom_normalize”,
    “r_canonical_sum_merge”, “r_monom_insert”, “r_varlist_insert”,
    “r_canonical_sum_scalar”, “r_canonical_sum_scalar2”,
    “r_canonical_sum_scalar3”, “r_canonical_sum_prod”,
    “r_canonical_sum_simplify”, “r_ivl_aux”, “r_interp_vl”,
    “r_interp_m”, “r_ics_aux”, “r_interp_cs”, “r_spolynom_normalize”,
    “r_spolynom_simplify”, “r_interp_sp”
  ]
)

val _ = export_theory();
