(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)
structure bvec :> bvec =
struct
	
    open MuddyCore
	
    open bdd fdd 
	
    prim_type bvec
    type const = int
	
    val bvectrue: precision -> bvec = app1 (symb "mlbvec_true")
    val bvecfalse: precision -> bvec = app1 (symb "mlbvec_false")
    val con: precision -> const -> bvec = app2 (symb "mlbvec_con")
	
    val var: precision -> varnum -> int -> bvec = app3 (symb "mlbvec_var")
    val varfdd: fddvar -> bvec = app1 (symb "mlbvec_varfdd")
	
    val coerce: precision -> bvec -> bvec = app2 (symb "mlbvec_coerce")
	
    val isConst: bvec -> bool = app1 (symb "mlbvec_isconst")
    val getConst: bvec -> const = app1 (symb "mlbvec_getconst")
	
    fun lookupConst bvec = 
	if isConst bvec then SOME(getConst bvec) else NONE
	    
    val add: bvec * bvec -> bvec = cur2 (symb "mlbvec_add")
    val sub: bvec * bvec -> bvec = cur2 (symb "mlbvec_sub")

    val mul     : bvec * bvec -> bvec = cur2 (symb "mlbvec_mul")
    val mulfixed: bvec * const -> bvec = cur2 (symb "mlbvec_mulfixed")

    val op div : bvec * bvec -> bvec * bvec = cur2 (symb "mlbvec_div")
    val divfixed: bvec * const -> bvec * bvec = cur2 (symb "mlbvec_divfixed")
    val divi      = #1 o op div
    val divifixed = #1 o divfixed
    val modu      = #2 o op div
    val modufixed = #2 o divfixed

(*    val divifixed: bvec * const -> bvec = cur2 (symb "mlbvec_divi")
    val modufixed: bvec * const -> bvec = cur2 (symb "mlbvec_modu")
*)
    val shl     : bvec -> bvec -> bdd -> bvec = app3 (symb "mlbvec_shl")
    val shlfixed: bvec -> int -> bdd -> bvec = app3 (symb "mlbvec_shlfixed")

    val shr     : bvec -> bvec -> bdd -> bvec = app3 (symb "mlbvec_shr")
    val shrfixed: bvec -> int  -> bdd -> bvec = app3 (symb "mlbvec_shrfixed")

    val lth: bvec * bvec -> bdd = cur2 (symb "mlbvec_lth")
    val lte: bvec * bvec -> bdd = cur2 (symb "mlbvec_lte")
    val gth: bvec * bvec -> bdd = cur2 (symb "mlbvec_gth")
    val gte: bvec * bvec -> bdd = cur2 (symb "mlbvec_gte")
    val equ: bvec * bvec -> bdd = cur2 (symb "mlbvec_equ")
    val neq: bvec * bvec -> bdd = cur2 (symb "mlbvec_neq")
end
