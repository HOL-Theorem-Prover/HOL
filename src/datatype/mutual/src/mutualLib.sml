(* ===================================================================== *)
(* FILE          : mutualLib.sml                                         *)
(* VERSION       : 1.0                                                   *)
(* DESCRIPTION   : Creates the structure of the exported identifiers     *)
(*                 for the improved mutual recursion library.            *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : April 21, 1998                                        *)
(* COPYRIGHT     : Copyright (c) 1998 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)


structure mutualLib =
    struct
        val list_Axiom = theorem "list" "list_Axiom"
        val sum_Axiom = theorem "sum" "sum_Axiom"
        val prod_Axiom =
            prove((--`!f. ?!g. !(x:'a) (y:'b).((g(x,y)):'c) = (f x y)`--),
                  GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN
                  REPEAT STRIP_TAC THENL
                  [(EXISTS_TAC (--`UNCURRY (f:'a -> 'b -> 'c)`--) THEN
                    REWRITE_TAC [definition "pair" "UNCURRY_DEF"]),
                   (CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
                    PURE_ONCE_REWRITE_TAC
                    [SYM(SPEC_ALL (theorem "pair" "PAIR"))] THEN
                    ASM_REWRITE_TAC[])]);

        val define_mutual_functions = Recftn.define_mutual_functions;

        val MUTUAL_INDUCT_THEN = Mutual_induct_then.MUTUAL_INDUCT_THEN;

    end

