open List_conv;

LIST_CONV (--`SNOC h []:'a list`--);
LIST_CONV (--`SNOC h (CONS h t):'a list`--);

LIST_CONV (--`NULL ([]:'a list)`--);
LIST_CONV (--`NULL (CONS h t:'a list)`--);
LIST_CONV (--`NULL (SNOC h t:'a list)`--);
LIST_CONV (--`NULL (APPEND l1 l2 :'a list)`--);
LIST_CONV (--`NULL [1;2;3]`--);
LIST_CONV (--`NULL (REVERSE (l:bool list))`--);
LIST_CONV (--`NULL (FLAT (l:'a list list))`--);

LIST_CONV (--`LENGTH ([]:'a list)`--);
LIST_CONV (--`LENGTH (CONS h t:'a list)`--);
LIST_CONV (--`LENGTH (CONS h []:'a list)`--);
LIST_CONV (--`LENGTH (SNOC h t:'a list)`--);
LIST_CONV (--`LENGTH (SNOC h []:'a list)`--);
LIST_CONV (--`LENGTH (APPEND l1 l2 :'a list)`--);
LIST_CONV (--`LENGTH [1;2;3]`--);
LIST_CONV (--`LENGTH (SNOC 1 (SNOC 2 (SNOC 3 [])))`--);
LIST_CONV (--`LENGTH (FLAT (l :num list list))`--);
LIST_CONV (--`LENGTH (FLAT (l :'a list list))`--);

LIST_CONV (--`MAP (P:'a list -> 'a) []`--);
LIST_CONV (--`MAP (P:'a list -> 'a) (CONS h t)`--);
LIST_CONV (--`MAP (P:'a list -> 'a) (CONS h [])`--);
LIST_CONV (--`MAP (P:'a list -> 'a) (SNOC h t)`--);
LIST_CONV (--`MAP (P:'a list -> 'a) (SNOC h [])`--);
LIST_CONV (--`MAP (P:'a list -> 'a) [x;y;z]`--);
LIST_CONV (--`MAP (P:num list ->num) (APPEND l1 l2)`--);
LIST_CONV (--`MAP (f:'a ->'b) (FLAT l)`--);
LIST_CONV (--`MAP (f:num ->num) (FLAT l)`--);

LIST_CONV (--`FILTER (g:'b ->bool) []`--);
LIST_CONV (--`FILTER (g:'b ->bool) (CONS h t)`--);
LIST_CONV (--`FILTER (g:'b ->bool) (SNOC h t)`--);
LIST_CONV (--`FILTER (P:num list -> bool) (APPEND l1 l2)`--);
LIST_CONV (--`FILTER (f:'a  -> bool) (FLAT l)`--);

LIST_CONV (--`APPEND (l1:'a list) []`--);
LIST_CONV (--`APPEND [] (l1:'a list)`--);
LIST_CONV (--`APPEND (l1:'a list) (CONS h t)`--);
(* LIST_CONV (--`APPEND (l1:'a list) (APPEND l2 l3)`--)
   handle e => Raise e; BLOCKED *)
LIST_CONV (--`APPEND (APPEND l2 l3)(l1:'a list)`--);
LIST_CONV (--`APPEND (l1:'a list) (SNOC h t)`--);
(* LIST_CONV (--`APPEND (SNOC h t) (l1:'a list)`--)
   handle e => Raise e; BLOCKED *)
LIST_CONV (--`APPEND [1;2;3] [4;5;6]`--);
LIST_CONV (--`APPEND (SNOC 1 (SNOC 2 (SNOC 3 []))) [4;5;6]`--);
LIST_CONV (--`APPEND  [4;5;6] (SNOC 1 (SNOC 2 (SNOC 3 [])))`--);
LIST_CONV (--`APPEND [x] (l1:'a list)`--);
LIST_CONV (--`APPEND (CONS h t) ((CONS h t):'a list)`--);
LIST_CONV (--`APPEND (CONS h1 t1) ((SNOC h2 t2):'a list)`--);
LIST_CONV (--`APPEND (CONS h t) (l1:'a list)`--);
LIST_CONV (--`APPEND (l1:'a list) (CONS h t)`--);

LIST_CONV (--`FLAT (CONS h t :'a list list)`--);
LIST_CONV (--`FLAT (SNOC h t :'a list list)`--);
LIST_CONV (--`FLAT ([] :'a list list)`--);
LIST_CONV (--`FLAT (FLAT (l :'a list list list))`--);
LIST_CONV (--`FLAT (APPEND l1 l2 :'a list list)`--);
LIST_CONV (--`FLAT ([[h]] :'a list list)`--);

LIST_CONV (--`ALL_EL P ([]:'a list)`--);
LIST_CONV (--`ALL_EL P (CONS h t:'a list)`--);
LIST_CONV (--`ALL_EL P (SNOC h t:'a list)`--);
LIST_CONV (--`ALL_EL P (APPEND l1 l2:'a list)`--);
LIST_CONV (--`ALL_EL P (REVERSE (l:num list))`--);
LIST_CONV (--`ALL_EL P (FLAT (l:'a list list))`--);

LIST_CONV (--`SOME_EL P ([]:'a list)`--);
LIST_CONV (--`SOME_EL P (CONS h t:'a list)`--);
LIST_CONV (--`SOME_EL P (SNOC h t:'a list)`--);
LIST_CONV (--`SOME_EL P (APPEND l1 l2:'a list)`--);
LIST_CONV (--`SOME_EL P (REVERSE (l:'a list))`--);
LIST_CONV (--`SOME_EL P (FLAT (l:'a list list))`--);

LIST_CONV (--`IS_EL P ([]:'a list)`--);
LIST_CONV (--`IS_EL P (CONS h t:'a list)`--);
LIST_CONV (--`IS_EL P (SNOC h t:'a list)`--);
LIST_CONV (--`IS_EL P (APPEND l1 l2:'a list)`--);
LIST_CONV (--`IS_EL x (REVERSE (l:'a list))`--);
LIST_CONV (--`IS_EL P (FLAT (l:'a list list))`--);

LIST_CONV (--`SUM []`--);
LIST_CONV (--`SUM (CONS h t)`--);
LIST_CONV (--`SUM (SNOC h t)`--);
LIST_CONV (--`SUM (APPEND l1 l2)`--);
LIST_CONV (--`SUM (REVERSE (l:num list))`--);
LIST_CONV (--`SUM (FLAT l)`--);

LIST_CONV (--`AND_EL []`--);
LIST_CONV (--`AND_EL (CONS h t)`--);
LIST_CONV (--`AND_EL (SNOC h t)`--);
LIST_CONV (--`AND_EL (APPEND l1 l2)`--);
LIST_CONV (--`AND_EL (REVERSE l)`--);
LIST_CONV (--`AND_EL (FLAT l)`--);

LIST_CONV (--`OR_EL []`--);
LIST_CONV (--`OR_EL (CONS h t)`--);
LIST_CONV (--`OR_EL (SNOC h t)`--);
LIST_CONV (--`OR_EL (APPEND l1 l2)`--);
LIST_CONV (--`OR_EL (REVERSE l)`--);
LIST_CONV (--`OR_EL (FLAT l)`--);


LIST_CONV (--`REVERSE ([]:'a list)`--);
LIST_CONV (--`REVERSE (CONS h t:'a list)`--);
LIST_CONV (--`REVERSE (SNOC h t:'a list)`--);
LIST_CONV (--`REVERSE (APPEND l1 l2:'a list)`--);
LIST_CONV (--`REVERSE (FLAT l:'a list list)`--);

LIST_CONV (--`PREFIX P ([]:'a list)`--);
LIST_CONV (--`PREFIX P (CONS x l:'a list)`--);

LIST_CONV (--`SUFFIX P ([]:'a list)`--);
LIST_CONV (--`SUFFIX P (SNOC x l:'a list)`--);

LIST_CONV (--`(FLAT o REVERSE) ([]:'a list list)`--);
LIST_CONV (--`(FLAT o REVERSE) (CONS x l:'a list list)`--);
LIST_CONV (--`(FLAT o REVERSE) (APPEND l1 l2:'a list list)`--);
LIST_CONV (--`(FLAT o REVERSE) (FLAT l:'a list list)`--);

val db = list_thm_database ();

val COMM_ADD = prove((--`COMM $+`--),
   REWRITE_TAC[definition "operator" "COMM_DEF"] THEN
   REPEAT GEN_TAC THEN
   SUBST1_TAC(SPECL[(--`x:num`--),(--`y:num`--)]
                   (theorem "arithmetic"  "ADD_SYM")) THEN
   REWRITE_TAC[]);

val ASSOC_DEF = definition "operator" "ASSOC_DEF";
val RIGHT_ID_DEF = definition "operator" "RIGHT_ID_DEF";
val LEFT_ID_DEF = definition "operator" "LEFT_ID_DEF";
val MONOID_DEF = definition "operator" "MONOID_DEF";

val ADD_SYM = theorem "arithmetic"   "ADD_SYM";
val ADD_ASSOC = theorem "arithmetic" "ADD_ASSOC";
val ADD = definition "arithmetic"  "ADD";
val ADD_CLAUSES = theorem "arithmetic"  "ADD_CLAUSES";

val ASSOC_ADD = TAC_PROOF(([],    --`ASSOC $+`--),
    REWRITE_TAC[ASSOC_DEF,ADD_ASSOC]);

val RIGHT_ID_ADD_0 = TAC_PROOF(([], --`RIGHT_ID $+ 0`--),
    REWRITE_TAC[RIGHT_ID_DEF,ADD_CLAUSES]);

val LEFT_ID_ADD_0 = TAC_PROOF(([],    --`LEFT_ID $+ 0`--),
    REWRITE_TAC[LEFT_ID_DEF,ADD_CLAUSES]);

val MONOID_ADD_0 = TAC_PROOF(([],  --`MONOID $+ 0`--),
    REWRITE_TAC[MONOID_DEF,ASSOC_ADD,
    	LEFT_ID_ADD_0,RIGHT_ID_ADD_0]);


set_list_thm_database
     {Fold_thms =[theorem "List" "SUM_FOLDR", theorem "List" "SUM_FOLDL"],
      Aux_thms = [MONOID_ADD_0, COMM_ADD]};

LIST_CONV (--`SUM []`--);
LIST_CONV (--`SUM (CONS h t)`--);
LIST_CONV (--`SUM (SNOC h t)`--);
LIST_CONV (--`SUM (APPEND l1 l2)`--);
LIST_CONV (--`SUM (REVERSE (l:num list))`--);
LIST_CONV (--`SUM (FLAT l)`--);

set_list_thm_database {Fold_thms = [],  Aux_thms = []};

X_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"], Aux_thms = []}
               (--`SUM []`--);
X_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"], Aux_thms = []}
               (--`SUM (CONS h t)`--);
X_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDL"], Aux_thms = []}
               (--`SUM (SNOC h t)`--);
X_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"],
                Aux_thms = [MONOID_ADD_0]}
              (--`SUM (APPEND l1 l2)`--);
X_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"],
                Aux_thms = [MONOID_ADD_0]}
              (--`SUM (FLAT l)`--);


set_list_thm_database(db);

LIST_CONV (--`SUM []`--);
LIST_CONV (--`SUM (CONS h t)`--);
LIST_CONV (--`SUM (SNOC h t)`--);
LIST_CONV (--`SUM (APPEND l1 l2)`--);
LIST_CONV (--`SUM (REVERSE (l:num list))`--);
LIST_CONV (--`SUM (FLAT l)`--);


PURE_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"], Aux_thms = []}
               (--`SUM []`--);
PURE_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"], Aux_thms = []}
               (--`SUM (CONS h t)`--);
PURE_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDL"], Aux_thms = []}
               (--`SUM (SNOC h t)`--);
PURE_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"],
                Aux_thms = [MONOID_ADD_0]}
              (--`SUM (APPEND l1 l2)`--);
PURE_LIST_CONV {Fold_thms = [theorem "List" "SUM_FOLDR"],
                Aux_thms = [MONOID_ADD_0]}
              (--`SUM (FLAT l)`--);






(*
new_theory "foo";
val MULTL_FOLDR = new_definition ("MULTL_FOLDR",
       (--`MULTL l = FOLDR $* 1 l`--)
      );
val MULTL_FOLDL = new_definition ("MULTL_FOLDL",
       (--`MULTL_FOLDL l = FOLDL $* 1 l`--)
      );

?? ML type errors
LIST_CONV ([MULTL_FOLDR], []) (--`MULTL []`--);
LIST_CONV ([MULTL_FOLDR], []) (--`MULTL (CONS h t)`--);
LIST_CONV ([MULTL_FOLDL], []) (--`MULTL_FOLDL (SNOC h t)`--);
*)



(* EVALUATION CONVERSIONS *)

SUM_CONV (--`SUM []`--);
SUM_CONV (--`SUM [1]`--);
SUM_CONV (--`SUM [1;2;3;4]`--);


EL_CONV (--`EL 0 ([]:num list)`--);
EL_CONV (--`EL 0 [0]`--);
EL_CONV (--`EL 0 [0;1;2;3]`--);
EL_CONV (--`EL 1 [0;1;2;3]`--);
EL_CONV (--`EL 3 [0;1;2;3]`--);
EL_CONV (--`EL 3 [T;F;F;T]`--);

ELL_CONV (--`ELL 0 ([0]:num list)`--);
ELL_CONV (--`ELL 0 ([0;1;2;3]:num list)`--);
ELL_CONV (--`ELL 1 ([0;1;2;3]:num list)`--);
ELL_CONV (--`ELL 3 ([0;1;2;3]:num list)`--);
ELL_CONV (--`ELL 3 [T;F;F;T]`--);

FLAT_CONV (--`FLAT [[1;2;3;4];[2;3;4];[3;4]]`--);
FLAT_CONV (--`FLAT [[];[];([]:'a list)]`--);
FLAT_CONV (--`FLAT [[];[1];[]]`--);

APPEND_CONV (--`APPEND [1;2;3;4] [2;3;4]`--);

LENGTH_CONV (--`LENGTH [1;2;3;4]`--);
REVERSE_CONV(--`REVERSE [1;2;3;4]`--);
REVERSE_CONV(--`REVERSE [1]`--);
REVERSE_CONV(--`REVERSE ([]:'a list)`--);

SNOC_CONV(--`SNOC 5 []`--);
SNOC_CONV(--`SNOC 5 [1;2;3;4]`--);

LAST_CONV (--`LAST [1;2;3;4]`--);
BUTLAST_CONV (--`BUTLAST [1;2;3;4]`--);

SEG_CONV (--`SEG 2 3 [0;1;2;3;4;5;6]`--);
SEG_CONV (--`SEG 4 3 [0;1;2;3;4;5;6]`--);
SEG_CONV (--`SEG 4 0 [0;1;2;3;4;5;6]`--);

REPLICATE_CONV (--`REPLICATE 4 4`--);
REPLICATE_CONV (--`REPLICATE 0 4`--);

REPLICATE_CONV (--`REPLICATE 3 (x:bool)`--);
REPLICATE_CONV (--`REPLICATE 3 (SUC 3)`--);
REPLICATE_CONV (--`REPLICATE 3 T`--);
REPLICATE_CONV (--`REPLICATE 3 (1 + (2+ 3))`--);
REPLICATE_CONV (--`REPLICATE 3 [1;2;3]`--);
REPLICATE_CONV (--`REPLICATE 0 [1;2;3]`--);


FIRSTN_CONV(--`FIRSTN 2 [1;2;3;4]`--);
FIRSTN_CONV(--`FIRSTN 3 [1;2;3;4]`--);

BUTLASTN_CONV (--`BUTLASTN 2 [1;2;3;4]`--);

BUTFIRSTN_CONV (--`BUTFIRSTN 2 [1;2;3;4]`--);

LASTN_CONV (--`LASTN 2 [1;2;3;4]`--);
LASTN_CONV (--`LASTN 1 [1;2;3;4]`--);

MAP_CONV LENGTH_CONV (--`MAP LENGTH [[1;2;3;4];[2;3;4];[3;4]]`--);

FOLDR_CONV APPEND_CONV (--`FOLDR APPEND [] [[1;2;3;4];[2;3;4];[3;4]]`--);
FOLDL_CONV APPEND_CONV (--`FOLDL APPEND [] [[1;2;3;4];[2;3;4];[3;4]]`--);

GENLIST_CONV (BETA_CONV THENC (TOP_DEPTH_CONV num_CONV))
             (--`GENLIST (\n . SUC n) 4`--);

SCANL_CONV APPEND_CONV (--`SCANL APPEND [] [[1;2;3;4];[2;3;4];[3;4]]`--);
SCANR_CONV APPEND_CONV (--`SCANR APPEND [] [[1;2;3;4];[2;3;4];[3;4]]`--);

MAP2_CONV APPEND_CONV
     (--`MAP2 APPEND  [[1;2;3;4];[2;3;4];[3;4]] [[1;2;3;4];[2;3;4];[3;4]]`--);

FILTER_CONV BETA_CONV (--`FILTER (\x. T) [1;2;3;4]`--);
FILTER_CONV BETA_CONV (--`FILTER (\x. F) [1;2;3;4]`--);

ALL_EL_CONV BETA_CONV (--`ALL_EL (\x. F) [1;2;3;4]`--);
ALL_EL_CONV BETA_CONV (--`ALL_EL (\x. T) [1;2;3;4]`--);
ALL_EL_CONV BETA_CONV (--`ALL_EL (\x. T) ([]:num list)`--);
ALL_EL_CONV (BETA_CONV THENC bool_EQ_CONV) (--`ALL_EL (\x. x = F) [T;T;F;F]`--);
ALL_EL_CONV (BETA_CONV THENC bool_EQ_CONV) (--`ALL_EL (\x. x = T) [T;T;F;F]`--);
ALL_EL_CONV (BETA_CONV THENC bool_EQ_CONV) (--`ALL_EL (\x. x = T) [T;T;T]`--);

SOME_EL_CONV BETA_CONV (--`SOME_EL (\x. F) [1;2;3;4]`--);
SOME_EL_CONV BETA_CONV (--`SOME_EL (\x. T) [1;2;3;4]`--);
SOME_EL_CONV BETA_CONV (--`SOME_EL (\x. T) ([]:num list)`--);

IS_EL_CONV bool_EQ_CONV (--`IS_EL T [F;F;F;F]`--);
IS_EL_CONV bool_EQ_CONV (--`IS_EL F [T;T;F;F]`--);
IS_EL_CONV bool_EQ_CONV (--`IS_EL F []`--);

AND_EL_CONV (--`AND_EL []`--);
AND_EL_CONV (--`AND_EL [T]`--);
AND_EL_CONV (--`AND_EL [F]`--);
AND_EL_CONV (--`AND_EL [T;F;T;F]`--);
AND_EL_CONV (--`AND_EL [F;F;F;F]`--);

OR_EL_CONV (--`OR_EL []`--);
OR_EL_CONV (--`OR_EL [T]`--);
OR_EL_CONV (--`OR_EL [F]`--);
OR_EL_CONV (--`OR_EL [T;F;T;F]`--);
OR_EL_CONV (--`OR_EL [F;F;F;F]`--);


(*
NULL_CONV (--`NULL ([]:'a list)`--);
NULL_CONV (--`NULL [T]`--);
NULL_CONV (--`NULL [1;2;3]`--);
NULL_CONV (--`NULL [[1;2;3];[1]]`--);

HD_CONV (--`HD [1]`--);
HD_CONV (--`HD [1;2;3]`--);

TL_CONV (--`TL [1]`--);
TL_CONV (--`TL [1;2;3]`--);
*)


list_EQ_CONV bool_EQ_CONV (--`[] = ([]:bool list)`--);
list_EQ_CONV bool_EQ_CONV (--`[T] = [F]`--);
list_EQ_CONV bool_EQ_CONV (--`[T;F;T;F] = [F;T;F;F]`--);

list_EQ_CONV bool_EQ_CONV (--`[T;F;T;F] = [F]`--); (* FAILS *)
list_EQ_CONV bool_EQ_CONV (--`[T;F;T;F] = [T;F;T]`--); (* FAILS *)
list_EQ_CONV bool_EQ_CONV (--`[T] = []`--); (* FAILS *)
list_EQ_CONV bool_EQ_CONV (--`[] = [T]`--); (* FAILS *)

(*
g `!l. APPEND [1] l = CONS 1 l`;
e SNOC_INDUCT_TAC;
b();
e LIST_INDUCT_TAC;

g `!l1 l2.( LENGTH l1 = LENGTH l2) ==> (APPEND [1] l1 = CONS 1 l2)`;
e EQ_LENGTH_INDUCT_TAC;
b();
e EQ_LENGTH_SNOC_INDUCT_TAC;
*)


(* (KLS) The following is unnecessary, since "define_type" has not been
   changed. But anyway, we'll leave it.

new_theory "temp";

val void_Axiom = define_type{name="void_Axiom" ,
                             type_spec= `void = Void`,
                             fixities = [Prefix]};

val pair = define_type{name="pair",
                       type_spec= `pair = CONST of 'a#'b`,
                       fixities = [Prefix]};

val onetest = define_type{name="onetest",
                          type_spec=`onetest = OOOO of one`,
                          fixities = [Prefix]};

val tri_Axiom =  define_type{name="tri_Axiom",
                            type_spec=`tri = Hi | Lo | Fl`,
                            fixities = [Prefix,Prefix,Prefix]};

val iso_Axiom =  define_type{name="iso_Axiom",
                             type_spec=`iso = ISO of 'a`,
                             fixities = [Prefix]};

val List_Axiom = define_type{name="List_Axiom",
                             type_spec=`List = Nil | CCC of 'a => List`,
                             fixities = [Prefix,Infix 40]};

val ty_Axiom = define_type{name="ty_Axiom",
        type_spec = `ty = C1 of 'a
                        | C2
                        | C3 of 'a => 'b => ty
                        | C4 of ty => 'c => ty => 'a => 'b
                        | C5 of ty => ty`,
        fixities = [Prefix, Prefix, Prefix, Prefix, Prefix]};

define_type{name="bintree",
            type_spec=`bintree = LEAF of 'a
                               | TREE of bintree => bintree`,
            fixities = [Prefix,Prefix]};

define_type{name="seven",
            type_spec= `typ = C of one
                                   => (one#one)
                                   => (one -> one-> 'a list)
                                   => ('a,one#one,'a list) ty`,
            fixities = [Prefix]};

define_type{name="seven'",
            type_spec= `Typ = D of one # (one#one) # (one -> one -> 'a list)
                                   # ('a,one#one,'a list) ty`,
            fixities = [Prefix]};
*)
