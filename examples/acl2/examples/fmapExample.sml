(*****************************************************************************)
(* Test script for encoding using finite maps.                               *)
(*****************************************************************************)

load "acl2encodeLib";
load "fmap_encodeTheory";

val fmap = ``:'a |-> 'b``;
val sexp = ``:sexp``;

quietdec := true;
open listTheory;
quietdec := false;

val _ = polytypicLib.add_translation sexp fmap handle e => Raise e;

val _ = polytypicLib.add_coding_theorem sexp fmap "encode_decode_map"
 	fmap_encodeTheory.ENCDECMAP_FMAP;
val _ = polytypicLib.add_coding_theorem sexp fmap "encode_detect_all"
    	fmap_encodeTheory.ENCDETALL_FMAP;
val _ = polytypicLib.add_coding_theorem sexp fmap "decode_encode_fix"
        fmap_encodeTheory.DECENCFIX_FMAP;

val _ = polytypicLib.add_coding_theorem sexp fmap "fix_id"
        fmap_encodeTheory.FIXID_FMAP;

val _ = polytypicLib.add_source_theorem fmap "all_id"
        fmap_encodeTheory.ALLID_FMAP;

val _ = polytypicLib.add_source_theorem fmap "map_id"
        fmap_encodeTheory.MAPID_FMAP;

val _ = polytypicLib.add_coding_theorem sexp fmap "detect_dead"
        fmap_encodeTheory.DETECTDEAD_FMAP;
val _ = polytypicLib.add_coding_theorem sexp fmap "general_detect"
        fmap_encodeTheory.DETECT_GENERAL_FMAP

val _ = polytypicLib.add_source_function fmap "map"
        {const = ``map_fmap``, definition = fmap_encodeTheory.map_fmap_def, induction = NONE};

val _ = polytypicLib.add_source_function fmap "all"
        {const = ``all_fmap``, definition = fmap_encodeTheory.all_fmap_def, induction = NONE};

val _ = polytypicLib.add_coding_function sexp fmap "encode"
        {const = ``encode_fmap``, definition = fmap_encodeTheory.encode_fmap_def, induction = NONE};

val _ = polytypicLib.add_coding_function sexp fmap "decode"
        {const = ``decode_fmap``, definition = fmap_encodeTheory.decode_fmap_def, induction = NONE};

val _ = polytypicLib.add_coding_function sexp fmap "detect"
        {const = ``detect_fmap``, definition = fmap_encodeTheory.detect_fmap_def, induction = NONE};

val _ = polytypicLib.add_coding_function sexp fmap "fix"
        {const = ``fix_fmap``, definition = fmap_encodeTheory.fix_fmap_def, induction = NONE};

val _ = encodeLib.set_bottom_value fmap ``nil``;

val _ = functionEncodeLib.add_standard_rewrite 1 "sorted_car" fmap_encodeTheory.sorted_car_rewrite;
val _ = functionEncodeLib.add_standard_rewrite 0 "fdom" fmap_encodeTheory.fdom_rewrite;
val _ = functionEncodeLib.add_standard_rewrite 0 "fapply" fmap_encodeTheory.apply_rewrite;

fun add_fmap_coding_theorem s t = 
let val (_,[from,to]) = dest_type t
    val cc = polytypicLib.get_coding_theorem_conclusion ``:sexp`` s t
    val t1 = polytypicLib.get_coding_theorem ``:sexp`` ``:'a |-> 'b`` s
    val t2 = PART_MATCH (lhs o rand) (SPEC_ALL t1) (lhs cc)
    val tm = (rand (rator (concl t2)))
    val tt = fst (dom_rng (type_of (rand tm)))
    val t3 = METIS_PROVE [fmap_encodeTheory.ONE_ONE_RING, fmap_encodeTheory.ONE_ONE_I,
                          polytypicLib.generate_source_theorem "map_id" tt,
                          polytypicLib.generate_coding_theorem ``:sexp`` "encode_decode_map" tt] tm
    val t4 = MATCH_MP t2 t3
in  polytypicLib.add_coding_theorem_precise sexp t s (
         METIS_PROVE [polytypicLib.generate_coding_theorem ``:sexp`` s from,
                 polytypicLib.generate_coding_theorem ``:sexp`` s to, t4] cc)
end;

fun initialise_fmap_type t = 
let val (_,[from,to]) = dest_type t
    val _ = acl2encodeLib.initialise_type (polytypicLib.base_type from) handle ExistsAlready => ()
    val _ = acl2encodeLib.initialise_type (polytypicLib.base_type to) handle ExistsAlready => ()
    val _ = add_fmap_coding_theorem "encode_detect_all" t
    val _ = add_fmap_coding_theorem "encode_decode_map" t
    val _ = add_fmap_coding_theorem "decode_encode_fix" t
in  ()
end;

val _ = initialise_fmap_type ``:int |-> int``;
val _ = initialise_fmap_type ``:num option |-> int list``;

val tf_def = Define `tf (x : int |-> int) = if 0 IN FDOM x then x ' 0 else 0`;

val oneone_int = prove(``ONE_ONE int``,METIS_TAC [translateTheory.ENCDECMAP_INT, fmap_encodeTheory.ENCDECMAP_FMAP, fmap_encodeTheory.ONE_ONE_I, 
                         fmap_encodeTheory.ONE_ONE_RING, translateTheory.ENCDECMAP_INT]);

val _ = acl2encodeLib.translate_conditional_function [(``tf``, "test_tf")] [oneone_int] tf_def handle e => acl2encodeLib.Raise e;