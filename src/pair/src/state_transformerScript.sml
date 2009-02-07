open HolKernel Parse boolLib pairTheory pairSyntax combinTheory ;

val _ = new_theory "state_transformer";

infixr 0 ||
infix 1 >>;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;
val Suff = Q_TAC SUFF_TAC;
val Know = Q_TAC KNOW_TAC;
val FUN_EQ_TAC = CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV);

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val UNIT_DEF = new_definition ("UNIT_DEF",
  ``UNIT (x:'b) = \(s:'a). (x, s)``);

val BIND_DEF = new_definition ("BIND_DEF",
  ``BIND (g:'a -> 'b # 'a) (f:'b -> 'a -> 'c # 'a) = UNCURRY f o g``);

val IGNORE_BIND_DEF = new_definition("IGNORE_BIND_DEF",
  ``IGNORE_BIND f g = BIND f (\x. g)``);

val MMAP_DEF = new_definition ("MMAP_DEF",
  ``MMAP (f:'c->'b) (m:'a->'c#'a) = BIND m (UNIT o f)``);

val JOIN_DEF = new_definition ("JOIN_DEF",
  ``JOIN (z:'a->('a->'b#'a)#'a) = BIND z I``);

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val BIND_LEFT_UNIT = store_thm
  ("BIND_LEFT_UNIT",
   ``!(k:'a->'b->'c#'b) x. BIND (UNIT x) k = k x``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [BIND_DEF, UNIT_DEF, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [UNCURRY_DEF]);

val UNIT_UNCURRY = store_thm
  ("UNIT_UNCURRY",
   ``!(s:'a#'b). UNCURRY UNIT s = s``,
   REWRITE_TAC [UNCURRY_VAR, UNIT_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [PAIR]);

val BIND_RIGHT_UNIT = store_thm
  ("BIND_RIGHT_UNIT",
   ``!(k:'a->'b#'a). BIND k UNIT = k``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [BIND_DEF, UNIT_UNCURRY, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val BIND_ASSOC = store_thm
  ("BIND_ASSOC",
   ``!(k:'a->'b#'a) (m:'b->'a->'c#'a) (n:'c->'a->'d#'a).
       BIND k (\a. BIND (m a) n) = BIND (BIND k m) n``,
   REWRITE_TAC [BIND_DEF, UNCURRY_VAR, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val MMAP_ID = store_thm
  ("MMAP_ID",
   ``MMAP I = (I:('a->'b#'a)->('a->'b#'a))``,
   MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, I_THM, o_DEF]
   ++ CONV_TAC (DEPTH_CONV ETA_CONV)
   ++ REWRITE_TAC [BIND_RIGHT_UNIT]);

val MMAP_COMP = store_thm
  ("MMAP_COMP",
   ``!f g. (MMAP (f o g):('a->'b#'a)->('a->'d#'a))
           = (MMAP f:('a->'c#'a)->('a->'d#'a)) o MMAP g``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, o_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ Suff `(\x. UNIT (f (g x)))
                  = (\a. BIND ((\x. UNIT (g x)) a) (\x. UNIT (f x)))`
      >> (STRIP_TAC ++ ASM_REWRITE_TAC [])
   ++ MATCH_MP_TAC EQ_EXT
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [BIND_LEFT_UNIT]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val MMAP_UNIT = store_thm
  ("MMAP_UNIT",
   ``!(f:'b->'c). MMAP f o UNIT = (UNIT:'c->'a->'c#'a) o f``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, o_DEF, BIND_LEFT_UNIT]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val MMAP_JOIN = store_thm
  ("MMAP_JOIN",
   ``!f. MMAP f o JOIN = JOIN o MMAP (MMAP f:('a->'b#'a)->('a->'c#'a))``,
   REPEAT STRIP_TAC
   ++ MATCH_MP_TAC EQ_EXT
   ++ REWRITE_TAC [MMAP_DEF, o_DEF, JOIN_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [GSYM BIND_ASSOC, I_THM]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]);

val JOIN_UNIT = store_thm
  ("JOIN_UNIT",
   ``JOIN o UNIT = (I:('a->'b#'a)->('a->'b#'a))``,
   REWRITE_TAC [JOIN_DEF, o_DEF, BIND_LEFT_UNIT, I_DEF, S_DEF, K_DEF]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC []);

val JOIN_MMAP_UNIT = store_thm
  ("JOIN_MMAP_UNIT",
   ``JOIN o MMAP UNIT = (I:('a->'b#'a)->('a->'b#'a))``,
   REWRITE_TAC [JOIN_DEF, o_DEF, MMAP_DEF]
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ CONV_TAC (DEPTH_CONV BETA_CONV)
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]
   ++ MATCH_MP_TAC EQ_EXT
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [BIND_RIGHT_UNIT, I_THM]);

val JOIN_MAP_JOIN = store_thm
  ("JOIN_MAP_JOIN",
   ``JOIN o MMAP JOIN = ((JOIN o JOIN)
       :('a -> ('a -> ('a -> 'b # 'a) # 'a) # 'a) -> 'a -> 'b # 'a)``,
   REWRITE_TAC [JOIN_DEF, o_DEF, MMAP_DEF]
   ++ MATCH_MP_TAC EQ_EXT
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]);

val JOIN_MAP = store_thm
  ("JOIN_MAP",
   ``!k (m:'b->'a->'c#'a). BIND k m = JOIN (MMAP m k)``,
   REWRITE_TAC [JOIN_DEF, o_DEF, MMAP_DEF]
   ++ REWRITE_TAC [GSYM BIND_ASSOC]
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC [BIND_LEFT_UNIT, I_THM]
   ++ CONV_TAC (DEPTH_CONV (ETA_CONV ORELSEC BETA_CONV))
   ++ REWRITE_TAC []);

val FST_o_UNIT = store_thm
  ("FST_o_UNIT",
   ``!x. FST o UNIT x = K x``,
   FUN_EQ_TAC
   ++ REWRITE_TAC [o_THM, UNIT_DEF, K_THM]
   ++ BETA_TAC
   ++ REWRITE_TAC [FST]);

val SND_o_UNIT = store_thm
  ("SND_o_UNIT",
   ``!x. SND o UNIT x = I``,
   FUN_EQ_TAC
   ++ REWRITE_TAC [o_THM, UNIT_DEF, I_THM]
   ++ BETA_TAC
   ++ REWRITE_TAC [SND]);

val FST_o_MMAP = store_thm
  ("FST_o_MMAP",
   ``!f g. FST o MMAP f g = f o FST o g``,
   FUN_EQ_TAC
   ++ REWRITE_TAC [MMAP_DEF, BIND_DEF, UNCURRY, o_THM, UNIT_DEF]
   ++ BETA_TAC
   ++ REWRITE_TAC [FST]);

val _ = export_theory ();
