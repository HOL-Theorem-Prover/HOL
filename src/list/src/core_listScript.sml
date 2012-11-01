open HolKernel Parse boolLib

open BasicProvers Datatype

val _ = new_theory "core_list"

val _ = Hol_datatype `list = NIL | CONS of 'a => list`;

(* Concrete syntax *)
val _ = add_listform {separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "["], rightdelim = [TOK "]"],
                      cons = "CONS", nilstr = "NIL",
                      block_info = (PP.INCONSISTENT, 0)};

val _ = add_rule {term_name = "CONS", fixity = Infixr 490,
                  pp_elements = [TOK "::", BreakSpace(0,2)],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 2))};

val list_Axiom = TypeBase.axiom_of ``:'a list``;

val NULL_DEF = new_recursive_definition
      {name = "NULL_DEF",
       rec_axiom = list_Axiom,
       def = --`(NULL []     = T) /\
                (NULL (h::t) = F)`--};
val _ = export_rewrites ["NULL_DEF"]

val HD = new_recursive_definition
      {name = "HD",
       rec_axiom = list_Axiom,
       def = --`HD (h::t) = h`--};
val _ = export_rewrites ["HD"]

val TL = new_recursive_definition
      {name = "TL",
       rec_axiom = list_Axiom,
       def = --`TL (h::t) = t`--};
val _ = export_rewrites ["TL"]

val SUM = new_recursive_definition
      {name = "SUM",
       rec_axiom =  list_Axiom,
       def = --`(SUM [] = 0) /\
          (!h t. SUM (h::t) = h + SUM t)`--};
val _ = export_rewrites ["SUM"]

val APPEND = new_recursive_definition
      {name = "APPEND",
       rec_axiom = list_Axiom,
       def = --`(!l:'a list. APPEND [] l = l) /\
                  (!l1 l2 h. APPEND (h::l1) l2 = h::APPEND l1 l2)`--};
val _ = export_rewrites ["APPEND"]

val _ = set_fixity "++" (Infixl 480);
val _ = overload_on ("++", Term`APPEND`);

val FLAT = new_recursive_definition
      {name = "FLAT",
       rec_axiom = list_Axiom,
       def = --`(FLAT []     = []) /\
          (!h t. FLAT (h::t) = APPEND h (FLAT t))`--};
val _ = export_rewrites ["FLAT"]

val LENGTH = new_recursive_definition
      {name = "LENGTH",
       rec_axiom = list_Axiom,
       def = --`(LENGTH []     = 0) /\
     (!(h:'a) t. LENGTH (h::t) = SUC (LENGTH t))`--};
val _ = export_rewrites ["LENGTH"]

val MAP = new_recursive_definition
      {name = "MAP",
       rec_axiom = list_Axiom,
       def = --`(!f:'a->'b. MAP f [] = []) /\
                   (!f h t. MAP f (h::t) = f h::MAP f t)`--};
val _ = export_rewrites ["MAP"]

val LIST_TO_SET_DEF = new_recursive_definition{
  name = "LIST_TO_SET_DEF",
  rec_axiom = list_Axiom,
  def = ``(!x:'a. LIST_TO_SET [] x <=> F) /\
          (!h:'a t x. LIST_TO_SET (h::t) x = (x = h) \/ LIST_TO_SET t x)``}
val _ = overload_on ("set", ``LIST_TO_SET``)
val _ = overload_on ("MEM", ``\h:'a l:'a list. h IN LIST_TO_SET l``)
val _ = export_rewrites ["LIST_TO_SET_DEF"]

val FILTER = new_recursive_definition
      {name = "FILTER",
       rec_axiom = list_Axiom,
       def = --`(!P. FILTER P [] = []) /\
             (!(P:'a->bool) h t.
                    FILTER P (h::t) =
                         if P h then (h::FILTER P t) else FILTER P t)`--};
val _ = export_rewrites ["FILTER"]

val FOLDR = new_recursive_definition
      {name = "FOLDR",
       rec_axiom = list_Axiom,
       def = --`(!f e. FOLDR (f:'a->'b->'b) e [] = e) /\
            (!f e x l. FOLDR f e (x::l) = f x (FOLDR f e l))`--};
val _ = export_rewrites ["FOLDR"]

val FOLDL = new_recursive_definition
      {name = "FOLDL",
       rec_axiom = list_Axiom,
       def = --`(!f e. FOLDL (f:'b->'a->'b) e [] = e) /\
            (!f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l)`--};
val _ = export_rewrites ["FOLDL"]

val EVERY_DEF = new_recursive_definition
      {name = "EVERY_DEF",
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. EVERY P [] = T)  /\
                (!P h t. EVERY P (h::t) = P h /\ EVERY P t)`--};
val _ = export_rewrites ["EVERY_DEF"]

val EXISTS_DEF = new_recursive_definition
      {name = "EXISTS_DEF",
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. EXISTS P [] = F)
            /\  (!P h t.      EXISTS P (h::t) = P h \/ EXISTS P t)`--};
val _ = export_rewrites ["EXISTS_DEF"]

val EL = new_recursive_definition
      {name = "EL",
       rec_axiom = prim_recTheory.num_Axiom,
       def = --`(!l. EL 0 l = (HD l:'a)) /\
                (!l:'a list. !n. EL (SUC n) l = EL n (TL l))`--};
val _ = export_rewrites ["EL"]

val _ = computeLib.add_persistent_funs [
      "APPEND",
      "EXISTS_DEF",
      "EVERY_DEF",
      "FILTER",
      "FLAT",
      "FOLDL",
      "FOLDR",
      "HD",
      "LENGTH",
      "MAP",
      "NULL_DEF",
      "TL"
    ]

val _ = export_theory()
