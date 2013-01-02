(* HOL-Omega Appetizers, as described in the HOL-Omega TUTORIAL TEASER. *)

structure appetizersScript =
struct

open HolKernel Parse boolLib bossLib

val _ = new_theory "appetizers";

local open (*combinTheory pred_setLib*) bagLib in end;

val _ = set_trace "Unicode" 0;
val _ = set_trace "types" 1;

val _ = Hol_datatype `collection_ops1 =
     <| empty  : 'x 'col;
        insert : 'x -> 'x 'col -> 'x 'col;
        length : 'x 'col -> num |>`;

(* List operations *)

val list_ops = Define
     `list_ops = <|empty := []:'a list; insert := CONS; length := LENGTH|>`;

val list_ops_ty = type_of ``list_ops``;

(* Set operations *)

val set_ops = Define
     `set_ops = <|empty := {}:'a set; insert := $INSERT; length := CARD|>`;

val set_ops_ty = type_of ``set_ops``;

(* Bag operations *)

val bag_ops = Define
     `bag_ops = <| empty := {||}:'a bag; insert := BAG_INSERT;
                   length := BAG_CARD|>`;

val bag_ops_ty = type_of ``bag_ops``;

(* Object-oriented collections *)

val _ = Hol_datatype `collection =
     <| this : 'x 'col;
        ops  : ('col,'x) collection_ops1 |>`;

val insert_def = Define
   `insert x (c:('col,'x)collection) =
             <| this := c.ops.insert x c.this;
                ops  := c.ops |>`;

val length_def = Define
   `length (c:('col,'x)collection) = c.ops.length c.this`;

(* Adding a fold operation *)

val _ = Hol_datatype `collection_ops2 =
     <| empty  : 'x 'col;
        insert : 'x -> 'x 'col -> 'x 'col;
        length : 'x 'col -> num;
        fold   : !'y. ('x -> 'y -> 'y) -> 'y -> 'x 'col -> 'y |>`;

val list_ops = Define
   `list_ops = <| empty := []:'a list; insert := CONS; length := LENGTH;
                  fold := \:'b. FOLDR|>`;

val list_ops_ty = type_of ``list_ops``;

val _ = Hol_datatype `collection =
     <| this : 'x 'col;
        ops  : ('col,'x) collection_ops2 |>`;

val fold_def = Define
   `fold f (e:'b) (c:('col,'a)collection) = c.ops.fold f e c.this`;

val ex1 = ``<| this := [2;3;5;7]; ops := list_ops |>``;

val ex1a = ``fold (\x y. x+y) 0 ^ex1``;

val ex1b = ``fold (\x y. EVEN x /\ y) T ^ex1``;

(* Adding a map operation *)

val _ = Hol_datatype `collection_ops3 =
     <| length : 'x 'col -> num;
        empty  : 'x 'col;
        insert : 'x -> 'x 'col -> 'x 'col;
        fold   : !'y. ('x -> 'y -> 'y) -> 'y -> 'x 'col -> 'y;
        map    : !'y. ('x -> 'y) -> 'x 'col -> 'y 'col |>`;

val list_ops = Define
   `list_ops = \:'a.
                 <|empty := []:'a list; insert := CONS; length := LENGTH;
                   fold := \:'b. FOLDR; map := \:'b. MAP |>`;

val list_ops_ty = type_of ``list_ops``;

val set_ops = Define
   `set_ops = \:'a.
                <|empty := {}:'a set; insert := $INSERT; length := CARD;
                  fold := \:'b. \f e s. ITSET f s e; map := \:'b. IMAGE |>`;

val set_ops_ty = type_of ``set_ops``;

val bag_ops = Define
   `bag_ops = \:'a.
                <|empty := {||}:'a bag; insert := BAG_INSERT; length := BAG_CARD;
                  fold := \:'b. \f e b. ITBAG f b e; map := \:'b. BAG_IMAGE |>`;

val bag_ops_ty = type_of ``bag_ops``;

val _ = Hol_datatype `collection =
     <| this : 'x 'col;
        ops  : !'x. ('col,'x) collection_ops3 |>`;

val insert_def = Define
   `insert x (c:('col,'x)collection) =
             <| this := c.ops.insert x c.this;
                ops  := c.ops |>`;

val length_def = Define
   `length (c:('col,'x)collection) = c.ops.length c.this`;

val fold_def = Define
   `fold f (e:'b) (c:('col,'a)collection) = c.ops.fold f e c.this`;

val map_def = Define
   `map (f:'a -> 'b) c =
            <| this := c.ops.map f c.this;
               ops  := c.ops |> `;

val union_def =
  Define `union (c1: ('col1,'a)collection) (c2: ('col2,'a)collection) =
            <| this := fold c2.ops.insert c2.this c1 : 'a 'col2;
               ops  := c2.ops |>`;

val ex1 = ``<| this := [2;3;5;7]; ops := list_ops |>``;

val ex2 = ``<| this := {2;3;5;7}; ops := set_ops |>``;

val ex3 = ``<| this := {|2;3;5;7|}; ops := bag_ops |>``;


(* Abstract collections *)

(* Existential types *)

val ety = ``:?'col. ('col, 'a) collection``;

(* Packages containing lists *)

val list_pack = ``pack (:list, <|this := [2;3;2]; ops := list_ops|>)``;

val list_pack_ty = type_of list_pack;

val list_pack2 =
    ``pack (:list, <| this := [[2];[3;5];[7]]; ops := list_ops |> )``;

val list_pack2_ty = type_of list_pack2;

val list_pack3 =
    ``pack (:list, <| this := [[2];[3;5];[7]]; ops := list_ops |> )
        : ?'x. ('x,num list) collection``;

val list_pack3_ty = type_of list_pack3;

(* Packages containing sets *)

val set_pack =
    ``pack (:\'a.'a set, <| this := {2;3;2}; ops := set_ops |> )``;

val set_pack_ty = type_of set_pack;

(* Packages containing bags *)

val bag_pack =
    ``pack (:\'a.'a bag, <| this := {|2;3;2|}; ops := bag_ops |> )``;

val bag_pack_ty = type_of bag_pack;

val packs_have_same_type =         eq_ty list_pack_ty set_pack_ty
                           andalso eq_ty  set_pack_ty bag_pack_ty;

val lengthp_def =
  Define `lengthp (p: ?'col. ('col,'a)collection) =
            let (:'col, c) = p in
              c.ops.length c.this `;

(* The following raises a type checking exception:

val this_def =
  Define `this (p: ?'col. ('col,'a)collection) =
            let (:'col, c) = p in
              c.this `;

*)

val insertp_def =
  Define `insertp (e:'a) (p: ?'col. ('col,'a)collection) =
            let (:'col, c) = p in
              pack (:'col,
                    <| this := c.ops.insert e c.this : 'a 'col;
                       ops  := c.ops |>) `;

val foldp_def =
  Define `foldp (f:'a -> 'b -> 'b) (e:'b) (p: ?'col. ('col,'a)collection) =
            let (:'col, c) = p in
              fold f e c `;

val mapp_def =
  Define `mapp (f:'a -> 'b) (p: ?'col. ('col,'a)collection) =
            let (:'col, c) = p in
              pack (:'col, map f c) `;

val unionp_def =
  Define `unionp (p1: ?'col. ('col,'a)collection)
                 (p2: ?'col. ('col,'a)collection) =
            let (:'col1, c1) = p1 in
            let (:'col2, c2) = p2 in
                pack (:'col2, union c1 c2) `;


val _ = set_trace "types" 1;
val _ = set_trace "kinds" 0;
val _ = html_theory "appetizers";

val _ = export_theory();

end; (* structure appetizersScript *)
