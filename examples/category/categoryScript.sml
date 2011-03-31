open HolKernel bossLib

val _ = new_theory "category"

val _ = Hol_datatype `category =
  <| ob : 'a set ;
     mor : 'b set ;
     dom : 'b -> 'a ;
     cod : 'b -> 'a ;
     id : 'a -> 'b ;
     comp : 'b # 'b -> 'b |>`

val is_category_def = Define`
  is_category c =
    (!f. f IN c.mor ==> c.dom f IN c.ob) /\
    (!f. f IN c.mor ==> c.cod f IN c.ob) /\
    (!a. a IN c.ob ==> c.id a IN c.mor) /\
    (!f g. f IN c.mor /\ g IN c.mor /\ (c.cod f = c.dom g) ==>
           c.comp (g,f) IN c.mor /\
           (c.dom (c.comp (g,f)) = c.dom f) /\
           (c.cod (c.comp (g,f)) = c.cod g)) /\
    (!a f. a IN c.ob /\ f IN c.mor /\ (c.dom f = a) ==> (c.comp (f, c.id a) = f)) /\
    (!a f. a IN c.ob /\ f IN c.mor /\ (c.cod f = a) ==> (c.comp (c.id a, f) = f)) /\
    (!f g h. f IN c.mor /\ g IN c.mor /\ h IN c.mor /\
             (c.cod f = c.dom g) /\ (c.cod g = c.dom h) ==>
             (c.comp (h, (c.comp (g,f))) = c.comp (c.comp (h,g), f)))`

val _ = export_theory ()
