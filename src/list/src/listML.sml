structure listML :> listML =
struct

  fun cons h t = h::t
  val null = List.null
  val hd = List.hd
  val tl = List.tl
  fun append l1 l2 = l1 @ l2

  fun flat [] = []
    | flat (h::t) = append h (flat t)
 
  fun length [] = numML.zero
    | length (h::t) = numML.+ numML.one (length t);

  val map = List.map

  fun map2 f [] [] = []
    | map2 f (h1::t1) (h2::t2) = f h1 h2::map2 f t1 t2

  fun mem x [] = false
    | mem x (h::t) = (x=h) orelse mem x t;

  val filter = List.filter
  fun foldr (f:'a->'b->'b) e [] = e
    | foldr f e (x::l) = f x (foldr f e l);

  fun foldl (f:'b->'a->'b) e [] = e
    | foldl f e (x::l) = foldl f (f e x) l;

  val every = List.all
  val exists = List.exists

  fun el n l = if n=numML.zero then hd l else el (numML.pre n) (tl l);

  fun zip ([],[]) = []
    | zip (x1::l1, x2::l2) = (x1,x2)::zip (l1, l2);

  fun unzip [] = ([], [])
    | unzip ((x,y)::l) = let val (l1,l2) = unzip l in (x::l1, y::l2) end

  fun sum [] = numML.zero
    | sum (h::t) = numML.+ h (sum t);

  val reverse = List.rev

  val last = List.last

  fun front (h::t) = if null t then [] else h::front t

  fun all_distinct [] = true
    | all_distinct (h::t) = not (mem h t) andalso all_distinct t


val _ = app ConstMapML.insert
           [(listSyntax.nil_tm,    ("List","nil")),
            (listSyntax.cons_tm,   ("ListML","cons")),
            (listSyntax.null_tm,   ("ListML","null")),
            (listSyntax.hd_tm,     ("ListML","hd")),
            (listSyntax.tl_tm,     ("ListML","tl")),
            (listSyntax.append_tm, ("ListML","append")),
            (listSyntax.flat_tm,   ("ListML","flat")),
            (listSyntax.length_tm, ("ListML","length")),
            (listSyntax.map_tm,    ("ListML","map")),
            (listSyntax.map2_tm,   ("ListML","map2")),
            (listSyntax.mem_tm,    ("ListML","mem")),
            (listSyntax.filter_tm, ("ListML","filter")),
            (listSyntax.foldr_tm,  ("ListML","foldr")),
            (listSyntax.foldl_tm,  ("ListML","foldl")),
            (listSyntax.every_tm,  ("ListML","every")),
            (listSyntax.exists_tm, ("ListML","exists")),
            (listSyntax.el_tm,     ("ListML","el")),
            (listSyntax.zip_tm,    ("ListML","zip")),
            (listSyntax.unzip_tm,  ("ListML","unzip")),
            (listSyntax.sum_tm,    ("ListML","sum")),
            (listSyntax.reverse_tm,("ListML","reverse")),
            (listSyntax.last_tm,   ("ListML","last")),
            (listSyntax.front_tm,  ("ListML","front")),
            (listSyntax.all_distinct_tm, ("ListML","all_distinct"))];
end
