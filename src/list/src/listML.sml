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
           [(listSyntax.nil_tm,    ("","[]")),
            (listSyntax.cons_tm,   ("","::")),
            (listSyntax.null_tm,   ("listML","null")),
            (listSyntax.hd_tm,     ("listML","hd")),
            (listSyntax.tl_tm,     ("listML","tl")),
            (listSyntax.append_tm, ("listML","append")),
            (listSyntax.flat_tm,   ("listML","flat")),
            (listSyntax.length_tm, ("listML","length")),
            (listSyntax.map_tm,    ("listML","map")),
            (listSyntax.map2_tm,   ("listML","map2")),
            (listSyntax.mem_tm,    ("listML","mem")),
            (listSyntax.filter_tm, ("listML","filter")),
            (listSyntax.foldr_tm,  ("listML","foldr")),
            (listSyntax.foldl_tm,  ("listML","foldl")),
            (listSyntax.every_tm,  ("listML","every")),
            (listSyntax.exists_tm, ("listML","exists")),
            (listSyntax.el_tm,     ("listML","el")),
            (listSyntax.zip_tm,    ("listML","zip")),
            (listSyntax.unzip_tm,  ("listML","unzip")),
            (listSyntax.sum_tm,    ("listML","sum")),
            (listSyntax.reverse_tm,("listML","reverse")),
            (listSyntax.last_tm,   ("listML","last")),
            (listSyntax.front_tm,  ("listML","front")),
            (listSyntax.all_distinct_tm, ("listML","all_distinct"))];
end
