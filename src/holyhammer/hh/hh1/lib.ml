








let fail() = failwith "";;





let curry f x y = f(x,y);;

let uncurry f(x,y) = f x y;;

let iii x = x;;

let kkk x y = x;;

let ccc f x y = f y x;;

let www f x = f x x;;

let o = fun f g x -> f(g x);;

let (f_f) = fun f g (x,y) -> (f x,g y);;





let hd l =
  match l with
   h::t -> h
  | _ -> failwith "hd";;

let tl l =
  match l with
   h::t -> t
  | _ -> failwith "tl";;

let map f =
  let rec mapf l =
    match l with
      [] -> []
    | (x::t) -> let y = f x in y::(mapf t) in
  mapf;;

let rec last l =
  match l with
    [x] -> x
  | (h::t) -> last t
  | [] -> failwith "last";;

let rec butlast l =
  match l with
    [_] -> []
  | (h::t) -> h::(butlast t)
  | [] -> failwith "butlast";;

let rec el n l =
  if n = 0 then hd l else el (n - 1) (tl l);;

let rev =
  let rec rev_append acc l =
    match l with
      [] -> acc
    | h::t -> rev_append (h::acc) t in
  fun l -> rev_append [] l;;

let rec map2 f l1 l2 =
  match (l1,l2) with
    [],[] -> []
  | (h1::t1),(h2::t2) -> let h = f h1 h2 in h::(map2 f t1 t2)
  | _ -> failwith "map2: length mismatch";;





let can f x = try (f x; true) with Failure _ -> false;;

let check p x = if p x then x else failwith "check";;





let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let rec repeat f x =
  try let y = f x in repeat f y with Failure _ -> x;;






exception Unchanged;;





let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec rev_itlist f l b =
  match l with
    [] -> b
  | (h::t) -> rev_itlist f t (f h b);;

let rec end_itlist f l =
  match l with
        []     -> failwith "end_itlist"
      | [x]    -> x
      | (h::t) -> f h (end_itlist f t);;

let rec itlist2 f l1 l2 b =
  match (l1,l2) with
    ([],[]) -> b
  | (h1::t1,h2::t2) -> f h1 h2 (itlist2 f t1 t2 b)
  | _ -> failwith "itlist2";;

let rec rev_itlist2 f l1 l2 b =
   match (l1,l2) with
     ([],[]) -> b
   | (h1::t1,h2::t2) -> rev_itlist2 f t1 t2 (f h1 h2 b)
      | _ -> failwith "rev_itlist2";;





let rec splitlist dest x =
  try let l,r = dest x in
      let ls,res = splitlist dest r in
      (l::ls,res)
  with Failure _ -> ([],x);;

let rev_splitlist dest =
  let rec rsplist ls x =
    try let l,r = dest x in
        rsplist (r::ls) l
    with Failure _ -> (x,ls) in
  fun x -> rsplist [] x;;

let striplist dest =
  let rec strip x acc =
    try let l,r = dest x in
        strip l (strip r acc)
    with Failure _ -> x::acc in
  fun x -> strip x [];;





let rec nsplit dest clist x =
  if clist = [] then [],x else
  let l,r = dest x in
  let ll,y = nsplit dest (tl clist) r in
  l::ll,y;;





let rec replicate x n =
    if n < 1 then []
    else x::(replicate x (n - 1));;

let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);;





let rec forall p l =
  match l with
    [] -> true
  | h::t -> p(h) && forall p t;;

let rec forall2 p l1 l2 =
  match (l1,l2) with
    [],[] -> true
  | (h1::t1,h2::t2) -> p h1 h2 && forall2 p t1 t2
  | _ -> false;;

let rec exists p l =
  match l with
    [] -> false
  | h::t -> p(h) || exists p t;;

let length =
  let rec len k l =
    if l = [] then k else len (k + 1) (tl l) in
  fun l -> len 0 l;;

let rec filter p l =
  match l with
    [] -> l
  | h::t -> let t' = filter p t in
            if p(h) then if t'==t then l else h::t'
            else t';;

let rec partition p l =
  match l with
    [] -> [],l
  | h::t -> let yes,no = partition p t in
            if p(h) then (if yes == t then l,[] else h::yes,no)
            else (if no == t then [],l else yes,h::no);;

let rec mapfilter f l =
  match l with
    [] -> []
  | (h::t) -> let rest = mapfilter f t in
              try (f h)::rest with Failure _ -> rest;;

let rec find p l =
  match l with
      [] -> failwith "find"
    | (h::t) -> if p(h) then h else find p t;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;

let flat l = itlist (@) l [];;

let rec remove p l =
  match l with
    [] -> failwith "remove"
  | (h::t) -> if p(h) then h,t else
              let y,n = remove p t in y,h::n;;

let rec chop_list n l =
  if n = 0 then [],l else
  try let m,l' = chop_list (n-1) (tl l) in (hd l)::m,l'
  with Failure _ -> failwith "chop_list";;

let index x =
  let rec ind n l =
    match l with
      [] -> failwith "index"
    | (h::t) -> if Pervasives.compare x h = 0 then n else ind (n + 1) t in
  ind 0;;





let rec mem x lis =
  match lis with
    [] -> false
  | (h::t) -> Pervasives.compare x h = 0 || mem x t;;

let insert x l =
  if mem x l then l else x::l;;

let union l1 l2 = itlist insert l1 l2;;

let unions l = itlist union l [];;

let intersect l1 l2 = filter (fun x -> mem x l2) l1;;

let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1;;

let subset l1 l2 = forall (fun t -> mem t l2) l1;;

let set_eq l1 l2 = subset l1 l2 && subset l2 l1;;





let rec assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare x a = 0 then y else assoc a t
  | [] -> failwith "find";;

let rec rev_assoc a l =
  match l with
    (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assoc a t
  | [] -> failwith "find";;





let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let rec unzip =
  function [] -> [],[]
         | ((a,b)::rest) -> let alist,blist = unzip rest in
                            (a::alist,b::blist);;





let rec shareout pat all =
  if pat = [] then [] else
  let l,r = chop_list (length (hd pat)) all in
  l::(shareout (tl pat) r);;





let rec do_list f l =
  match l with
    [] -> ()
  | (h::t) -> (f h; do_list f t);;





let rec sort cmp lis =
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;





let uniq l =
  let rec uniq2 acc = function
      x::(y::_ as t) -> uniq2 (if Pervasives.compare x y = 0 then acc else x :: acc) t
    | [x] -> rev (x :: acc)
    | [] -> rev acc
  in uniq2 [] l;;

let setify s = uniq (List.sort Pervasives.compare s);;





let implode l = itlist (^) l "";;

let explode s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.sub s n 1)::l) in
  exap (String.length s - 1) [];;





let gcd =
  let rec gxd x y =
    if y = 0 then x else gxd y (x mod y) in
  fun x y -> let x' = abs x and y' = abs y in
              if x' < y' then gxd y' x' else gxd x' y';;





open Num;;
let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10

let pow2 n = power_num num_2 (Int n);;
let pow10 n = power_num num_10 (Int n);;

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r');;

let numerator x = fst (numdom x)
and denominator x = snd (numdom x);;

let gcd_num n1 n2 =
  num_of_big_int(Big_int.gcd_big_int (big_int_of_num n1) (big_int_of_num n2));;

let lcm_num x y =
  if x =/ num_0 && y =/ num_0 then num_0
  else abs_num((x */ y) // gcd_num x y);;





let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;





let report s =
  Format.print_string s; Format.print_newline();;





let warn cond s =
  if cond then report ("Warning: "^s) else ();;





let verbose = ref true;;
let report_timing = ref true;;





let remark s =
  if !verbose then report s else ();;





let time f x =
  if not (!report_timing) then f x else
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      report("CPU time (user): "^(string_of_float(finish_time -. start_time)));
      result
  with e ->
      let finish_time = Sys.time() in
      Format.print_string("Failed after (user) CPU time of "^
                          (string_of_float(finish_time -. start_time))^": ");
      raise e;;





let rec assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if Pervasives.compare x a = 0 then y else assocd a t d;;

let rec rev_assocd a l d =
  match l with
    [] -> d
  | (x,y)::t -> if Pervasives.compare y a = 0 then x else rev_assocd a t d;;





let rec qmap f l =
  match l with
    h::t -> let h' = f h and t' = qmap f t in
            if h' == h && t' == t then l else h'::t'
  | _ -> l;;





let rec merge ord l1 l2 =
  match l1 with
    [] -> l2
  | h1::t1 -> match l2 with
                [] -> l1
              | h2::t2 -> if ord h1 h2 then h1::(merge ord t1 l2)
                          else h2::(merge ord l1 t2);;

let mergesort ord =
  let rec mergepairs l1 l2 =
    match (l1,l2) with
        ([s],[]) -> s
      | (l,[]) -> mergepairs [] l
      | (l,[s1]) -> mergepairs (s1::l) []
      | (l,(s1::s2::ss)) -> mergepairs ((merge ord s1 s2)::l) ss in
  fun l -> if l = [] then [] else mergepairs [] (map (fun x -> [x]) l);;





let increasing f x y = Pervasives.compare (f x) (f y) < 0;;

let decreasing f x y = Pervasives.compare (f x) (f y) > 0;;










type ('a,'b)func =
   Empty
 | Leaf of int * ('a*'b)list
 | Branch of int * int * ('a,'b)func * ('a,'b)func;;





let undefined = Empty;;





let is_undefined f =
  match f with
    Empty -> true
  | _ -> false;;





let mapf =
  let rec map_list f l =
    match l with
      [] -> []
    | (x,y)::t -> (x,f(y))::(map_list f t) in
  let rec mapf f t =
    match t with
      Empty -> Empty
    | Leaf(h,l) -> Leaf(h,map_list f l)
    | Branch(p,b,l,r) -> Branch(p,b,mapf f l,mapf f r) in
  mapf;;





let foldl =
  let rec foldl_list f a l =
    match l with
      [] -> a
    | (x,y)::t -> foldl_list f (f a x y) t in
  let rec foldl f a t =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldl_list f a l
    | Branch(p,b,l,r) -> foldl f (foldl f a l) r in
  foldl;;

let foldr =
  let rec foldr_list f l a =
    match l with
      [] -> a
    | (x,y)::t -> f x y (foldr_list f t a) in
  let rec foldr f t a =
    match t with
      Empty -> a
    | Leaf(h,l) -> foldr_list f l a
    | Branch(p,b,l,r) -> foldr f l (foldr f r a) in
  foldr;;





let graph f = setify (foldl (fun a x y -> (x,y)::a) [] f);;

let dom f = setify(foldl (fun a x y -> x::a) [] f);;

let ran f = setify(foldl (fun a x y -> y::a) [] f);;





let applyd =
  let rec apply_listd l d x =
    match l with
      (a,b)::t -> let c = Pervasives.compare x a in
                  if c = 0 then b else if c > 0 then apply_listd t d x else d x
    | [] -> d x in
  fun f d x ->
    let k = Hashtbl.hash x in
    let rec look t =
      match t with
        Leaf(h,l) when h = k -> apply_listd l d x
      | Branch(p,b,l,r) when (k lxor p) land (b - 1) = 0
                -> look (if k land b = 0 then l else r)
      | _ -> d x in
    look f;;

let apply f = applyd f (fun x -> failwith "apply");;

let tryapplyd f a d = applyd f (fun x -> d) a;;

let defined f x = try apply f x; true with Failure _ -> false;;





let undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then t
          else if c < 0 then l else
          let t' = undefine_list x t in
          if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Empty
          else Leaf(h,l')
      | Branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else (match l' with Empty -> r | _ -> Branch(p,b,l',r))
          else
            let r' = und r in
            if r' == r then t
            else (match r' with Empty -> l | _ -> Branch(p,b,l,r'))
      | _ -> t in
    und;;





let (|->),combine =
  let newbranch p1 t1 p2 t2 =
    let zp = p1 lxor p2 in
    let b = zp land (-zp) in
    let p = p1 land (b - 1) in
    if p1 land b = 0 then Branch(p,b,t1,t2)
    else Branch(p,b,t2,t1) in
  let rec define_list (x,y as xy) l =
    match l with
      (a,b as ab)::t ->
          let c = Pervasives.compare x a in
          if c = 0 then xy::t
          else if c < 0 then xy::l
          else ab::(define_list xy t)
    | [] -> [xy]
  and combine_list op z l1 l2 =
    match (l1,l2) with
      [],_ -> l2
    | _,[] -> l1
    | ((x1,y1 as xy1)::t1,(x2,y2 as xy2)::t2) ->
          let c = Pervasives.compare x1 x2 in
          if c < 0 then xy1::(combine_list op z t1 l2)
          else if c > 0 then xy2::(combine_list op z l1 t2) else
          let y = op y1 y2 and l = combine_list op z t1 t2 in
          if z(y) then l else (x1,y)::l in
  let (|->) x y =
    let k = Hashtbl.hash x in
    let rec upd t =
      match t with
        Empty -> Leaf (k,[x,y])
      | Leaf(h,l) ->
           if h = k then Leaf(h,define_list (x,y) l)
           else newbranch h t k (Leaf(k,[x,y]))
      | Branch(p,b,l,r) ->
          if k land (b - 1) <> p then newbranch p t k (Leaf(k,[x,y]))
          else if k land b = 0 then Branch(p,b,upd l,r)
          else Branch(p,b,l,upd r) in
    upd in
  let rec combine op z t1 t2 =
    match (t1,t2) with
      Empty,_ -> t2
    | _,Empty -> t1
    | Leaf(h1,l1),Leaf(h2,l2) ->
          if h1 = h2 then
            let l = combine_list op z l1 l2 in
            if l = [] then Empty else Leaf(h1,l)
          else newbranch h1 t1 h2 t2
    | (Leaf(k,lis) as lf),(Branch(p,b,l,r) as br) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z lf l with
                 Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z lf r with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch k lf p br
    | (Branch(p,b,l,r) as br),(Leaf(k,lis) as lf) ->
          if k land (b - 1) = p then
            if k land b = 0 then
              (match combine op z l lf with
                Empty -> r | l' -> Branch(p,b,l',r))
            else
              (match combine op z r lf with
                 Empty -> l | r' -> Branch(p,b,l,r'))
          else
            newbranch p br k lf
    | Branch(p1,b1,l1,r1),Branch(p2,b2,l2,r2) ->
          if b1 < b2 then
            if p2 land (b1 - 1) <> p1 then newbranch p1 t1 p2 t2
            else if p2 land b1 = 0 then
              (match combine op z l1 t2 with
                 Empty -> r1 | l -> Branch(p1,b1,l,r1))
            else
              (match combine op z r1 t2 with
                 Empty -> l1 | r -> Branch(p1,b1,l1,r))
          else if b2 < b1 then
            if p1 land (b2 - 1) <> p2 then newbranch p1 t1 p2 t2
            else if p1 land b2 = 0 then
              (match combine op z t1 l2 with
                 Empty -> r2 | l -> Branch(p2,b2,l,r2))
            else
              (match combine op z t1 r2 with
                 Empty -> l2 | r -> Branch(p2,b2,l2,r))
          else if p1 = p2 then
           (match (combine op z l1 l2,combine op z r1 r2) with
              (Empty,r) -> r | (l,Empty) -> l | (l,r) -> Branch(p1,b1,l,r))
          else
            newbranch p1 t1 p2 t2 in
  (|->),combine;;





let (|=>) = fun x y -> (x |-> y) undefined;;





let rec choose t =
  match t with
    Empty -> failwith "choose: completely undefined function"
  | Leaf(h,l) -> hd l
  | Branch(b,p,t1,t2) -> choose t1;;





let rec mem' eq =
  let rec mem x lis =
    match lis with
      [] -> false
    | (h::t) -> eq x h || mem x t
  in mem;;

let insert' eq x l =
  if mem' eq x l then l else x::l;;

let union' eq l1 l2 = itlist (insert' eq) l1 l2;;

let unions' eq l = itlist (union' eq) l [];;

let subtract' eq l1 l2 = filter (fun x -> not (mem' eq x l2)) l1;;






let num_of_string =
  let values =
   ["0",0; "1",1; "2",2; "3",3; "4",4;
    "5",5; "6",6; "7",7; "8",8; "9",9;
    "a",10; "A",10; "b",11; "B",11;
    "c",12; "C",12; "d",13; "D",13;
    "e",14; "E",14; "f",15; "F",15] in
  let valof b s =
    let v = Int(assoc s values) in
    if v </ b then v else failwith "num_of_string: invalid digit for base"
  and two = num_2 and ten = num_10 and sixteen = Int 16 in
  let rec num_of_stringlist b l =
    match l with
      [] -> failwith "num_of_string: no digits after base indicator"
    | [h] -> valof b h
    | h::t -> valof b h +/ b */ num_of_stringlist b t in
  fun s ->
    match explode(s) with
        [] -> failwith "num_of_string: no digits"
      | "0"::"x"::hexdigits -> num_of_stringlist sixteen (rev hexdigits)
      | "0"::"b"::bindigits -> num_of_stringlist two (rev bindigits)
      | decdigits -> num_of_stringlist ten (rev decdigits);;





let strings_of_file filename =
  let fd = try Pervasives.open_in filename
           with Sys_error _ ->
             failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    try let l = Pervasives.input_line fd in
        suck_lines (l::acc)
    with End_of_file -> rev acc in
  let data = suck_lines [] in
  (Pervasives.close_in fd; data);;

let string_of_file filename =
  end_itlist (fun s t -> s^"\n"^t) (strings_of_file filename);;

let file_of_string filename s =
  let fd = Pervasives.open_out filename in
  output_string fd s; close_out fd;;

(* Tail-recursive *)
let uniq2 l =
  let rec uniq2 acc = function
      x::(y::_ as t) -> uniq2 (if Pervasives.compare x y = 0 then acc else x :: acc) t
    | [x] -> List.rev (x :: acc)
    | [] -> List.rev acc
  in uniq2 [] l;;
let setify2 l = uniq2 (List.sort compare l);;
