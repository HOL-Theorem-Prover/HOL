structure Regexp_Match :> Regexp_Match =
struct

open Lib Feedback Regexp_Type;

val ERR = mk_HOL_ERR "Regexp_Match";

type regexp = Regexp_Type.regexp;

fun regexp_compare r1 r2 = Regexp_Type.regexp_compare(r1,r2);

fun regexp_leq r s =
  case regexp_compare r s
   of LESS => true
    | EQUAL => true
    | GREATER => false
;

(*---------------------------------------------------------------------------*)
(* Taken from cakeML version, itself derived from the HOL model              *)
(*---------------------------------------------------------------------------*)

val the = Option.valOf;

fun inv_image rel f x y = rel (f x) (f y);

fun el n list = if n = 0 then hd list else el (n-1) (tl list);

fun upto b t = if b <= t then b::upto (b+1) t else [];;

fun genlist f n = if n<0 then [] else map f (upto 0 (n-1));

fun drop n l = if n<=0 then l else drop (n-1) (tl l);

(*---------------------------------------------------------------------------*)
(* merge sort                                                                *)
(*---------------------------------------------------------------------------*)

local
fun merge rel l1 l2 =
 case (l1,l2)
  of ([],[]) => []
   | ([],_) => l2
   | (_,[]) => l1
   | (x::t1,y::t2) =>
       if rel x y then
          x::merge rel t1 l2 else
          y::merge rel l1 t2;

fun sort2 rel x y = if rel x y then [x, y] else [y, x];

fun sort3 rel x y z =
 if rel x y then
     if rel y z then [x, y, z]
     else if rel x z then [x, z, y]
     else [z, x, y]
 else if rel y z then if rel x z then [y, x, z] else [y, z, x]
      else [z, y, x];

fun mergesortN rel n l =
 if n = 0 then [] else
 if n = 1 then (if null l then [] else [hd l]) else
 if n = 2
   then (case l
          of (x::y::t) => sort2 rel x y
           | other => other) else
 if n = 3
   then (case l
          of (x::y::z::t) => sort3 rel x y z
           | [x,y] => sort2 rel x y
           | other => other)
 else
 let val len1 = n div 2
 in merge rel (mergesortN rel len1 l)
              (mergesortN rel (n - len1) (drop len1 l))
 end;

in
  fun mergesort rel l = mergesortN rel (length l) l
end

(*---------------------------------------------------------------------------*)
(* Finite maps, from examples/balanced_mapTheory.                            *)
(*---------------------------------------------------------------------------*)

structure Finite_Map =
struct

datatype ('k,'v) balanced_map
  = Tip
  | Bin of int * 'k * 'v * ('k,'v)balanced_map * ('k,'v) balanced_map;

val ratio = 2;
val delta  = 3;

val empty = Tip;

fun singleton k x = Bin(1,k,x,Tip,Tip);

fun size fmap =
 case fmap
  of Tip => 0
   | Bin (s,k,v,l,r) => s;

fun member cmp k fmap =
 case fmap
  of Tip => false
   | Bin (s,k', v, l, r) =>
     case cmp k k'
      of LESS => member cmp k l
       | GREATER => member cmp k r
       | EQUAL => true;

fun lookup cmp k fmap =
 case fmap
  of Tip => NONE
   | Bin(s, k', v, l, r) =>
      case cmp k k'
       of LESS => lookup cmp k l
        | GREATER => lookup cmp k r
        | EQUAL => SOME v;

fun foldrWithKey f z fmap =
 case fmap
  of Tip => z
   | Bin(u, kx, x, l, r) =>
        foldrWithKey f (f kx x (foldrWithKey f z r)) l;

fun balanceL k x fmap1 fmap2 =
 case (fmap1,fmap2)
  of (Tip,Tip)
      => Bin (1, k, x, Tip, Tip)
   | (Bin (s', k', v', Tip, Tip), Tip)
      => Bin (2, k, x, Bin (s', k', v', Tip, Tip), Tip)
   | (Bin (u1, lk, lx, Tip, Bin(u2, lrk, lrx, u3, u4)), Tip)
      => Bin(3, lrk, lrx, Bin(1, lk, lx, Tip, Tip), Bin(1,k, x, Tip, Tip))
   | (Bin(u5, lk, lx, Bin (s', k', v', l', r'), Tip), Tip)
      => Bin(3, lk, lx, Bin(s', k', v', l', r'), Bin(1, k, x, Tip, Tip))
   | (Bin(ls, lk, lx, Bin(lls, k', v', l', r'), Bin(lrs, lrk, lrx, lrl, lrr)), Tip)
      => if lrs < ratio*lls
          then
            Bin (1+ls, lk, lx, Bin(lls, k', v', l', r'),
                 Bin (1+lrs, k, x, Bin (lrs, lrk, lrx, lrl, lrr), Tip))
          else
            Bin (1+ls, lrk, lrx,
                 Bin (1+lls+size lrl, lk, lx, Bin(lls, k', v', l', r'), lrl),
                 Bin (1+size lrr, k, x, lrr, Tip))
   | (Tip, Bin(rs, k', v', l', r'))
      => Bin (1+rs, k, x, Tip, Bin(rs, k', v', l', r'))
   | (Bin(ls, lk, lx, ll, lr), Bin(rs, k', v', l', r'))
      => if ls > delta*rs
          then (case (ll, lr)
                 of (Bin (lls, u6, u7, u8, u9), Bin(lrs, lrk, lrx, lrl, lrr))
                    => if lrs < ratio*lls then
                        Bin (1+ls+rs, lk, lx, ll,
                             Bin (1+rs+lrs, k, x, lr, Bin(rs, k', v', l', r')))
                      else
                        Bin (1+ls+rs, lrk, lrx,
                             Bin (1+lls+size lrl, lk, lx, ll, lrl),
                             Bin (1+rs+size lrr, k, x, lrr, Bin (rs, k', v', l', r')))
                  | (u10, u11) => Tip (* error "Failure in Data.Map.balanceL" *)
               )
         else
            Bin (1+ls+rs, k, x, Bin (ls, lk, lx, ll, lr), Bin(rs, k', v', l', r'));

fun balanceR k x fmap1 fmap2 =
 case (fmap1,fmap2)
  of (Tip,Tip)
      => Bin(1, k, x, Tip, Tip)
   | (Tip, Bin(s', k', v', Tip, Tip))
     => Bin(2, k, x, Tip, Bin(s', k', v', Tip, Tip))
   | (Tip,Bin(u1, rk, rx, Tip, Bin(s', k', v', l', r')))
     => Bin(3, rk, rx, Bin(1, k, x, Tip, Tip), Bin(s', k', v', l', r'))
   | (Tip, Bin(u2, rk, rx, Bin(u3, rlk, rlx, u4, u5), Tip))
      => Bin(3, rlk, rlx,
             Bin(1, k, x, Tip, Tip),
             Bin(1, rk, rx, Tip, Tip))
   | (Tip, Bin(rs, rk, rx, Bin(rls, rlk, rlx, rll, rlr),
                           Bin(rrs, k', v', l', r')))
     => if rls < ratio*rrs
        then
          Bin (1+rs, rk, rx,
               Bin (1+rls,k, x, Tip, Bin(rls, rlk, rlx, rll, rlr)),
               Bin(rrs, k', v', l', r'))
        else
          Bin (1+rs, rlk, rlx,
               Bin (1+size rll, k, x, Tip, rll),
               Bin (1+rrs+size rlr, rk, rx, rlr, Bin(rrs, k', v', l', r')))
   | (Bin(ls, k', v', l', r'), Tip)
     =>  Bin (1+ls, k, x, Bin(ls, k', v', l', r'), Tip)
   | (Bin(ls, k', v', l', r'), Bin(rs, rk, rx, rl, rr))
     => if rs > delta*ls
        then
         (case (rl, rr)
           of (Bin(rls, rlk, rlx, rll, rlr), Bin(rrs, u6, u7,u8,u9))
               => if rls < ratio*rrs
                  then Bin (1+ls+rs, rk, rx,
                            Bin (1+ls+rls, k, x, Bin(ls, k', v', l', r'), rl),
                            rr)
                  else Bin (1+ls+rs, rlk, rlx,
                            Bin (1+ls+size rll, k, x, Bin(ls, k', v', l', r'), rll),
                            Bin (1+rrs+size rlr, rk, rx, rlr, rr))
            | (u10,u11) => Tip (* error "Failure in Data.Map.balanceR" *)
          )
        else
           Bin (1+ls+rs, k, x,
                Bin(ls, k', v', l', r'), Bin(rs, rk,rx,rl, rr));

fun insert cmp k v fmap =
 case fmap
  of Tip => singleton k v
   | Bin(s, k', v', l, r) =>
       case cmp k k'
        of LESS => balanceL k' v' (insert cmp k v l) r
         | GREATER => balanceR k' v' l (insert cmp k v r)
         | EQUAL => Bin(s,k,v,l,r);

end; (* structure Finite_Map *)

(*---------------------------------------------------------------------------*)
(* Support for smart derivatives                                             *)
(*---------------------------------------------------------------------------*)

fun build_char_set cs = Chset cs;

fun assoc_cat r s =
  case r
   of Cat(r1,r2) => Cat(r1,assoc_cat r2 s)
    | otherwise => Cat(r,s);

fun build_cat r s =
   if (r = EMPTY) orelse (s = EMPTY) then EMPTY else
   if r = EPSILON then s else
   if s = EPSILON then r
   else assoc_cat r s;

fun build_neg r =
  case r
   of Neg s => s
    | otherwise => Neg r;

fun build_star r =
  case r
   of Star s => r
    | otherwise => Star r;

fun flatten_or rlist =
 case rlist
  of [] => []
   | Or rs::t => rs @ flatten_or t
   | r::rs => r :: flatten_or rs;

(*---------------------------------------------------------------------------*)
(* Requires all charsets to be leftmost in rs. Mergesort takes care of that. *)
(*---------------------------------------------------------------------------*)

fun merge_charsets list =
 case list
  of (Chset a::Chset b::t) => merge_charsets (Chset(charset_union a b)::t)
   | otherwise => list;

fun remove_dups rlist =
 case rlist
  of [] => []
   | [r] => [r]
   | r::s::t =>
      if regexp_compare r s = EQUAL then
        remove_dups (s::t)
      else
        r::remove_dups (s::t);

fun build_or rlist =
 let val rlist' =
         remove_dups
           (merge_charsets
              (mergesort regexp_leq
                 (flatten_or rlist)))
 in
  if mem (Neg EMPTY) rlist' then Neg EMPTY else
  if mem (Star SIGMA) rlist' then Neg EMPTY
  else
  case rlist'
   of [] => EMPTY
    | [r] => r
    | [Chset cs, r] => (if r = Neg (Chset cs) then Neg EMPTY else
                        if cs = charset_empty then r
                        else Or rlist')
    | Chset cs :: t =>
       (if mem (Neg (Chset cs)) t then Neg EMPTY else
        if cs = charset_empty then Or t
        else Or rlist')
    | _ => Or rlist'
end;

fun normalize r =
 case r
  of Chset cs => build_char_set cs
   | Cat(s,t) => build_cat (normalize s) (normalize t)
   | Star s   => build_star (normalize s)
   | Or rs    => build_or (List.map normalize rs)
   | Neg s    => build_neg (normalize s);

(*---------------------------------------------------------------------------*)
(* Does a regexp admit EPSILON (the empty string)                            *)
(*---------------------------------------------------------------------------*)

fun nullable r =
 case r
  of Chset cs => false
   | Star s   => true
   | Cat(s,t) => nullable s andalso nullable t
   | Or rs    => List.exists nullable (List.rev rs)
   | Neg s    => not(nullable s);

(*---------------------------------------------------------------------------*)
(* Take derivative, then apply smart constructors.                           *)
(*---------------------------------------------------------------------------*)

fun smart_deriv c r =
 case r
  of Chset cs => if charset_mem c cs then EPSILON else EMPTY
   | Cat(Chset cs,t) => if charset_mem c cs then t else EMPTY
   | Cat(s,t) =>
      let val dr = build_cat (smart_deriv c s) t
      in if nullable s
          then build_or [dr, smart_deriv c t]
          else dr
      end
   | Star s => build_cat (smart_deriv c s) (build_star s)
   | Or rs  => build_or (map (smart_deriv c) rs)
   | Neg s  => build_neg (smart_deriv c s);

(*---------------------------------------------------------------------------*)
(* Cache applications of smart_deriv. Unhelpful right now ... might be too   *)
(* fine-grained.                                                             *)
(*---------------------------------------------------------------------------*)
(*
type table = (char * regexp,regexp) Redblackmap.dict
type cache = table ref

fun regexp_cmp (r1,r2) = regexp_compare r1 r2;

fun new_table() =
  Redblackmap.mkDict (pair_compare (Char.compare,regexp_cmp)) : table


local
  val cache = ref (new_table()) : cache
  fun lookup x = Redblackmap.peek (!cache, x)
  fun store (x,y) = (cache := Redblackmap.insert(!cache,x,y))
  fun storable (Chset _) = false
    | storable other = true
in
fun clear_cache () = (cache := new_table())
fun cached_values () = Redblackmap.listItems (!cache)

fun smart_deriv c r =
 if storable r then
  (case lookup (c,r)
    of SOME y => y
     | NONE =>
       let val r' =
           (case r
             of Chset cs => if charset_mem c cs then EPSILON else EMPTY
              | Cat(Chset cs,t) => if charset_mem c cs then t else EMPTY
              | Cat(s,t) =>
                let val dr = build_cat (smart_deriv c s) t
                in if nullable s
                    then build_or [dr, smart_deriv c t]
                    else dr
                end
             | Star s => build_cat (smart_deriv c s) (build_star s)
             | Or rs  => build_or (map (smart_deriv c) rs)
             | Neg s  => build_neg (smart_deriv c s))
      in
         store((c,r),r')
       ; r'
      end)
  else
   (case r
     of Chset cs => if charset_mem c cs then EPSILON else EMPTY
      | Cat(Chset cs,t) => if charset_mem c cs then t else EMPTY
      | Cat(s,t) =>
        let val dr = build_cat (smart_deriv c s) t
        in if nullable s
           then build_or [dr, smart_deriv c t]
           else dr
        end
      | Star s => build_cat (smart_deriv c s) (build_star s)
      | Or rs  => build_or (map (smart_deriv c) rs)
      | Neg s  => build_neg (smart_deriv c s))
end
*)

(*---------------------------------------------------------------------------*)
(* Support for the core regexp compiler.                                     *)
(*---------------------------------------------------------------------------*)

fun transitions r = List.map (fn c => (c,smart_deriv c r)) alphabet;

fun extend_states next_state state_map trans translist =
 case translist
  of [] => (next_state,state_map,trans)
   | (c,s)::t =>
       case Finite_Map.lookup regexp_compare s state_map
        of SOME n => extend_states next_state state_map ((c,n)::trans) t
         | NONE   => extend_states (next_state + 1)
                        (Finite_Map.insert regexp_compare
                                   s next_state state_map)
                        ((c,next_state)::trans)
                        t;

fun build_table translist r arg =
 case arg of
      (next_state,state_map,table) =>
 case extend_states next_state state_map [] translist of
      (next_state,state_map,trans) =>
 case Finite_Map.lookup regexp_compare r state_map
  of SOME n => (next_state, state_map, (n,trans)::table)
   | NONE   => (next_state + 1,
                Finite_Map.insert regexp_compare r next_state state_map,
                (next_state,trans)::table);

fun insert_regexp r seen = Finite_Map.insert regexp_compare r () seen;
fun mem_regexp r seen    = Finite_Map.member regexp_compare r seen;

(*---------------------------------------------------------------------------*)
(* Core regexp compiler. The seen argument holds the already-seen regexps,   *)
(* which become states in the final DFA. The n argument is a step-index used *)
(* to ensure that the function terminates.                                   *)
(*---------------------------------------------------------------------------*)

fun brzozo seen worklist acc n =
 case worklist
  of [] => SOME(seen,acc)
   | r::t =>
     if n <= 0 then NONE else
     if mem_regexp r seen
       then brzozo seen t acc (n-1)
        else let val translist = transitions r
             in brzozo
                  (insert_regexp r seen)
                  (remove_dups (map snd translist) @ t)
                  (build_table translist r acc)
                  (n-1)
             end;
val bigIndex = 2147483647;

fun get_accepts fmap =
 mergesort (fn x => fn y => x <= y)
  (Finite_Map.foldrWithKey
      (fn r => fn n => fn nlist => if nullable r then n::nlist else nlist)
      [] fmap);

fun alist_to_vec list default n max =
 if n=0 then [] else
 case list
  of [] => default :: alist_to_vec [] default (n-1) max
   | ((x,y)::t) =>
      if n <= max then
        (if x = max - n then y :: alist_to_vec t default (n-1) max
         else if x < max - n then alist_to_vec t default n max
         else default :: alist_to_vec list default (n-1) max)
      else [];

fun accepts_to_final_vector accept_states max_state =
  alist_to_vec (map (fn x => (x,true)) accept_states)
               false max_state max_state;

fun table_to_vectors table =
 map (fn p => case p of (k,table2) =>
       alist_to_vec
           (mergesort (inv_image (fn x => fn y => x <= y) fst)
              (map (fn p1 => case p1 of (c,n) => (Char.ord c,SOME n)) table2))
           NONE alphabet_size alphabet_size)
     (mergesort (inv_image (fn x => fn y => x <= y) fst) table);

fun compile_regexp r =
 let val s = normalize r
 in case the (brzozo Finite_Map.empty [s]
                     (1, Finite_Map.singleton s 0, []) bigIndex)
    of (states,(last_state,state_numbering,table))
    => let val delta_vecs = table_to_vectors table
           val final = accepts_to_final_vector
                            (get_accepts state_numbering) last_state
       in (state_numbering, delta_vecs, final)
       end
 end;

fun exec_dfa final_states table n string =
 case string
  of [] => el n final_states
   | c::t =>
       case el (Char.ord c) (el n table)
        of NONE => false
         | SOME k => exec_dfa final_states table k t;

(*---------------------------------------------------------------------------*)
(* Returns a function of type :string -> bool                                *)
(*---------------------------------------------------------------------------*)

fun matcher r =
 case compile_regexp r
  of (state_numbering,delta,final)
  => let val start_state = the (Finite_Map.lookup regexp_compare
                                      (normalize r) state_numbering)
         val match_string = exec_dfa final delta start_state
     in
        {table = map (map Option.valOf) delta,
         start = start_state,
         final = final,
         matchfn = fn s =>  match_string (String.explode s)}
     end;


(*---------------------------------------------------------------------------*)
(* Vector-based DFA instead of list-based.                                   *)
(*---------------------------------------------------------------------------*)

fun vector_matcher r =
 let val {table,start,final,matchfn} = matcher r
     val vfinal  = Vector.fromList final
     val vtable = Vector.fromList (List.map Vector.fromList table)
     fun run n [] = Vector.sub(vfinal,n)
       | run n (c::t) = run (Vector.sub(Vector.sub(vtable,n), Char.ord c)) t
     val match_string = run start
 in {start = start,
     table = vtable,
     final = vfinal,
     matchfn = fn s => match_string (String.explode s)}
 end

(*---------------------------------------------------------------------------*)
(* Just compute the states; no tracking of info needed to construct the rest *)
(* of the DFA.                                                               *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Optimization of certain annoying (because slow to compile) Or regexps.    *)
(*                                                                           *)
(* The following code asserts that                                           *)
(*                                                                           *)
(*  smart_deriv c (Or [w, wr_1, ..., wr_n, EPSILON])                         *)
(*                                                                           *)
(* is equal to                                                               *)
(*                                                                           *)
(*  Or [r_1, ..., r_n, EPSILON] OR EMPTY                                     *)
(*                                                                           *)
(* (where w is a charset) depending on whether c is in the charset or not.   *)
(*                                                                           *)
(* Assumption: the input Or regexp is in normal form. That would mean that   *)
(* EPSILON comes after all the charsets and Cats, so should be at the end.   *)
(* Also, if args is the list constructed by Or, len(args) > 1 so there is a  *)
(* last element x of args, and a separate head element w. Also, w can't be   *)
(* the empty charset. If w is the full charset then EMPTY is not returned.   *)
(*---------------------------------------------------------------------------*)

val tracing = ref true;

fun kprint s = if !tracing then print s else ();

val _ = Feedback.register_btrace("regexp-compiler",tracing);

fun drop w (Cat(a,b)) =
     (case regexp_compare w a
       of EQUAL => b
        | otherwise => raise ERR "drop" "")
  | drop r _ = raise ERR "drop" "";

fun lift_cset_from_or rlist =
 case rlist
  of (w as Chset _) :: t =>
      let val (t',x) = Lib.front_last t
          val t'' = mapfilter (drop w) t'
      in
        if x = EPSILON andalso length t' = length t''
        then let val _ = kprint "\n\n Optimization SUCCEEDS!!\n\n"
                 val trimmed = build_or (t'' @ [EPSILON])
             in if w = SIGMA
                then SOME [trimmed]
                else SOME [EMPTY,trimmed]
             end
        else NONE
      end
   | otherwise => NONE

fun uniq rlist = remove_dups (mergesort regexp_leq rlist);

fun transitions r =
 case r of
  Or rlist =>
     (case lift_cset_from_or rlist
       of SOME rlist' => rlist'
        | NONE => uniq(List.map (fn c => smart_deriv c r) alphabet)
     )
   | otherwise =>
      uniq(List.map (fn c => smart_deriv c r) alphabet);

fun dom_brzozo seen [] = seen
  | dom_brzozo seen (r::t) =
      (kprint ("Worklist length: "^Int.toString(length t + 1)^". Head:\n  ")
       ; if !tracing then print_regexp r else ()
       ; kprint "\n"
       ;
        if mem_regexp r seen
         then (kprint "already seen; trying next element.\n\n"
               ;
               dom_brzozo seen t
              )
         else let val _ = kprint ("will be a new state (size: "^Int.toString (PolyML.objSize r)^"). ")
                  val prospects = transitions r
                  val _ = kprint ("Successors: "^Int.toString (length prospects)^"\n\n")
              in dom_brzozo (insert_regexp r seen)
                            (prospects @ t)
              end
        );

fun domBrz r =
 let open regexpMisc
     val _ = stdErr_print "Starting Brzozowski.\n"
     val states = time (dom_brzozo Finite_Map.empty) [normalize r]
     val _ = stdErr_print ("states: "^Int.toString (Finite_Map.size states)^"\n");
 in
   ()
 end;

end
