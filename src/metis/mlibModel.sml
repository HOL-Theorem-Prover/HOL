(* ========================================================================= *)
(* FINITE MODELS                                                             *)
(* Copyright (c) 2003-2004 Joe Hurd.                                         *)
(* ========================================================================= *)

(*
app load ["mlibHeap", "mlibTerm", "mlibSubst", "mlibMatch", "mlibThm", "mlibTermorder"];
*)

(*
*)
structure mlibModel :> mlibModel =
struct

infix ## |->;

open mlibUseful mlibTerm;

structure W = Word; local open Word in end;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibModel";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val gen = Random.newgenseed 1.0;

type fp = string * int list;

val fp_compare = lex_order String.compare (lex_list_order Int.compare);

val pp_fp = pp_map
  (fn (f,a) => Fn (f, map (fn n => Fn (int_to_string n, [])) a)) pp_term;

fun cached c f k =
  case Binarymap.peek (!c,k) of SOME v => v
  | NONE => let val v = f k val () = c := Binarymap.insert (!c,k,v) in v end;

fun log2_int 1 = 0 | log2_int n = 1 + log2_int (n div 2);

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed and cannot be perturbed             *)
(* Note: a model of size N has integer elements 0...N-1                      *)
(* ------------------------------------------------------------------------- *)

type fix = int -> {func : (string * int list) -> int option,
                   pred : (string * int list) -> bool option};

fun fix_merge fix1 fix2 N =
  let
    val {func = func1, pred = pred1} = fix1 N
    val {func = func2, pred = pred2} = fix2 N
    fun func x = case func1 x of NONE => func2 x | sn => sn
    fun pred x = case pred1 x of NONE => pred2 x | sb => sb
  in
    {func = func, pred = pred}
  end;

fun fix_mergel fixl = foldl (fn (h,t) => fix_merge h t) (hd fixl) (tl fixl);

fun map_fix map_fn fix N =
  let
    val {func,pred} = fix N
    fun func' (f,a) = case map_fn f of NONE => NONE | SOME f' => func (f',a)
    fun pred' (p,a) = case map_fn p of NONE => NONE | SOME p' => pred (p',a)
  in
    {func = func', pred = pred'}
  end;

val pure_fix : fix =
  fn _ => {func = K NONE, pred = fn ("=",[m,n]) => SOME (m = n) | _ => NONE};

val basic_fix : fix =
  let
    fun func ("id",[n]) = SOME n
      | func ("fst",[n,_]) = SOME n
      | func ("snd",[_,n]) = SOME n
      | func ("#1",n::_) = SOME n
      | func ("#2",_::n::_) = SOME n
      | func ("#3",_::_::n::_) = SOME n
      | func _ = NONE
    fun pred ("<>",[m,n]) = SOME (m = n)
      | pred _ = NONE
  in
    K {func = func, pred = pred}
  end;

local
  type div_set = (int * int) Binaryset.set
  val empty : div_set = Binaryset.empty (lex_order Int.compare Int.compare);
  fun member i (s : div_set) = Binaryset.member (s,i);
  fun add i (s : div_set) = Binaryset.add (s,i);

  fun mk_div _ i 0 s = add (i,0) s
    | mk_div N i j s = mk_div N i ((j + i) mod N) (add (i,j) s);
in
  fun modulo_fix N =
    let
      fun f x = x mod N
      val divides = foldl (fn (i,s) => mk_div N i i s) empty (interval 0 N)
      val zero = f 0 and one = f 1 and two = f 2
      fun func ("0",[]) = SOME zero
        | func ("1",[]) = SOME one
        | func ("2",[]) = SOME two
        | func ("suc",[n]) = SOME (f (n + one))
        | func ("pre",[n]) = SOME (f (n - one))
        | func ("~",[n]) = SOME (f (~n))
        | func ("+",[m,n]) = SOME (f (m + n))
        | func ("-",[m,n]) = SOME (f (m - n))
        | func ("*",[m,n]) = SOME (f (m * n))
        | func ("exp",[m,n]) = SOME (funpow n (fn x => f (x * m)) one)
        | func ("mod",[m,n]) = SOME (if n = zero then m else m mod n)
        | func _ = NONE
      fun pred ("<=",[m,n]) = SOME (m <= n)
        | pred ("<",[m,n]) = SOME (m < n)
        | pred (">",[m,n]) = SOME (m > n)
        | pred (">=",[m,n]) = SOME (m >= n)
        | pred ("is_0",[n]) = SOME (n = zero)
        | pred ("divides",[m,n]) = SOME (member (m,n) divides)
        | pred ("odd",[n]) = Option.map not (pred ("even",[n]))
        | pred ("even",[n]) = pred ("divides",[two,n])
        | pred _ = NONE
    in
      {func = func, pred = pred}
    end;
end;

fun heap_fix N =
  let
    val M = N - 1
    fun f x = if x <= 0 then 0 else if M <= x then M else x
    val zero = f 0 and one = f 1 and two = f 2
    fun func ("0",[]) = SOME zero
      | func ("1",[]) = SOME one
      | func ("2",[]) = SOME two
      | func ("suc",[m]) = SOME (f (m + one))
      | func ("pre",[m]) = SOME (f (m - one))
      | func ("+",[m,n]) = SOME (f (m + n))
      | func ("-",[m,n]) = SOME (f (m - n))
      | func ("*",[m,n]) = SOME (f (m * n))
      | func ("exp",[m,n]) = SOME (funpow n (fn x => f (x * m)) one)
      | func _ = NONE
    fun pred ("<=",[m,n]) = SOME (m <= n)
      | pred ("<",[m,n]) = SOME (m < n)
      | pred (">",[m,n]) = SOME (m > n)
      | pred (">=",[m,n]) = SOME (m >= n)
      | pred ("is_0",[m]) = SOME (m = zero)
      | pred _ = NONE
  in
    {func = func, pred = pred}
  end;

fun set_fix N =
  let
    val empty = 0w0
    and univ = W.- (W.<< (0w1, W.fromInt (log2_int N)), 0w1)
    fun to_set n = W.max (W.fromInt n, univ)
    val from_set = W.toInt
    fun union s t = W.orb (s,t)
    fun inter s t = W.andb (s,t)
    fun compl s = W.andb (W.notb s, univ)
    fun subset s t = inter s (compl t) = empty
    fun count_bits w =
        if w = 0w0 then 0 else
          (if W.andb (w,0w1) = 0w1 then 1 else 0) + count_bits (W.>> (w,0w1))
    fun func ("empty",[]) = SOME (from_set empty)
      | func ("univ",[]) = SOME (from_set univ)
      | func ("union",[m,n]) = SOME (from_set (union (to_set m) (to_set n)))
      | func ("inter",[m,n]) = SOME (from_set (inter (to_set m) (to_set n)))
      | func ("compl",[n]) = SOME (from_set (compl (to_set n)))
      | func ("card",[n]) = SOME (count_bits (to_set n))
      | func _ = NONE
    fun pred ("in",[_,n]) =
        let
          val s = to_set n
        in
          if s = empty then SOME false
          else if s = univ then SOME true else NONE
        end
      | pred ("subset",[m,n]) = SOME (subset (to_set m) (to_set n))
      | pred _ = NONE
  in
    {func = func, pred = pred}
  end;

(* ------------------------------------------------------------------------- *)
(* Parameters                                                                *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int, fix : fix};

val defaults = {size = 5, fix = pure_fix};

fun update_size f (parm : parameters) : parameters =
  let val {size = n, fix = r} = parm in {size = f n, fix = r} end;

fun update_fix f (parm : parameters) : parameters =
  let val {size = n, fix = r} = parm in {size = n, fix = f r} end;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = (string,int) Binarymap.dict;

val emptyv : valuation = Binarymap.mkDict String.compare;

fun insertv (v |-> n) s : valuation = Binarymap.insert (s,v,n);

fun lookupv (s : valuation) v =
  case Binarymap.peek (s,v) of SOME n => n
  | NONE => raise Bug "mlibModel.lookupv";

fun randomv n =
  let fun f (v,s) = insertv (v |-> Random.range (0,n) gen) s
  in foldl f emptyv
  end;

val pp_valuation =
  pp_map (map op|-> o Binarymap.listItems)
  (pp_list (pp_maplet pp_string pp_int));

fun valuation_to_string v = PP.pp_to_string (!LINE_LENGTH) pp_valuation v;

(* ------------------------------------------------------------------------- *)
(* Random models are based on cryptographic hashing                          *)
(* ------------------------------------------------------------------------- *)

local
  fun randomize id p pred args =
    let
      val mesg =
        int_to_string id ^ " " ^ p ^ " " ^ (if pred then "p" else "f") ^
        foldl (fn (a,s) => s ^ " " ^ int_to_string a) "" args
      val hash = mlibPortable.md5 mesg
      val _ = chatting 4 andalso
              chat ("randomize: mesg=" ^ mesg ^ ", hash=" ^ hash ^ ".\n")
    in
      hash
    end;

  (* Extraction is supposed to follow a uniform distribution.             *)
  (* Unless we are lucky enough to get BASE mod N = 0, to keep the bias   *)
  (* beneath MAX_BIAS we must ensure the number of iterations n satisfies *)
  (* BASE^n / N >= 1 / MAX_BIAS.                                          *)
  val BASE = 64;
  val MAX_BIAS = 0.01;

  val bias = Real.ceil (1.0 / MAX_BIAS);
  fun extract N =
    let
      val base_mod_N = BASE mod N
      fun ext _ _ [] = raise Bug "mlibModel.extract: ran out of data"
        | ext t i (c :: cs) =
          let
            val i = (base_mod_N * i + base64_to_int c) mod N
            val t = t div BASE
          in
            if t = 0 orelse base_mod_N = 0 then i else ext t i cs
          end
    in
      ext (N * bias - 1) 0
    end;
in
  fun random_fn N id (f,args) =
    extract N (String.explode (randomize id f false args));

  fun random_pred id (p,args) =
    base64_to_int (String.sub (randomize id p true args, 0)) mod 2 = 0;
end;

fun cached_random_fn cache N id f_args = cached cache (random_fn N id) f_args;
fun cached_random_pred cache id p_args = cached cache (random_pred id) p_args;

(* ------------------------------------------------------------------------- *)
(* Representing finite models.                                               *)
(* ------------------------------------------------------------------------- *)

datatype model = MODEL of
  {parm : parameters,
   id : int,
   cachef : (fp,int) Binarymap.dict ref,
   cachep : (fp,bool) Binarymap.dict ref,
   overf : (fp,int) Binarymap.dict,
   overp : (fp,bool) Binarymap.dict,
   fixf : (string * int list) -> int option,
   fixp : (string * int list) -> bool option};

local
  val new_id = let val n = ref ~1 in fn () => (n := !n + 1; !n) end;
in
  fun new (parm : parameters) =
    let
      val {size = n, fix = r} = parm
      val {func = fixf, pred = fixp} = r n
      val () = assert (1 <= n) (Bug "mlibModel.new: nonpositive size")
      val id = new_id ()
      val cachef = ref (Binarymap.mkDict fp_compare)
      val cachep = ref (Binarymap.mkDict fp_compare)
      val overf = Binarymap.mkDict fp_compare
      val overp = Binarymap.mkDict fp_compare
    in
      MODEL
      {parm = parm, id = id, cachef = cachef, cachep = cachep,
       overf = overf, overp = overp, fixf = fixf, fixp = fixp}
    end;
end;

fun msize (MODEL {parm = {size = N, ...}, ...}) = N;

fun update_overf overf m =
  let val MODEL {parm, id, cachef, cachep, overp, fixf, fixp, ...} = m
  in MODEL {parm = parm, id = id, cachef = cachef, cachep = cachep,
            overf = overf, overp = overp, fixf = fixf, fixp = fixp}
  end;

fun update_overp overp m =
  let val MODEL {parm, id, cachef, cachep, overf, fixf, fixp, ...} = m
  in MODEL {parm = parm, id = id, cachef = cachef, cachep = cachep,
            overf = overf, overp = overp, fixf = fixf, fixp = fixp}
  end;

fun pp_model pp (MODEL {parm = {size = N, ...}, id, ...}) =
  pp_string pp (int_to_string id ^ ":" ^ int_to_string N);

(* ------------------------------------------------------------------------- *)
(* Evaluating ground formulas on models                                      *)
(* ------------------------------------------------------------------------- *)

fun eval_fn m f_args =
  let
    val MODEL {parm = {size = N, ...}, id, cachef, overf, fixf, ...} = m
  in
    case fixf f_args of SOME b => b
    | NONE =>
      (case Binarymap.peek (overf,f_args) of SOME n => n
       | NONE => cached_random_fn cachef N id f_args)
  end;

fun eval_pred m p_args =
  let
    val MODEL {id,cachep,overp,fixp,...} = m
  in
    case fixp p_args of SOME b => b
    | NONE =>
      (case Binarymap.peek (overp,p_args) of SOME b => b
       | NONE => cached_random_pred cachep id p_args)
  end;

fun eval_term m v =
  let
    fun e (Var x) = lookupv v x
      | e (Fn (f,a)) = eval_fn m (f, map (eval_term m v) a)
  in
    e
  end;

fun evaluate_term m tm = eval_term m emptyv tm;

fun eval_formula m =
  let
    fun e True _ = true
      | e False _ = false
      | e (Atom (Var _)) _ = raise Bug "eval_formula: boolean var"
      | e (Atom (Fn (p,a))) v = eval_pred m (p, map (eval_term m v) a)
      | e (Not p) v = not (e p v)
      | e (Or (p,q)) v = e p v orelse e q v
      | e (And (p,q)) v = e p v andalso e q v
      | e (Imp (p,q)) v = e (Or (Not p, q)) v
      | e (Iff (p,q)) v = e p v = e q v
      | e (Forall (x,p)) v = List.all (e' p v x) (interval 0 (msize m))
      | e (Exists (x,p)) v = e (Not (Forall (x, Not p))) v
    and e' fm v x n = e fm (insertv (x |-> n) v)
  in
    fn v => fn fm => e fm v
  end;

fun evaluate_formula m fm = eval_formula m emptyv fm;

(* ------------------------------------------------------------------------- *)
(* Check whether a random grounding of a formula is satisfied by the model   *)
(* ------------------------------------------------------------------------- *)

fun check1 fvs m fm =
  let
    val v = randomv (msize m) fvs
    val _ = chatting 3 andalso
            chat ("check: valuation=" ^ valuation_to_string v ^ ".\n")
  in
    eval_formula m v fm
  end;

fun check m fm = check1 (FV fm) m fm;

fun checkn m fm n =
  let
    val fvs = FV fm
    val r =
      if null fvs then if check1 [] m fm then n else 0
      else funpow n (fn i => if check1 fvs m fm then i + 1 else i) 0
    val _ = chatting 1 andalso
            chat ("checkn: " ^ formula_to_string fm ^ ": " ^
                  int_to_string r ^ "/" ^ int_to_string n ^ "\n")
  in
    r
  end;

fun count m fm =
  let
    val n = rev (interval 0 (msize m))
    fun f x [] = x
      | f (i,j) ((v,[]) :: l) =
      f ((if eval_formula m v fm then i + 1 else i), j + 1) l
      | f x ((v, w :: ws) :: l) =
      f x (foldl (fn (i,z) => (insertv (w |-> i) v, ws) :: z) l n)
    val r = f (0,0) [(emptyv, FV fm)]
    val _ = chatting 1 andalso
            chat ("count: " ^ formula_to_string fm ^ ": " ^
                  int_to_string (fst r) ^ "/" ^ int_to_string (snd r) ^ "\n")
  in
    r
  end;

(* ------------------------------------------------------------------------- *)
(* Sets of model perturbations                                               *)
(* ------------------------------------------------------------------------- *)

datatype perturbation = PredP of (fp,bool) maplet | FnP of (fp,int) maplet;

val pp_perturbation =
  pp_map (fn PredP (p |-> s) => p |-> bool_to_string s
           | FnP (p |-> n) => p |-> int_to_string n)
  (pp_maplet pp_fp pp_string);

fun perturbation_to_string p = PP.pp_to_string (!LINE_LENGTH) pp_perturbation p;

fun comparep (PredP _, FnP _) = LESS
  | comparep (PredP (p1 |-> b1), PredP (p2 |-> b2)) =
  lex_order fp_compare bool_compare ((p1,b1),(p2,b2))
  | comparep (FnP (f1 |-> n1), FnP (f2 |-> n2)) =
  lex_order fp_compare Int.compare ((f1,n1),(f2,n2))
  | comparep (FnP _, PredP _) = GREATER;

val emptyp : perturbation Binaryset.set = Binaryset.empty comparep;

val sizep = Binaryset.numItems;

fun randomp s = List.nth (Binaryset.listItems s, Random.range (0, sizep s) gen);

fun addp x s = Binaryset.add (s,x);

fun deletep x s = Binaryset.delete (s,x);

fun unionp s t = Binaryset.union (s,t);

fun interp s t = Binaryset.intersection (s,t);

(* ------------------------------------------------------------------------- *)
(* Perturbing a model to make a ground formula true                          *)
(* ------------------------------------------------------------------------- *)

fun perturb_targets N p =
  let
    val dom = interval 0 N
    fun g l t x = p (List.revAppend (l, x :: t))
    fun f acc _ [] = rev acc
      | f acc l (h :: t) = f (List.filter (g l t) dom :: acc) (h :: l) t
  in
    f [] []
  end;

fun perturb_fnl m v =
  let
    val MODEL {fixf,...} = m
    fun pert_fnl tms targs set = foldl pert_fn set (zip tms targs)
    and pert_fn ((_,[]),set) = set
      | pert_fn ((Var _,_),set) = set
      | pert_fn ((Fn (f,tms), targ), set) =
      let
        val targset = Intset.addList (Intset.empty,targ)
        fun testf args = Intset.member (targset, eval_fn m (f,args))
        val args = map (eval_term m v) tms
        val targs = perturb_targets (msize m) testf args
        val set =
          case fixf (f,args) of (SOME _) => set
          | NONE => foldl (fn (x,s) => addp (FnP ((f,args) |-> x)) s) set targ
      in
        pert_fnl tms targs set
      end
  in
    pert_fnl
  end;

fun perturb_atom m v s (p,tms) =
  let
    val MODEL {fixp,...} = m
    fun testp args = eval_pred m (p,args) = s
    val args = map (eval_term m v) tms
    val targs = perturb_targets (msize m) testp args
    val set =
      case fixp (p,args) of (SOME _) => emptyp
      | NONE => addp (PredP ((p,args) |-> s)) emptyp
  in
    perturb_fnl m v tms targs set
  end;

fun perturb_formula m =
  let
    fun ex v x = map (fn n => insertv (x |-> n) v) (interval 0 (msize m))
    fun f _ _ True = emptyp
      | f _ _ False = emptyp
      | f s v (Not p) = f (not s) v p
      | f _ _ (Atom (Var _)) = raise Bug "perturb_formula: boolean var"
      | f s v (Atom (Fn p)) = perturb_atom m v s p
      | f true v (Or (p,q)) = fl unionp [(v,p),(v,q)]
      | f false v (Or (p,q)) = f true v (And (Not p, Not q))
      | f true v (And (p,q)) = flc interp [(v,p),(v,q)]
      | f false v (And (p,q)) = f true v (Or (Not p, Not q))
      | f s v (Imp (p,q)) = f s v (Or (Not p, q))
      | f s v (Iff (p,q)) = f s v (And (Imp (p,q), Imp (q,p)))
      | f true v (Exists (x,p)) = fl unionp (map (fn w => (w,p)) (ex v x))
      | f false v (Exists (x,p)) = f true v (Forall (x, Not p))
      | f true v (Forall (x,p)) = flc interp (map (fn w => (w,p)) (ex v x))
      | f false v (Forall (x,p)) = f true v (Exists (x, Not p))
    and flc c l = fl c (List.filter (fn (v,p) => not (eval_formula m v p)) l)
    and fl c l =
      case map (fn (v,p) => f true v p) l of
        [] => raise Bug "perturb_formula: no identity"
      | h :: t => foldl (fn (s,x) => c s x) h t
  in
    f true
  end;

fun override m =
  let
    val MODEL {overf,overp,fixf,fixp,...} = m
  in
    fn PredP (p |-> b) =>
       (if chatting 2 andalso chat "checking pred override\n" andalso
           Option.isSome (fixp p) then raise Bug "override: fixp" else ();
        update_overp (Binarymap.insert (overp,p,b)) m)
     | FnP (f |-> n) =>
       (if chatting 2 andalso chat "checking fn override\n" andalso
           Option.isSome (fixf f) then raise Bug "override: fixf" else ();
        update_overf (Binarymap.insert (overf,f,n)) m)
  end;

fun perturb m v fm =
  let
    fun f perts =
      if sizep perts = 0 then NONE else
        let
          val pert = randomp perts
          val m' = override m pert
          val good = eval_formula m' v fm
          val _ = chatting 2 andalso
                  chat ("perturb: " ^ (if good then "good" else "bad") ^
                        " pert: " ^ perturbation_to_string pert ^ ".\n")
        in
          if good then SOME m' else f (deletep pert perts)
        end
  in
    f (perturb_formula m v fm)
  end;

local
  fun integrate (vs,fm,n,i,p) m =
    let
      val v = randomv (msize m) vs
      val _ = chatting 3 andalso
              chat ("integrate: valuation=" ^ valuation_to_string v ^ ".\n")
    in
      if eval_formula m v fm then ((vs, fm, n + 1, i, p), m) else
        case perturb m v fm of NONE => ((vs, fm, n, i + 1, p), m)
        | SOME m => ((vs, fm, n, i, p + 1), m)
    end;

  fun chatperturb (_,fm,n,i,p) =
    (chat ("perturb: " ^ formula_to_string fm ^ "\n" ^
           "     tests=" ^ int_to_string (n + i + p) ^
           ": natural=" ^ int_to_string n ^
           ", impossible=" ^ int_to_string i ^
           ", perturbed=" ^ int_to_string p ^ ".\n"); true);
in
  fun perturb fms perts m =
    let
      val fmi = map (fn p => (FV p, p, 0, 0, 0)) fms
      val (fmi,m) = funpow perts (uncurry (maps integrate)) (fmi,m)
      val _ = chatting 1 andalso List.all chatperturb fmi
    in
      m
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing terms with free vars                                      *)
(* ------------------------------------------------------------------------- *)

local
  exception Toomany;

  val i2s = int_to_string;

  fun b2s true = "T" | b2s false = "F";

  val mkv = foldl (fn (x,v) => insertv x v) emptyv;

  fun tablify tab =
    join "\n"
    (align_table {pad = #" ", left = false}
     (map (fn l => ("  " ^ hd l) :: map (fn x => " " ^ x) (tl l)) tab)) ^ "\n";

  fun to_string eval x2s m tm [] = x2s (eval m (mkv []) tm)
    | to_string eval x2s m tm [v] =
      let
        val l = interval 0 (msize m)
        val head = v :: map i2s l
        val line = "" :: map (fn x => x2s (eval m (mkv [v |-> x]) tm)) l
      in
        tablify [head,line]
      end
    | to_string eval x2s m tm [v,w] =
      let
        val l = interval 0 (msize m)
        val head = ["" :: v :: map i2s l, w :: "" :: map (K "") l]
        fun f y x = x2s (eval m (mkv [v |-> x, w |-> y]) tm)
        val tab = head @ map (fn y => i2s y :: "" :: map (f y) l) l
      in
        tablify tab
      end
    | to_string _ _ _ _ _ = raise Toomany;
in
  fun term_to_string m tm =
    to_string eval_term i2s m tm (FVT tm)
    handle Toomany => raise Error "mlibModel.term_to_string: too many free vars";

  fun formula_to_string m fm =
    to_string eval_formula b2s m fm (FV fm)
    handle Toomany => raise Error "mlibModel.formula_to_string: too many free vars";
end;

(* ------------------------------------------------------------------------- *)
(* Rebinding for signature                                                   *)
(* ------------------------------------------------------------------------- *)

val size = msize;

end
