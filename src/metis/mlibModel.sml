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

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val module = "mlibModel";
val () = traces := {module = module, alignment = I} :: !traces;
fun chatting l = tracing {module = module, level = l};
fun chat s = (trace s; true)

(* ------------------------------------------------------------------------- *)
(* Parameters                                                                *)
(* ------------------------------------------------------------------------- *)

type parameters = {size : int};

val defaults = {size = 5};

fun update_size f (parm : parameters) : parameters =
  let val {size = n} = parm in {size = f n} end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val gen = Random.newgenseed 1.0;

type fp = string * int list;

val fp_compare = lex_combine String.compare (lex_compare Int.compare);

val pp_fp = pp_map
  (fn (f,a) => Fn (f, map (fn n => Fn (int_to_string n, [])) a)) pp_term;

fun cached c f k =
  case Binarymap.peek (!c,k) of SOME v => v
  | NONE => let val v = f k val () = c := Binarymap.insert (!c,k,v) in v end;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = (string,int) Binarymap.dict;

val emptyv : valuation = Binarymap.mkDict String.compare;

fun insertv (v |-> n) s : valuation = Binarymap.insert (s,v,n);

fun lookupv (s : valuation) v =
  case Binarymap.peek (s,v) of SOME n => n
  | NONE => raise BUG "mlibModel.lookupv" "";

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
      fun ext _ _ [] = raise BUG "mlibModel.extract" "ran out of data"
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
  {parm   : parameters,
   id     : int,
   cachef : (fp,int) Binarymap.dict ref,
   cachep : (fp,bool) Binarymap.dict ref,
   overf  : (fp,int) Binarymap.dict,
   overp  : (fp,bool) Binarymap.dict};

local
  val new_id = let val n = ref ~1 in fn () => (n := !n + 1; !n) end;
in
  fun new (parm : parameters) =
    let
      val () = assert (1 <= #size parm) (BUG "mlibModel.new" "nonpositive size")
      val id = new_id ()
      val cachef = ref (Binarymap.mkDict fp_compare)
      val cachep = ref (Binarymap.mkDict fp_compare)
      val overf = Binarymap.mkDict fp_compare
      val overp = Binarymap.mkDict fp_compare
    in
      MODEL
      {parm = parm, id = id, cachef = cachef, cachep = cachep,
       overf = overf, overp = overp}
    end;
end;

fun msize (MODEL {parm = {size = N, ...}, ...}) = N;

fun update_overf f m =
  let val MODEL {parm, id, cachef=cf, cachep=cp, overp=p, ...} = m
  in MODEL {parm=parm, id=id, cachef=cf, cachep=cp, overf=f, overp=p}
  end;

fun update_overp p m =
  let val MODEL {parm, id, cachef=cf, cachep=cp, overf=f, ...} = m
  in MODEL {parm=parm, id=id, cachef=cf, cachep=cp, overf=f, overp=p}
  end;

fun pp_model pp (MODEL {parm = {size = N, ...}, id, ...}) =
  pp_string pp (int_to_string id ^ ":" ^ int_to_string N);

(* ------------------------------------------------------------------------- *)
(* Evaluating ground formulas on models                                      *)
(* ------------------------------------------------------------------------- *)

fun eval_fn m f_args =
  let
    val MODEL {parm = {size = N, ...}, id, cachef, overf, ...} = m
  in
    case Binarymap.peek (overf,f_args) of SOME n => n
    | NONE => cached_random_fn cachef N id f_args
  end;

fun eval_pred _ ("=",[x,y]) = x = y
  | eval_pred m p_args =
  let
    val MODEL {id,cachep,overp,...} = m
  in
    case Binarymap.peek (overp,p_args) of SOME b => b
    | NONE => cached_random_pred cachep id p_args
  end;

fun eval_term m v =
  let
    fun e (Var x) = lookupv v x
      | e (Fn (f,a)) = eval_fn m (f, map (eval_term m v) a)
  in
    e
  end;

fun eval_formula m =
  let
    fun e True _ = true
      | e False _ = false
      | e (Atom (Var _)) _ = raise BUG "eval_formula" "boolean var"
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
  lex_combine fp_compare bool_compare ((p1,b1),(p2,b2))
  | comparep (FnP (f1 |-> n1), FnP (f2 |-> n2)) =
  lex_combine fp_compare Int.compare ((f1,n1),(f2,n2))
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

fun perturb_fn _ _ [] _ set = set
  | perturb_fn _ _ _ (Var _) set = set
  | perturb_fn m v targ (Fn (f,tms)) set =
  let
    val testf =
      let val targset = Intset.addList (Intset.empty, targ)
      in fn args => Intset.member (targset, eval_fn m (f,args))
      end
    val args = map (eval_term m v) tms
    val set = foldl (fn (x,s) => addp (FnP ((f,args) |-> x)) s) set targ
    val targs = perturb_targets (msize m) testf args
  in
    foldl (fn ((tm,t),z) => perturb_fn m v t tm z) set (zip tms targs)
  end;

fun perturb_atom m v s (p,tms) =
  let
    fun testp args = eval_pred m (p,args) = s
    val args = map (eval_term m v) tms
    val targs = perturb_targets (msize m) testp args
    val set =
      case (p,tms) of ("=",[_,_]) => emptyp
      | _ => addp (PredP ((p,args) |-> s)) emptyp
  in
    foldl (fn ((tm,targ),z) => perturb_fn m v targ tm z) set (zip tms targs)
  end;

fun perturb_formula m =
  let
    fun ex v x = map (fn n => insertv (x |-> n) v) (interval 0 (msize m))
    fun f _ _ True = emptyp
      | f _ _ False = emptyp
      | f s v (Not p) = f (not s) v p
      | f _ _ (Atom (Var _)) = raise BUG "perturb_formula" "boolean var"
      | f s v (Atom (Fn p)) = perturb_atom m v s p
      | f true v (Or (p,q)) = fl unionp [(v,p), (v,q)]
      | f false v (Or (p,q)) = f true v (And (Not p, Not q))
      | f true v (And (p,q)) = flc interp [(v,p), (v,q)]
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
        [] => raise BUG "perturb_formula" "no identity"
      | h :: t => foldl (fn (s,x) => c s x) h t
  in
    f true
  end;

fun override m =
  let
    val MODEL {overf,overp,...} = m
  in
    fn PredP (p |-> b) => update_overp (Binarymap.insert (overp, p, b)) m
     | FnP (f |-> n) => update_overf (Binarymap.insert (overf, f, n)) m
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
(* Signature functions                                                       *)
(* ------------------------------------------------------------------------- *)

val size = msize;

end
