structure set_sepLib :> set_sepLib =
struct

(* 
  app load ["set_sepTheory"];
*)
 
open HolKernel boolLib bossLib;
open set_sepTheory;
 

(* ----------------------------------------------------------------------------- *)
(* Helpers                                                                       *)
(* ----------------------------------------------------------------------------- *)

fun conv2ssfrag name conv pattern = simpLib.SSFRAG{
  ac = [], congs = [],
  convs = [{ name  = name, conv = K (K conv), key = SOME([], pattern), trace = 10 }],
  dprocs = [], filter = NONE, rewrs = []};


(* ----------------------------------------------------------------------------- *)
(* MOVE_STAR_TAC in various forms                                                *)
(* ----------------------------------------------------------------------------- *)

val star_ss = simpLib.ac_ss [(STAR_ASSOC,STAR_SYM)];
 
fun MATCH_TYPE_mk_eq (t,t') =
  let
    fun f x y = inst (match_type (type_of x) (type_of y)) x
  in
    mk_eq (f t t',t') handle e => mk_eq (t,f t' t)
  end;

fun MOVE_STAR_THM t t' =
  let 
    val tm  = (Parse.typedTerm t  ``:('a->bool)->bool`` handle e => Parse.Term t)
    val tm' = (Parse.typedTerm t' ``:('a->bool)->bool`` handle e => Parse.Term t')
    val goal = MATCH_TYPE_mk_eq (tm,tm')  
  in
    prove(goal,
    SIMP_TAC (bool_ss++star_ss) [emp_STAR]
    THEN METIS_TAC [STAR_ASSOC,STAR_SYM,STAR_OVER_DISJ])    
  end;

fun ONCE_REWRITE_ASSUMS xs = 
  POP_ASSUM_LIST (fn thms => 
    (MAP_EVERY (ASSUME_TAC o ONCE_REWRITE_RULE xs)) (rev thms));

fun MOVE_STAR_TAC t t' = ONCE_REWRITE_TAC [MOVE_STAR_THM t t'];
fun ASM_MOVE_STAR_TAC t t' = ONCE_REWRITE_ASSUMS [MOVE_STAR_THM t t'];
fun FULL_MOVE_STAR_TAC t t' = MOVE_STAR_TAC t t' THEN ASM_MOVE_STAR_TAC t t';

fun MOVE_STAR_CONV t t' = ONCE_REWRITE_CONV [MOVE_STAR_THM t t'];
fun MOVE_STAR_RULE t t' = CONV_RULE (MOVE_STAR_CONV t t');


(* ----------------------------------------------------------------------------- *)
(* Conversions for pushing cond to the right                                     *)
(* ----------------------------------------------------------------------------- *)

val cond_ELIM = prove(
  ``!c c' P . (cond c * cond c' = cond (c /\ c')) /\ 
              (P * cond c * cond c' = P * cond (c /\ c'))``,
  REWRITE_TAC [GSYM STAR_ASSOC,SEP_cond_CLAUSES]);
  
val cond_MOVE = prove(
  ``!c P Q. (cond c * P = P * cond c) /\
            (P * cond c * Q = P * Q * cond c)``,
  SIMP_TAC (bool_ss++star_ss) []);

val SEP_cond_CONV =
  REWRITE_CONV [STAR_ASSOC] THENC
  REPEATC (REWRITE_CONV [cond_ELIM] THENC ONCE_REWRITE_CONV [cond_MOVE]) THENC
  REWRITE_CONV [GSYM CONJ_ASSOC];

val SEP_cond_ss = conv2ssfrag "SEP_cond_CONV" SEP_cond_CONV ``x * (y:'a set -> bool)``;


(* ----------------------------------------------------------------------------- *)
(* Conversions for pushing SEP_EXISTS to the left                                *)
(* ----------------------------------------------------------------------------- *)

val star = prim_mk_const {Name="STAR",Thy="set_sep"};
val sep_conj = prim_mk_const {Name="SEP_CONJ",Thy="set_sep"};
val sep_disj = prim_mk_const {Name="SEP_DISJ",Thy="set_sep"};
val sep_exists = prim_mk_const {Name="SEP_EXISTS",Thy="set_sep"};

val dest_star = dest_binop star (ERR"dest_star" "not a \"*\"");
val dest_sep_conj = dest_binop sep_conj (ERR"dest_conj" "not a \"/\\\"");
val dest_sep_disj = dest_binop sep_disj (ERR"dest_disj" "not a \"\\/\"");
val dest_sep_exists = dest_binder sep_exists (ERR"dest_sep_exists" "not a \"SEP_EXISTS\"");

val BINOP1 = RATOR_CONV o RAND_CONV;
val BINOP2 = RAND_CONV;

fun LEFT_EXISTS_ABSORB dest_fun rule (tm:term) =
  let
    val (x,y) = dest_fun tm
    val (v,x) = dest_sep_exists x
    val x = mk_abs(v,x)
    val th = ISPECL [x,y] rule
    val c1 = ALPHA_CONV v THENC ABS_CONV BETA_CONV
    val c2 = ALPHA_CONV v THENC (ABS_CONV o BINOP1) BETA_CONV;
    val c1 = (BINOP1 o BINOP1 o RAND_CONV) c1
    val c2 = (BINOP2 o RAND_CONV) c2;
    val th = CONV_RULE (c1 THENC c2) th
  in th end;

fun RIGHT_EXISTS_ABSORB dest_fun rule (tm:term) =
  let
    val (x,y) = dest_fun tm
    val (v,y) = dest_sep_exists y
    val y = mk_abs(v,y)
    val th = ISPECL [y,x] rule
    val c1 = ALPHA_CONV v THENC ABS_CONV BETA_CONV
    val c2 = ALPHA_CONV v THENC (ABS_CONV o BINOP2) BETA_CONV;
    val c1 = (BINOP1 o BINOP2 o RAND_CONV) c1
    val c2 = (BINOP2 o RAND_CONV) c2;
    val th = CONV_RULE (c1 THENC c2) th
  in th end;

fun EXISTS_ABSORB dest_fun (r1,r2) =
  LEFT_EXISTS_ABSORB dest_fun r1 ORELSEC 
  RIGHT_EXISTS_ABSORB dest_fun r2;

fun FORMAT_RULES th = (th, ONCE_REWRITE_RULE [STAR_SYM,SEP_CONJ_SYM,SEP_DISJ_SYM] th);
val STAR_RULES = FORMAT_RULES SEP_EXISTS_ABSORB_STAR; 
val SEP_DISJ_RULES = FORMAT_RULES SEP_EXISTS_ABSORB_DISJ; 
val SEP_CONJ_RULES = FORMAT_RULES SEP_EXISTS_ABSORB_CONJ; 

val EXISTS_ABSORB_STAR = EXISTS_ABSORB dest_star STAR_RULES;
val EXISTS_ABSORB_SEP_DISJ = EXISTS_ABSORB dest_sep_disj SEP_DISJ_RULES;
val EXISTS_ABSORB_SEP_CONJ = EXISTS_ABSORB dest_sep_conj SEP_CONJ_RULES;

val SEP_EXISTS_ABSORB_CONV = 
  EXISTS_ABSORB_STAR ORELSEC
  EXISTS_ABSORB_SEP_DISJ ORELSEC
  EXISTS_ABSORB_SEP_CONJ;
 
val SEP_EXISTS_ss = conv2ssfrag 
  "SEP_EXISTS_ABSORB_CONV" SEP_EXISTS_ABSORB_CONV ``x:'a set -> bool``;


(* ----------------------------------------------------------------------------- *)
(* The main simpsets for set separation                                          *)
(* ----------------------------------------------------------------------------- *)

(* performs light simplifications *)

val sep_ss = rewrites 
  [SEP_DISJ_CLAUSES,SEP_CONJ_CLAUSES,SEP_cond_CLAUSES,
   SEP_FORALL_IGNORE,SEP_EXISTS_IGNORE,
   SEP_BIGDISJ_CLAUSES,SEP_BIGCONJ_CLAUSES,
   BIGSTAR_EMPTY,BIGSTAR_INSERT,BIGSTAR_ONE,BIGSTAR_UNION,
   F_STAR,emp_STAR];

(* performs more intrusive simplifications: pushes SEP_EXISTS and cond *)

val sep2_ss = 
  simpLib.merge_ss [SEP_EXISTS_ss,SEP_cond_ss,sep_ss,rewrites [STAR_ASSOC]];


(* ----------------------------------------------------------------------------- *)
(* Syntax related construstors and destructors                                   *)
(* ----------------------------------------------------------------------------- *)

open set_sepTheory

val STAR = prim_mk_const {Name="STAR",Thy="set_sep"};
val dest_STAR = dest_binop STAR (ERR"dest_STAR" "not a *");
val is_STAR = can dest_STAR;

fun list_dest_STAR tm =
  let val (v1,v2) = dest_STAR tm in list_dest_STAR v1 @ list_dest_STAR v2 end
  handle e => [tm];

fun mk_STAR(t1,t2) = (fst o dest_eq o concl o ISPECL [t1,t2]) STAR_def;

fun list_mk_STAR [] = raise ERR "list_mk_STAR" "Invalid argument"
  | list_mk_STAR [x] = x
  | list_mk_STAR (x::y::xs) = list_mk_STAR (mk_STAR(x,y)::xs);


(* ----------------------------------------------------------------------------- *)
(* Conversion for pushing a given term to the right                              *)
(* ----------------------------------------------------------------------------- *)

fun is_SEP_HIDE tm = (fst (dest_const tm) = "SEP_HIDE") handle e => false;

fun get_sep_domain tm = 
  if is_SEP_HIDE (fst (dest_comb tm)) 
  then snd (dest_comb tm) else fst (dest_comb tm) handle e => tm;

fun extract_domain tm =
  let val (h,q) = dest_comb tm in
    (if is_SEP_HIDE h then q else h) end handle e => tm;

fun mk_str_list_quote [] = [QUOTE "emp"] : (term frag) list
  | mk_str_list_quote (x::xs) =
     [QUOTE (foldl (fn (i,s) => s^"*i"^int_to_string i) ("i"^int_to_string x) xs)];

fun MOVE_OUT_TERM_CONV needle tm = let
  val xs = list_dest_STAR tm
  fun list_nums 0 xs = xs |
      list_nums i xs = list_nums (i-1) (i::xs)
  fun find_first n [] i = hd [] |
      find_first n (x::xs) i =
        if n = extract_domain x 
        then map (fn j => j + i) (list_nums (length xs) []) @ [i]
        else i :: find_first n xs (i+1)
  val from_list = mk_str_list_quote (list_nums (length(xs)) [])
  val to_list = mk_str_list_quote (find_first needle xs 1)
  in (REWRITE_CONV [STAR_ASSOC] THENC MOVE_STAR_CONV from_list to_list) tm end;

fun MOVE_OUT_CONV t tm = let
  val needle = Parse.parse_in_context (free_vars tm) t
  in MOVE_OUT_TERM_CONV needle tm end;

(* e.g. 

  MOVE_OUT_CONV `R a` ``R b 4w * R a (x + y) * ~S`` gives
    |- R b 4w * R a (x + y) * ~S = R b 4w * ~S * R a (x + y) : thm

  MOVE_OUT_CONV `R a` ``R b 4w * ~R a * ~S`` gives
    |- R b 4w * ~R a * ~S = R b 4w * ~S * ~R a : thm

*)

fun MOVE_OUT_LIST_TERM_CONV needles tm = let
  val xs = map (get_sep_domain) (list_dest_STAR tm)
  fun number (x,(i,xs)) = (i+1,xs @ [(x,i)])  
  val xs = snd (foldl number (1,[]) xs)
  fun find_and_delete x [] = hd []
    | find_and_delete x ((y,i)::ys) = 
       if x = y then (i,ys) else let
         val (j,zs) = find_and_delete x ys
       in (j,(y,i)::zs) end 
  fun fix (x,(xs,zs)) = let
    val (i,xs) = find_and_delete x xs
    in (xs,zs @ [i]) end
  val (left,zs) = foldl fix (xs,[]) needles
  fun f i = "x" ^ int_to_string i
  fun star_separate [] = "emp"
    | star_separate [x] = x
    | star_separate (x::xs) = x ^ "*" ^ star_separate xs
  val zs_str = star_separate (map f zs)
  val left_str = star_separate (map (f o snd) left)
  val to_list = if length(left) = 0 then zs_str else "("^left_str ^")*("^ zs_str^")"   
  val from_list = star_separate (map (f o snd) xs)
  val to_list = [QUOTE to_list]
  val from_list = [QUOTE from_list]
  in (REWRITE_CONV [STAR_ASSOC] THENC MOVE_STAR_CONV from_list to_list) tm end;
  
fun MOVE_OUT_LIST_CONV needles tm = let
  val ctxt = free_vars tm
  val needles = map (Parse.parse_in_context ctxt) needles
  in MOVE_OUT_LIST_TERM_CONV needles tm end;

(*

  val needles = [`g`,`rr`,`h 3`]
  val tm = ``g 1 * rttt 7  * ~k * h 3 4 * rr 6``
  MOVE_OUT_LIST_CONV needles tm

*)


end
