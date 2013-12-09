(*****************************************************************************)
(* FILE          : sup-inf.sml                                               *)
(* DESCRIPTION   : SUP-INF method for deciding a subset of Presburger        *)
(*                 arithmetic (R.E.Shostak, JACM Vol.24 No.4 Pages 529-543)  *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 16th February 1993                                        *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 16th February 1993                                        *)
(*****************************************************************************)

structure Sup_Inf :> Sup_Inf =
struct
  open Arbint
  val op << = String.<
  infix <<


open Rationals;
open Lib; infix ##;
open Feedback;

fun failwith function = raise HOL_ERR{origin_structure = "Sup_Inf",
                                      origin_function = function,
                                      message = ""};


(*===========================================================================*)
(* SUP-INF algorithm                                                         *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Datatype for representing the bounds of a normalised expression           *)
(*---------------------------------------------------------------------------*)

datatype bound = Bound of rat * (string * rat) list
               | Max_bound of bound list
               | Min_bound of bound list
               | Pos_inf
               | Neg_inf;

(*---------------------------------------------------------------------------*)
(* Datatype for representing the bounds of an non-normalised expression      *)
(*---------------------------------------------------------------------------*)

datatype internal_bound = Ibound of bound
                        | Mult_ibound of rat * internal_bound
                        | Plus_ibound of internal_bound * internal_bound
                        | Max_ibound of internal_bound list
                        | Min_ibound of internal_bound list;

(*---------------------------------------------------------------------------*)
(* solve_ineqs :                                                             *)
(*    (int * (string * int) list) list ->                                    *)
(*    string ->                                                              *)
(*    ((rat * (string * rat) list) list * (rat * (string * rat) list) list)  *)
(*---------------------------------------------------------------------------*)

fun solve_ineqs ineqs var =
   if (null ineqs)
   then ([],[])
   else let val (const,bind) = hd ineqs
            and (restl,restr) = solve_ineqs (tl ineqs) var
        in  (let val i = assoc var bind
                 val const' = Rat (const,(~i))
                 and bind' = map (I ## (fn n => Rat (n,(~i))))
                                (filter (fn (name,_) => not (name = var)) bind)
             in  if (i < zero)
                 then (((const',bind')::restl),restr)
                 else (restl,((const',bind')::restr))
             end)
            handle _ => (restl,restr)
        end;

(*---------------------------------------------------------------------------*)
(* UPPER : (int * (string * int) list) list -> string -> bound               *)
(*---------------------------------------------------------------------------*)

fun UPPER s x =
   let val uppers = fst (solve_ineqs s x)
   in  if (null uppers)
       then Pos_inf
       else if (null (tl uppers))
            then Bound (hd uppers)
            else Min_bound (map Bound uppers)
   end;

(*---------------------------------------------------------------------------*)
(* LOWER : (int * (string * int) list) list -> string -> bound               *)
(*---------------------------------------------------------------------------*)

fun LOWER s x =
   let val lowers = snd (solve_ineqs s x)
   in  if (null lowers)
       then Neg_inf
       else if (null (tl lowers))
            then Bound (hd lowers)
            else Max_bound (map Bound lowers)
   end;

(*---------------------------------------------------------------------------*)
(* SIMP_mult : rat -> bound -> bound                                         *)
(*---------------------------------------------------------------------------*)

fun SIMP_mult r (Bound (const,bind)) =
       Bound (rat_mult r const,map (I ## (rat_mult r)) bind)
  | SIMP_mult r (Max_bound bl) =
       (if ((Numerator r) < zero)
        then (Min_bound (map (SIMP_mult r) bl))
        else (Max_bound (map (SIMP_mult r) bl)))
  | SIMP_mult r (Min_bound bl) =
       (if ((Numerator r) < zero)
        then (Max_bound (map (SIMP_mult r) bl))
        else (Min_bound (map (SIMP_mult r) bl)))
  | SIMP_mult r Pos_inf = if ((Numerator r) < zero) then Neg_inf else Pos_inf
  | SIMP_mult r Neg_inf = if ((Numerator r) < zero) then Pos_inf else Neg_inf;

(*---------------------------------------------------------------------------*)
(* sum_bindings :                                                            *)
(*    (string * rat) list -> (string * rat) list -> (string * rat) list      *)
(*---------------------------------------------------------------------------*)

fun sum_bindings bind1 bind2 =
   if (null bind1) then bind2
   else if (null bind2) then bind1
   else (let val (name1:string,coeff1) = hd bind1
             and (name2,coeff2) = hd bind2
         in  if (name1 = name2) then
                (let val coeff = rat_plus coeff1 coeff2
                     and bind = sum_bindings (tl bind1) (tl bind2)
                 in  if ((Numerator coeff) = zero)
                     then bind
                     else (name1,coeff)::bind
                 end)
             else if (name1 << name2) then
                (name1,coeff1)::(sum_bindings (tl bind1) bind2)
             else (name2,coeff2)::(sum_bindings bind1 (tl bind2))
         end);

(*---------------------------------------------------------------------------*)
(* SIMP_plus : bound -> bound -> bound                                       *)
(*---------------------------------------------------------------------------*)

fun SIMP_plus (Bound (const1,bind1)) (Bound (const2,bind2)) =
       Bound (rat_plus const1 const2,sum_bindings bind1 bind2)
  | SIMP_plus (b1 as Bound _) (Max_bound bl) =
       Max_bound (map (SIMP_plus b1) bl)
  | SIMP_plus (b1 as Bound _) (Min_bound bl) =
       Min_bound (map (SIMP_plus b1) bl)
  | SIMP_plus (Bound _) Pos_inf = Pos_inf
  | SIMP_plus (Bound _) Neg_inf = Neg_inf
  | SIMP_plus (Max_bound bl) b2 = Max_bound (map (fn b => SIMP_plus b b2) bl)
  | SIMP_plus (Min_bound bl) b2 = Min_bound (map (fn b => SIMP_plus b b2) bl)
  | SIMP_plus Pos_inf Pos_inf = Pos_inf
  | SIMP_plus Pos_inf Neg_inf = failwith "SIMP_plus"
  | SIMP_plus (b1 as Pos_inf) b2 = SIMP_plus b2 b1
  | SIMP_plus Neg_inf Neg_inf = Neg_inf
  | SIMP_plus Neg_inf Pos_inf = failwith "SIMP_plus"
  | SIMP_plus (b1 as Neg_inf) b2 = SIMP_plus b2 b1;

(*---------------------------------------------------------------------------*)
(* SIMP : internal_bound -> bound                                            *)
(*---------------------------------------------------------------------------*)

fun SIMP (Ibound b) = b
  | SIMP (Mult_ibound (r,ib')) = SIMP_mult r (SIMP ib')
  | SIMP (Plus_ibound (ib1,ib2)) = SIMP_plus (SIMP ib1) (SIMP ib2)
  | SIMP (Max_ibound ibl) = Max_bound (map SIMP ibl)
  | SIMP (Min_ibound ibl) = Min_bound (map SIMP ibl);

(*---------------------------------------------------------------------------*)
(* SUPP : (string * bound) -> bound                                          *)
(* INFF : (string * bound) -> bound                                          *)
(*---------------------------------------------------------------------------*)

fun SUPP (x,y) =
   case y
   of (Bound (_,[])) => y
    | Pos_inf => y
    | Neg_inf => y
    | (Min_bound bl) => (Min_bound (map (fn y => SUPP (x,y)) bl))
    | (Bound (const,bind)) =>
         (let val b = (assoc x bind) handle NOT_FOUND => rat_zero
              and bind' = filter (fn p => not (fst p = x)) bind
          in  if ((null bind') andalso (const = rat_zero) andalso
                  (b = rat_one))
              then Pos_inf
              else let val b' = rat_minus rat_one b
                   in  if (Numerator b' < zero) then Pos_inf
                       else if (Numerator b' > zero) then
                          (Bound (rat_div const b',
                                  map (I ## (fn r => rat_div r b')) bind'))
                       else if (not (null bind')) then Pos_inf
                            else if (Numerator const < zero) then Neg_inf
                            else Pos_inf
                   end
          end)
    | _ => failwith "SUPP";

fun INFF (x,y) =
   case y
   of (Bound (_,[])) => y
    | Pos_inf => y
    | Neg_inf => y
    | (Max_bound bl) => (Max_bound (map (fn y => INFF (x,y)) bl))
    | (Bound (const,bind)) =>
         (let val b = (assoc x bind) handle NOT_FOUND => rat_zero
              and bind' = filter (fn p => not (fst p = x)) bind
          in  if ((null bind') andalso (const = rat_zero) andalso
                  (b = rat_one))
              then Neg_inf
              else let val b' = rat_minus rat_one b
                   in  if (Numerator b' < zero) then Neg_inf
                       else if (Numerator b' > zero) then
                          (Bound (rat_div const b',
                                  map (I ## (fn r => rat_div r b')) bind'))
                       else if (not (null bind')) then Neg_inf
                            else if (Numerator const > zero) then Pos_inf
                            else Neg_inf
                   end
          end)
    | _ => failwith "INFF";

(*---------------------------------------------------------------------------*)
(* occurs_in_bound : string -> bound -> bool                                 *)
(*---------------------------------------------------------------------------*)

fun occurs_in_bound v (Bound (_,bind)) = Lib.mem v (map fst bind)
  | occurs_in_bound v (Max_bound bl) =
       itlist (fn x => fn y => x orelse y) (map (occurs_in_bound v) bl) false
  | occurs_in_bound v (Min_bound bl) =
       itlist (fn x => fn y => x orelse y) (map (occurs_in_bound v) bl) false
  | occurs_in_bound _ _ = false;

(*---------------------------------------------------------------------------*)
(* occurs_in_ibound : string -> internal_bound -> bool                       *)
(*---------------------------------------------------------------------------*)

fun occurs_in_ibound v (Ibound b) = occurs_in_bound v b
  | occurs_in_ibound v (Mult_ibound (_,ib')) = occurs_in_ibound v ib'
  | occurs_in_ibound v (Plus_ibound (ib1,ib2)) =
       (occurs_in_ibound v ib1) orelse (occurs_in_ibound v ib2)
  | occurs_in_ibound v (Max_ibound ibl) =
       itlist (fn x => fn y => x orelse y) (map (occurs_in_ibound v) ibl) false
  | occurs_in_ibound v (Min_ibound ibl) =
       itlist (fn x => fn y => x orelse y) (map (occurs_in_ibound v) ibl)
                                                                         false;

(*---------------------------------------------------------------------------*)
(* SUP : (int * (string * int) list) list ->                                 *)
(*       (bound * (string list)) ->                                          *)
(*       internal_bound                                                      *)
(* INF : (int * (string * int) list) list ->                                 *)
(*       (bound * (string list)) ->                                          *)
(*       internal_bound                                                      *)
(*---------------------------------------------------------------------------*)

fun SUP s (J,H) =
   case J
   of (Bound (_,[])) => Ibound J
    | Pos_inf => Ibound J
    | Neg_inf => Ibound J
    | (Min_bound bl) => Min_ibound (map (fn j => SUP s (j,H)) bl)
    | (Bound (const,(rv as (v,r))::bind')) =>
         (if ((const = rat_zero) andalso (null bind'))
          then (if (r = rat_one) then
                   (if (Lib.mem v H)
                    then Ibound J
                    else let val Q = UPPER s v
                             val Z = SUP s (Q,Lib.union H [v])
                         in  Ibound (SUPP (v,SIMP Z))
                         end)
                else if (Numerator r < zero) then
                   (Mult_ibound (r,INF s (Bound (rat_zero,[(v,rat_one)]),H)))
                else Mult_ibound (r,SUP s (Bound (rat_zero,[(v,rat_one)]),H))
               )
          else let val B' = SUP s (Bound (const,bind'),Lib.union H [v])
                   and rvb = Bound (rat_zero,[rv])
               in  if (occurs_in_ibound v B')
                   then let val J' = SIMP (Plus_ibound (Ibound rvb,B'))
                        in  SUP s (J',H)
                        end
                   else Plus_ibound (SUP s (rvb,H),B')
               end)
    | _ => failwith "SUP"

and INF s (J,H) =
   case J
   of (Bound (_,[])) => Ibound J
    | Pos_inf => Ibound J
    | Neg_inf => Ibound J
    | (Max_bound bl) => Max_ibound (map (fn j => INF s (j,H)) bl)
    | (Bound (const,(rv as (v,r))::bind')) =>
         (if ((const = rat_zero) andalso (null bind'))
          then (if (r = rat_one) then
                   (if (Lib.mem v H)
                    then Ibound J
                    else let val Q = LOWER s v
                             val Z = INF s (Q,Lib.union H [v])
                         in  Ibound (INFF (v,SIMP Z))
                         end)
                else if (Numerator r < zero) then
                   (Mult_ibound (r,SUP s (Bound (rat_zero,[(v,rat_one)]),H)))
                else Mult_ibound (r,INF s (Bound (rat_zero,[(v,rat_one)]),H))
               )
          else let val B' = INF s (Bound (const,bind'),Lib.union H [v])
                   and rvb = Bound (rat_zero,[rv])
               in  if (occurs_in_ibound v B')
                   then let val J' = SIMP (Plus_ibound (Ibound rvb,B'))
                        in  INF s (J',H)
                        end
                   else Plus_ibound (INF s (rvb,H),B')
               end)
    | _ => failwith "INF";

(*---------------------------------------------------------------------------*)
(* eval_max_bound : bound list -> bound                                      *)
(*---------------------------------------------------------------------------*)

fun eval_max_bound bl =
   if (null bl) then failwith "eval_max_bound"
   else if (null (tl bl)) then (hd bl)
   else let val b = hd bl
            and max = eval_max_bound (tl bl)
        in  case (b,max)
            of (Pos_inf,_) => Pos_inf
             | (_,Pos_inf) => Pos_inf
             | (Neg_inf,_) => max
             | (_,Neg_inf) => b
             | (Bound (r1,[]),Bound (r2,[])) =>
                  (if (Numerator (rat_minus r1 r2) < zero) then max else b)
             | _ => failwith "eval_max_bound"
        end;

(*---------------------------------------------------------------------------*)
(* eval_min_bound : bound list -> bound                                      *)
(*---------------------------------------------------------------------------*)

fun eval_min_bound bl =
   if (null bl) then failwith "eval_min_bound"
   else if (null (tl bl)) then (hd bl)
   else let val b = hd bl
            and min = eval_min_bound (tl bl)
        in  case (b,min)
            of (Pos_inf,_) => min
             | (_,Pos_inf) => b
             | (_,Neg_inf) => Neg_inf
             | (Neg_inf,_) => Neg_inf
             | (Bound (r1,[]),Bound (r2,[])) =>
                  (if (Numerator (rat_minus r1 r2) < zero) then b else min)
             | _ => failwith "eval_min_bound"
        end;

(*---------------------------------------------------------------------------*)
(* eval_bound : bound -> bound                                               *)
(*---------------------------------------------------------------------------*)

fun eval_bound (b as Bound (_,[])) = b
  | eval_bound (Max_bound bl) = eval_max_bound (map eval_bound bl)
  | eval_bound (Min_bound bl) = eval_min_bound (map eval_bound bl)
  | eval_bound (b as Pos_inf) = b
  | eval_bound (b as Neg_inf) = b
  | eval_bound _ = failwith "eval_bound";

(*---------------------------------------------------------------------------*)
(* SUP_INF :                                                                 *)
(*    (int * (string * int) list) list -> (string * bound * bound) list      *)
(*---------------------------------------------------------------------------*)

fun SUP_INF set =
   let fun vars_of_coeffs coeffsl =
          Lib.mk_set (flatten (map ((map fst) o snd) coeffsl))
       val vars = vars_of_coeffs set
       and eval = eval_bound o SIMP
       fun make_bound v = Bound (rat_zero,[(v,rat_one)])
   in  map (fn v => let val b = make_bound v
                    in  (v,eval (INF set (b,[])),eval (SUP set (b,[])))
                    end) vars
   end;

end
