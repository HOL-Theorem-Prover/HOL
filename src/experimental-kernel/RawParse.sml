structure RawParse :> RawParse =
struct

open Term Feedback

val ERR = mk_HOL_ERR "RawParse"

datatype tok = bslash | fslash | colon | id of int | lparen | rparen
open StringCvt

fun readtok (c : (char, cs) reader) cs0 = let
  val cs = skipWS c cs0
  val intread = Int.scan DEC c
in
  case c cs of
    NONE => NONE
  | SOME (#"|",cs') => SOME (bslash,cs')
  | SOME (#"/",cs') => SOME (fslash,cs')
  | SOME (#":",cs') => SOME ( colon,cs')
  | SOME (#"(",cs') => SOME (lparen,cs')
  | SOME (#")",cs') => SOME (rparen,cs')
  | SOME c => (case intread cs of
                 NONE => NONE
               | SOME (i,cs') => SOME(id i, cs'))
end

(* SLR parser for grammar

     T   ::= tm $
     tm  ::= '|' [id] tm    -- abstraction
     tm  ::= '/' [id] tm    -- type abstraction
     tm  ::= ':' [id] tm    -- type combination ([id] refers to type which is the argument)
     tm  ::= tmc
     tmc ::= tmc tmb        -- combination
     tmc ::= tmb
     tmb ::= [id]
     tmb ::= '(' tm ')'
*)

datatype stk_item = TYLAM of hol_type | TYC of hol_type | LAM of term | C of term | BK | Start

fun parse tyv tmv c cs0 = let
  fun adv cs = case readtok c cs of NONE => (NONE, cs)
                                  | SOME (t, cs') => (SOME t, cs')
  fun new_bv i stk = LAM (Vector.sub(tmv,i)) :: stk
  fun new_btyv i stk = TYLAM (Vector.sub(tyv,i)) :: stk
  fun new_tyarg i stk = TYC (Vector.sub(tyv,i)) :: stk
  and parse_term stk cur =
      case cur of
        (NONE,_) => NONE
      | (SOME bslash, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_bv i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME fslash, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_btyv i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME colon, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_tyarg i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME (id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
      | _ => raise ERR "parse_term" "impossible"
  and reduce_tmb stk tm cur =
      case stk of
        [] => NONE
      | C t :: rest => parse_tmc (C (mk_comb(t,tm)) :: rest) cur
      | TYC ty :: rest => parse_tmc (C (mk_tycomb(tm,ty)) :: rest) cur
      | _ => parse_tmc (C tm :: stk) cur
  and parse_tmc stk cur =
      case cur of
        (NONE, _) => reduce_tm stk cur
      | (SOME(id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME rparen, cs') => reduce_tm stk (adv cs')
      | _ => raise ERR "parse_tmc" "impossible"
  and reduce_tm stk cur =
      case stk of
        C t :: BK :: rest => reduce_tmb rest t cur
      | C t :: Start :: rest => SOME (t, #2 cur)
      | C t :: LAM bv :: rest => reduce_tm (C (mk_abs(bv,t)) :: rest) cur
      | C t :: TYLAM bv :: rest => reduce_tm (C (mk_tyabs(bv,t)) :: rest) cur
      | _ => raise ERR "reduce_term" "impossible"
in
  parse_term [Start] (adv cs0)
end

fun readTerm tyv tmv s = valOf (scanString (parse tyv tmv) s)

datatype grav = Top | CombL | CombR
datatype ppaction = Brk | Tm of term * grav | Ty of hol_type * grav | Stg of string

fun pp_raw_term tymap map t = let
  fun doit acc actlist =
      case actlist of
        [] => String.concat (List.rev acc)
      | Brk :: rest => doit (" "::acc) rest
      | Stg s :: rest => doit (s::acc) rest
      | Ty (t,g) :: rest => let
        in
          doit (Int.toString (tymap t)::acc) rest
          handle e => ((*print "\npp_raw_term failed to find type id # for type ";
                       print (Type.type_to_string t);
                       print "\n";*)
                       raise e)
        end
      | Tm (t,g) :: rest => let
        in
          if is_var t orelse is_const t then
             doit (Int.toString (map t)::acc) rest
          else if is_comb t then let
              val (Rator,Rand) = dest_comb t
            in
              if g = CombR then
                doit acc
                     (Stg "(" :: Tm(Rator,CombL) :: Brk :: Tm(Rand,CombR) ::
                      Stg ")" :: rest)
              else
                doit acc (Tm(Rator,CombL) :: Brk :: Tm(Rand,CombR) :: rest)
            end
          else if is_abs t then let
              val (bv, body) = dest_abs t
              val core = [Stg "|", Tm(bv, Top), Brk, Tm(body, Top)]
            in
              if g <> Top then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
          else if is_tycomb t then let
              val (Rator,Rand) = dest_tycomb t
              val core = [Stg ":", Ty(Rand,CombL), Brk, Tm(Rator,CombR)]
            in
              if g = CombR then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
          else if is_tyabs t then let
              val (bv, body) = dest_tyabs t
              val core = [Stg "/", Ty(bv, Top), Brk, Tm(body, Top)]
            in
              if g <> Top then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
          else raise ERR "pp_raw_term" "unrecognized term"
        end
in
  doit [] [Tm(t,Top)]
end



end;
