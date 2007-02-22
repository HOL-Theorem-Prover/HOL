structure RawParse :> RawParse =
struct

open Term Feedback

datatype tok = bslash | id of int | lparen | rparen
open StringCvt

fun readtok (c : (char, cs) reader) cs0 = let
  val cs = skipWS c cs0
  val intread = Int.scan DEC c
in
  case c cs of
    NONE => NONE
  | SOME (#"|",cs') => SOME (bslash,cs')
  | SOME (#"(",cs') => SOME (lparen,cs')
  | SOME (#")",cs') => SOME (rparen,cs')
  | SOME c => (case intread cs of
                 NONE => NONE
               | SOME (i,cs') => SOME(id i, cs'))
end

(* SLR parser for grammar

     T   ::= tm $
     tm  ::= '|' [id] tm
     tm  ::= tmc
     tmc ::= tmc tmb
     tmc ::= tmb
     tmb ::= [id]
     tmb ::= '(' tm ')'
*)

datatype stk_item = LAM of term | C of term | BK | Start

fun parse tmv c cs0 = let
  fun adv cs = case readtok c cs of NONE => (NONE, cs)
                                  | SOME (t, cs') => (SOME t, cs')
  fun new_bv i stk = LAM (Vector.sub(tmv,i)) :: stk
  fun parse_term stk cur =
      case cur of
        (NONE,_) => NONE
      | (SOME bslash, cs') => let
        in
          case readtok c cs' of
            NONE => NONE
          | SOME (id i, cs'') => parse_term (new_bv i stk) (adv cs'')
          | _ => NONE
        end
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME (id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
  and reduce_tmb stk tm cur =
      case stk of
        [] => NONE
      | C t :: rest => parse_tmc (C (mk_comb(t,tm)) :: rest) cur
      | _ => parse_tmc (C tm :: stk) cur
  and parse_tmc stk cur =
      case cur of
        (NONE, _) => reduce_tm stk cur
      | (SOME(id i), cs') => reduce_tmb stk (Vector.sub(tmv,i)) (adv cs')
      | (SOME lparen, cs') => parse_term (BK :: stk) (adv cs')
      | (SOME rparen, cs') => reduce_tm stk (adv cs')
  and reduce_tm stk cur =
      case stk of
        C t :: BK :: rest => reduce_tmb rest t cur
      | C t :: Start :: rest => SOME (t, #2 cur)
      | C t :: LAM bv :: rest => reduce_tm (C (mk_abs(bv,t)) :: rest) cur
in
  parse_term [Start] (adv cs0)
end

fun readTerm tmv s = valOf (scanString (parse tmv) s)

datatype grav = Top | CombL | CombR
datatype ppaction = Brk | Tm of term * grav | Stg of string

fun pp_raw_term map t = let
  fun doit acc actlist =
      case actlist of
        [] => String.concat (List.rev acc)
      | Brk :: rest => doit (" "::acc) rest
      | Stg s :: rest => doit (s::acc) rest
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
          else let
              val (bv, body) = dest_abs t
              val core = [Stg "|", Tm(bv, Top), Brk, Tm(body, Top)]
            in
              if g <> Top then
                doit acc ((Stg "(" :: core) @ (Stg ")" :: rest))
              else
                doit acc (core @ rest)
            end
        end
in
  doit [] [Tm(t,Top)]
end



end;
