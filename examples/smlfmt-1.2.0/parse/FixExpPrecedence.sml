(** Copyright (c) 2020-2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** Identifies issues like parsing `e1 andalso e2 orelse e3`:
  *
  *   e1 andalso (e2 orelse e3)   INCORRECT
  *   (e1 andalso e2) orelse e3   CORRECT
  *
  * In this example, according to the Definition, `andalso` expressions have
  * higher precedence than `orelse`.
  *
  * At first, this might look just like a normal issue of infix-operator
  * precedence. But it's quite different, because it applies to any two
  * adjacent forms where one ends with an <exp> and the other
  * begins with an <exp>.
  *
  * Here are some examples:
  *
  *   ---- SOURCE ----                   ---- CORRECT PARSE ----
  *   raise e handle ...                 raise (e handle ...)
  *   if e1 then e2 else e3 handle ...   if e1 then e2 else (e3 handle ...)
  *   e1 orelse e2 handle ...            (e1 orelse e2) handle ...
  *   while e1 do e2 : ty                while e1 do (e2 : ty)
  *
  * The parser (Parser.sml) operates left-to-right, so to fix improperly
  * parsed expressions, we just need to compare the root node with its
  * right-child. This is what `maybeRotateLeft` does.
  *
  * For example:
  *
  *   maybeRotateLeft (AST(e1 orelse e2 handle ...))
  *     ==> AST((e1 orelse e2) handle ...)
  *
  *)
structure FixExpPrecedence:
sig
  val maybeRotateLeft: Ast.Exp.exp -> Ast.Exp.exp
end =
struct


  (** We could handle all possible pairs of expressions, but this would be
    * annoying. Instead, we just need to provide three pieces of information
    * for each expression:
    *
    *   1. Precedence level? (We'll use a total order)
    *   2. Its left-side expression (if there is one) and how to replace it
    *   with some other expression.
    *   3. Its right-side expression (if there is one) and how to replace it
    *   with some other expression.
    *
    * This gives us a pretty simple and straightforward implementation of
    * `maybeRotateLeft`!
    *)

  type replacer = {exp: Ast.Exp.exp, replaceWith: Ast.Exp.exp -> Ast.Exp.exp}

  datatype info =
    F of {prec: int, left: replacer option, right: replacer option}


  fun getInfo e =
    let
      open Ast.Exp
    in
      case e of
        Typed {exp, colon, ty} =>
          let
            fun leftReplaceWith e = Typed {exp = e, colon = colon, ty = ty}
          in
            F { prec = 10
              , left = SOME {exp = exp, replaceWith = leftReplaceWith}
              , right = NONE
              }
          end

      | Andalso {left, andalsoo, right} =>
          let
            fun leftReplaceWith e =
              Andalso {left = e, andalsoo = andalsoo, right = right}
            fun rightReplaceWith e =
              Andalso {left = left, andalsoo = andalsoo, right = e}
          in
            F { prec = 9
              , left = SOME {exp = left, replaceWith = leftReplaceWith}
              , right = SOME {exp = right, replaceWith = rightReplaceWith}
              }
          end

      | Orelse {left, orelsee, right} =>
          let
            fun leftReplaceWith e =
              Orelse {left = e, orelsee = orelsee, right = right}
            fun rightReplaceWith e =
              Orelse {left = left, orelsee = orelsee, right = e}
          in
            F { prec = 8
              , left = SOME {exp = left, replaceWith = leftReplaceWith}
              , right = SOME {exp = right, replaceWith = rightReplaceWith}
              }
          end

      | Handle {exp, handlee, elems, delims, optbar} =>
          let
            fun leftReplaceWith e =
              Handle
                { exp = e
                , handlee = handlee
                , elems = elems
                , delims = delims
                , optbar = optbar
                }
          in
            F { prec = 7
              , left = SOME {exp = exp, replaceWith = leftReplaceWith}
              , right = NONE
              }
          end

      | Raise {raisee, exp} =>
          let
            fun replaceRightWith e = Raise {raisee = raisee, exp = e}
          in
            F { prec = 6
              , left = NONE
              , right = SOME {exp = exp, replaceWith = replaceRightWith}
              }
          end

      | IfThenElse {iff, exp1, thenn, exp2, elsee, exp3} =>
          let
            fun replaceRightWith e =
              IfThenElse
                { iff = iff
                , exp1 = exp1
                , thenn = thenn
                , exp2 = exp2
                , elsee = elsee
                , exp3 = e
                }
          in
            F { prec = 5
              , left = NONE
              , right = SOME {exp = exp3, replaceWith = replaceRightWith}
              }
          end

      | While {whilee, exp1, doo, exp2} =>
          let
            fun replaceRightWith e =
              While {whilee = whilee, exp1 = exp1, doo = doo, exp2 = e}
          in
            F { prec = 4
              , left = NONE
              , right = SOME {exp = exp2, replaceWith = replaceRightWith}
              }
          end

      | _ => F {prec = 0, left = NONE, right = NONE}
    end


  fun maybeRotateLeft e =
    let
      val F {prec = rootPrecedence, right, ...} = getInfo e
    in
      case right of
        NONE => e
      | SOME {exp = rootRight, replaceWith = rootReplaceRightWith} =>
          let
            val F {prec = rightPrecedence, left, ...} = getInfo rootRight
          in
            case left of
              NONE => e
            | SOME {exp = rightLeft, replaceWith = rightReplaceLeftWith} =>
                if rootPrecedence > rightPrecedence then
                  rightReplaceLeftWith (rootReplaceRightWith rightLeft)
                else
                  e
          end
    end


end
