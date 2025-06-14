(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure ParseAnnotations:
sig
  (* see DecAnn in MLBAst *)
  type annotations = MLBToken.t Seq.t
  val modifyAllows: AstAllows.t -> annotations -> AstAllows.t
end =
struct

  type annotations = MLBToken.t Seq.t


  fun allowSuccessorML a b =
    AstAllows.make
      { topExp = AstAllows.topExp a
      , optBar = b
      , recordPun = b
      , orPat = b
      , extendedText = b
      , sigWithtype = b
      }


  fun allowOptBar a b =
    AstAllows.make
      { optBar = b
      , topExp = AstAllows.topExp a
      , recordPun = AstAllows.recordPun a
      , orPat = AstAllows.orPat a
      , extendedText = AstAllows.extendedText a
      , sigWithtype = AstAllows.sigWithtype a
      }


  fun allowRecordPunExps a b =
    AstAllows.make
      { optBar = AstAllows.optBar a
      , topExp = AstAllows.topExp a
      , recordPun = b
      , orPat = AstAllows.orPat a
      , extendedText = AstAllows.extendedText a
      , sigWithtype = AstAllows.sigWithtype a
      }


  fun allowOrPats a b =
    AstAllows.make
      { optBar = AstAllows.optBar a
      , topExp = AstAllows.topExp a
      , recordPun = AstAllows.recordPun a
      , orPat = b
      , extendedText = AstAllows.extendedText a
      , sigWithtype = AstAllows.sigWithtype a
      }


  fun allowExtendedTextConsts a b =
    AstAllows.make
      { optBar = AstAllows.optBar a
      , topExp = AstAllows.topExp a
      , recordPun = AstAllows.recordPun a
      , orPat = AstAllows.orPat a
      , extendedText = b
      , sigWithtype = AstAllows.sigWithtype a
      }

  fun allowSigWithtype a b =
    AstAllows.make
      { optBar = AstAllows.optBar a
      , topExp = AstAllows.topExp a
      , recordPun = AstAllows.recordPun a
      , orPat = AstAllows.orPat a
      , extendedText = AstAllows.extendedText a
      , sigWithtype = b
      }


  fun getElems ann =
    let
      val src = MLBToken.getSource ann

      (* this strips the initial and final `"` characters from the string *)
      val str = CharVector.tabulate (Source.length src - 2, fn i =>
        Source.nth src (i + 1))
    in
      String.tokens Char.isSpace str
    end


  fun applyGeneralAnn (allows, ann) =
    case getElems ann of
      ["allowSuccessorML", "true"] => allowSuccessorML allows true
    | ["allowSuccessorML", "false"] => allowSuccessorML allows false
    | _ => allows


  fun applySpecificAnn (allows, ann) =
    case getElems ann of
      ["allowOptBar", "true"] => allowOptBar allows true
    | ["allowOptBar", "false"] => allowOptBar allows false
    | ["allowOrPats", "true"] => allowOrPats allows true
    | ["allowOrPats", "false"] => allowOrPats allows false
    | ["allowRecordPunExps", "true"] => allowRecordPunExps allows true
    | ["allowRecordPunExps", "false"] => allowRecordPunExps allows false
    | ["allowExtendedTextConsts", "true"] => allowExtendedTextConsts allows true
    | ["allowExtendedTextConsts", "false"] =>
        allowExtendedTextConsts allows false
    | ["allowSigWithtype", "true"] => allowSigWithtype allows true
    | ["allowSigWithtype", "false"] => allowSigWithtype allows false
    | _ => allows


  fun modifyAllows allows anns =
    Seq.iterate applySpecificAnn (Seq.iterate applyGeneralAnn allows anns) anns

end
