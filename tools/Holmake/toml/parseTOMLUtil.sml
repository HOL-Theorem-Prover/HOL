(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)
structure parseTOMLUtil =
struct
  structure StringExt =
  struct
    fun implodeRev accum =
      String.implode (List.rev accum)
    open String (* There may be a built-in String.implodeRev *)
  end
  val implodeRev = StringExt.implodeRev
  structure E = TOMLerror
  (* type pos = { line : int, column : int } (* 0-based line and 0-based column (in bytes) *) *)
  type path = string list
  type key = string list (* non-empty list *)
  fun digitToInt c = Char.ord c - Char.ord #"0"
  (*: val revAppendUtf8 : word * char list -> char list *)
  fun revAppendUtf8 (i, accum) =
    if i < 0wx80 then (* 7-bit *)
      Char.chr (Word.toInt i) :: accum
    else if i < 0wx800 then (* 11-bit *)
      let
        val u0 = Word.orb (0wxC0, Word.>> (i, 0w6))
        val u1 = Word.orb (0wx80, Word.andb (i, 0wx3F))
      in
        Char.chr (Word.toInt u1) :: Char.chr (Word.toInt u0) :: accum
      end
    else if i < 0wx10000 then (* 16-bit *)
      if 0wxD800 <= i andalso i < 0wxE000 then
        raise E.ParseError E.INVALID_UNICODE_SCALAR
      else
        let
          val u0 = Word.orb (0wxE0, Word.>> (i, 0w12))
          val u1 = Word.orb (0wx80, Word.andb (Word.>> (i, 0w6), 0wx3F))
          val u2 = Word.orb (0wx80, Word.andb (i, 0wx3F))
        in
          Char.chr (Word.toInt u2) :: Char.chr (Word.toInt u1)
          :: Char.chr (Word.toInt u0) :: accum
        end
    else if i < 0wx110000 then (* 21-bit *)
      let
        val u0 = Word.orb (0wxF0, Word.>> (i, 0w18))
        val u1 = Word.orb (0wx80, Word.andb (Word.>> (i, 0w12), 0wx3F))
        val u2 = Word.orb (0wx80, Word.andb (Word.>> (i, 0w6), 0wx3F))
        val u3 = Word.orb (0wx80, Word.andb (i, 0wx3F))
      in
        Char.chr (Word.toInt u3) :: Char.chr (Word.toInt u2)
        :: Char.chr (Word.toInt u1) :: Char.chr (Word.toInt u0) :: accum
      end
    else
      raise E.ParseError E.INVALID_UNICODE_SCALAR
  fun isValidDate (_, 1, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (year, 2, 29) =
        Int.rem (year, 4) = 0
        andalso (Int.rem (year, 100) <> 0 orelse Int.rem (year, 400) = 0)
    | isValidDate (_, 2, mday) = 1 <= mday andalso mday <= 28
    | isValidDate (_, 3, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (_, 4, mday) = 1 <= mday andalso mday <= 30
    | isValidDate (_, 5, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (_, 6, mday) = 1 <= mday andalso mday <= 30
    | isValidDate (_, 7, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (_, 8, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (_, 9, mday) = 1 <= mday andalso mday <= 30
    | isValidDate (_, 10, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (_, 11, mday) = 1 <= mday andalso mday <= 30
    | isValidDate (_, 12, mday) = 1 <= mday andalso mday <= 31
    | isValidDate (_, _, _) = false
end
