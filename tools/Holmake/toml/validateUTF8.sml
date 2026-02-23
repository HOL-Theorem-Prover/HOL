(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)
structure validateUTF8 :> validateUTF8 =
struct
  exception InvalidUtf8
  datatype state =
    START
  | MID_1_OF_3_E0 (* -> 0xA0-0xBF 0x80-0xBF *)
  | MID_1_OF_3_ED (* -> 0x80-0x9F 0x80-0xBF *)
  | MID_1_OF_4_F0 (* -> 0x90-0xBF 0x80-0xBF 0x80-0xBF *)
  | MID_1_OF_4_F4 (* -> 0x80-0x8F 0x80-0xBF 0x80-0xBF *)
  | TAIL_1 (* -> 0x80-0xBF *)
  | TAIL_2 (* -> 0x80-0xBF 0x80-0xBF *)
  | TAIL_3 (* -> 0x80-0xBF 0x80-0xBF 0x80-0xBF *)
  type 'strm validating_stream = 'strm * state
  fun mkValidatingStream strm = (strm, START)
  (*
   * 1-byte: 0aaa aaaa / U+0000 - U+007F
   * 2-byte: 110a aaaa 10bb bbbb / U+0080 - U+07FF / 0b00010 <= aaaaa
   * 3-byte: 1110 aaaa 10bb bbbb 10cc cccc / U+0800 - U+D7FF, U+E000 - U+FFFF / 0b100000 <= aaaa_bbbbbb < 0b1101_100000, 0b1110_000000 <= aaaa_bbbbbb
   * 4-byte: 1111 0aaa 10bb bbbb 10cc cccc 10dd dddd / U+10000 - U+10FFFF / 0b10000 <= aaa_bbbbbb < 0b100_010000
   *)
  fun nextState (START, c) =
        if c < #"\128" (* 0x80 *) then
          START
        else if c < #"\224" (* 0xE0 *) then
          if #"\194" (* 0xC2 *) <= c then TAIL_1 else raise InvalidUtf8
        else if c = #"\224" (* 0xE0 *) then
          MID_1_OF_3_E0
        else if c = #"\237" (* 0xED *) then
          MID_1_OF_3_ED
        else if c < #"\240" (* 0xF0 *) then
          TAIL_2
        else if c = #"\240" (* 0xF0 *) then
          MID_1_OF_4_F0
        else if c < #"\244" (* 0xF4 *) then
          TAIL_3
        else if c = #"\244" (* 0xF4 *) then
          MID_1_OF_4_F4
        else
          raise InvalidUtf8
    | nextState (TAIL_1, c1) =
        if #"\128" (* 0x80 *) <= c1 andalso c1 < #"\192" (* 0xC0 *) then START
        else raise InvalidUtf8
    | nextState (MID_1_OF_3_E0, c1) =
        if #"\160" (* 0xA0 *) <= c1 andalso c1 < #"\192" (* 0xC0 *) then TAIL_1
        else raise InvalidUtf8
    | nextState (MID_1_OF_3_ED, c1) =
        if #"\128" (* 0x80 *) <= c1 andalso c1 < #"\160" (* 0xA0 *) then TAIL_1
        else raise InvalidUtf8
    | nextState (TAIL_2, c1) =
        if #"\128" (* 0x80 *) <= c1 andalso c1 < #"\192" (* 0xC0 *) then TAIL_1
        else raise InvalidUtf8
    | nextState (MID_1_OF_4_F0, c1) =
        if #"\144" (* 0x90 *) <= c1 andalso c1 < #"\192" (* 0xC0 *) then TAIL_2
        else raise InvalidUtf8
    | nextState (TAIL_3, c1) =
        if #"\128" (* 0x80 *) <= c1 andalso c1 < #"\192" (* 0xC0 *) then TAIL_2
        else raise InvalidUtf8
    | nextState (MID_1_OF_4_F4, c1) =
        if #"\128" (* 0x80 *) <= c1 andalso c1 < #"\144" (* 0x90 *) then TAIL_2
        else raise InvalidUtf8
  fun go (START, NONE) = NONE
    | go (_, NONE) = raise InvalidUtf8
    | go (state, SOME (c, strm)) =
        SOME (c, (strm, nextState (state, c)))
  fun validatingReader getc (strm, state) =
    go (state, getc strm)
end
