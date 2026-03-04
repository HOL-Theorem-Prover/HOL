(*
 * Copyright (c) 2024 ARATA Mizuki
 * This file is part of sml-toml.
 * See copyrights/sml-toml for copyright information.
 *)
signature validateUTF8 =
sig
  exception InvalidUtf8
  type 'strm validating_stream
  val mkValidatingStream: 'strm -> 'strm validating_stream
  val validatingReader: (char, 'strm) StringCvt.reader
                        -> (char, 'strm validating_stream) StringCvt.reader
end
