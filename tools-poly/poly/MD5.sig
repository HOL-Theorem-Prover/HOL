(* ========================================================================= *)
(* MD5 cryptographic hashing in SML                                          *)
(* Copyright (C) 2001 Daniel Wang. All rights reserved.                      *)
(* Derived from the RSA Data Security, Inc. MD5 Message-Digest Algorithm.    *)
(* ========================================================================= *)

signature MD5 =
sig

  type md5state

  val init : md5state
  val update : (md5state * Word8Vector.vector) -> md5state
  val final : md5state -> Word8Vector.vector
  val toHexString : Word8Vector.vector -> string
  val toBase64String : Word8Vector.vector -> string

end
