(*****************************************************************************)
(* Test script for encoding using finite maps.                               *)
(*****************************************************************************)

load "acl2encodeLib";

val tf_def = Define `tf (x : int |-> int) = if 0 IN FDOM x then x ' 0 else 0`;

val oneone_int = ONEONE_ENC_THM ``:int``;

val _ = acl2encodeLib.translate_conditional_function [(``tf``, "test_tf")] [oneone_int] tf_def handle e => acl2encodeLib.Raise e;