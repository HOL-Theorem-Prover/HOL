(* ===================================================================== *)
(* LIBRARY       : mutual                                                *)
(* VERSION       : 1.0                                                   *)
(* FILE          : mk_mutual_lib.sml                                     *)
(* DESCRIPTION   : Library for a more convenient and practical version   *)
(*                 of nested mutually recursive datatypes.               *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier                                 *)
(* DATE          : Aprile 18. 1998                                       *)
(* COPYRIGHT     : Copyright (c) 1998 by Peter Vincent Homeier           *)
(*                                                                       *)
(* ===================================================================== *)

val mutual_lib =
    Library.new_library
       {name = "mutual",
        doc = "A more convenient version"^
              " of nested mutually recursive datatypes, \n"^
              "  by Peter Vincent Homeier",
        path = (!Globals.HOLdir)^"contrib/mutual/",
        parents = [Sys_lib.nested_rec_lib],
        theories = [],
        code = ["mutrec.yak.sig",
                "mutrec.yak.sml",
                "define_mutual_types.sig",
                "define_mutual_types.sml",
                "recftn.sml",
                "mutual_induct_then.sig",
                "mutual_induct_then.sml",
                "mutualLib.sml"],
        help = [],
        loaded = "fn() => ()"};

