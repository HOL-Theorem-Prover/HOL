(* Copyright (C) 1997-2001 by Ken Friis Larsen and Jakob Lichtenberg. *)

structure MuddyCore =
struct

open Dynlib

local
  val path = case Process.getEnv "MUDDYHOME" of
                SOME p => Path.concat (p, "muddy.so")
              | NONE   => "muddy.so"
  val path = Globals.HOLDIR^"/sigobj/muddy.so"
  val hdl  = dlopen {lib = path, flag = RTLD_NOW, global = false}
in
  val symb = dlsym hdl
  fun cur2 h (a,b) = app2 h a b
  fun cur3 h (a,b,c) = app3 h a b c
  fun cur23 h a (b,c) = app3 h a b c
end

end
