(*
 * Copyright 1991-1995  University of Cambridge (Author: Monica Nesi)
 * Copyright 2016-2017  University of Bologna   (Author: Chun Tian)
 *)

signature CCSConv =
sig
  include Abbrev

  val eqf_elim			: thm -> thm
  val strip_trans		: thm -> (term * term) list
  val CCS_TRANS_CONV		: conv
  val CCS_TRANS			: term -> thm * (term * term) list
end

(* last updated: May 15, 2017 *)
