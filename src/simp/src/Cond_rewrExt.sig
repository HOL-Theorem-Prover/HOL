(* Conditional rewriting for the extension simplifier *)
signature Cond_rewrExt =
sig
  include Abbrev
  type config = Cond_rewr.config
  type runners = Cond_rewr.runners
  val is_var_perm : term * term -> bool
  (* = Cond_rewr.COND_REWR_CONVS *)
  val COND_REWR_CONVS : string * thm -> bool -> runners
  (* Its configured conversion; WITH_CONTEXT takes a depth limit *)
  val COND_REWR_CONV_WITH_CONFIG : string * thm -> bool -> config -> conv
  val COND_REWR_CONV_WITH_CONTEXT : string * thm -> bool ->
    {solver : term list -> term -> thm, stack : term list,
     cond_depth : int, term_ord : term * term -> order} -> conv

  (* A rewrite prepared with a use count, which it uses as given rather
     than resetting it.  Each successful application decrements the
     count.  runners gives the conversions without preparing them again.
     Concurrent use must be synchronised by the caller. *)
  type prepared
  val prepare : string * thm -> BoundedRewrites.control -> prepared
  val runners : prepared -> runners
  (* The same rewrite with another use count; fails if one is bounded
     and the other is not *)
  val rebind : prepared -> BoundedRewrites.control -> prepared
end
