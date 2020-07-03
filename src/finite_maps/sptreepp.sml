structure sptreepp :> sptreepp =
struct

open HolKernel Parse

fun lrnext n = if n = 0 then 1 else 2 * lrnext((n - 1) div 2)

datatype MLsptree = MLN | MLS of term | MBN of term * term
                  | MBS of term * term * term

fun dest_sptree tm =
    let val (f, args) = strip_comb tm
        val {Thy,Name,Ty} = dest_thy_const f
    in
      if Thy <> "sptree" then
        raise mk_HOL_ERR "sptreepp" "dest_sptree" "Not an sptree"
      else
      case (Name,args) of
          ("LN", _) => MLN
        | ("LS", [t]) => MLS t
        | ("BN", [t1,t2]) => MBN (t1,t2)
        | ("BS", [t1,t2,t3]) => MBS(t1,t2,t3)
        | _ => raise mk_HOL_ERR "sptreepp" "dest_sptree" "Not a ground sptree"
    end

fun derive_alist A i tm =
    case dest_sptree tm of
        MLN => A
      | MLS v => (i,v) :: A
      | MBN (lb,rb) =>
        let val inc = lrnext i
        in
          derive_alist (derive_alist A (i + 2 * inc) lb) (i + inc) rb
        end
      | MBS (lb,v,rb) =>
        let val inc = lrnext i
        in
          derive_alist (derive_alist ((i,v)::A) (i + 2 * inc) lb) (i + inc) rb
        end

val sptreepp_enabled = ref true
val _ = register_btrace ("PP.sptreepp_enabled", sptreepp_enabled)

fun sptree_printer (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val _ = get_tracefn "PP.sptreepp_enabled" () = 1 orelse
              raise UserPP_Failed
      val unicodep = get_tracefn "PP.avoid_unicode" () = 0
      val alist = derive_alist [] 0 tm handle HOL_ERR _ => raise UserPP_Failed
      val sorted = Listsort.sort (inv_img_cmp #1 Int.compare) alist
      val _ = if null alist then raise UserPP_Failed else ()
      val setp = type_of (snd (hd sorted)) = oneSyntax.one_ty
      val (llense, arrow, rlense) =
          if unicodep then ("⦕", "↦", "⦖") (* UOK *)
          else ("(|SPT|", "|->", "|)")
      val arrow_grav = Prec(100, "  sptreepp.arrow")
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      fun prkv (k,v) =
          if setp then
            add_string (Int.toString k)
          else
            block PP.INCONSISTENT 2 (
              add_string (Int.toString k) >>
              add_string " " >> add_string arrow >> add_break(1,0) >>
              printer {gravs = (arrow_grav,Top, arrow_grav),
                       depth = decdepth depth, binderp = false} v
            )
    in
      block PP.CONSISTENT 0 (
        add_string llense >> add_break(1,2) >>
        block PP.INCONSISTENT 0 (
            pr_list prkv (add_string ";" >> add_break(1,0)) sorted
        ) >> add_break(1,0) >>
        add_string rlense
      )
    end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "sptreepp.sptreepp", code = sptree_printer}

end (* struct *)
