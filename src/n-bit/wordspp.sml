structure wordspp :> wordspp =
struct

open HolKernel term_pp_types term_pp_utils Hol_pp
open fcpLib fcpSyntax

val ERR = mk_HOL_ERR "wordsLib"

val word_pp_mode = ref 0
val word_cast_on = ref false
val int_word_pp  = ref false

val _ = Feedback.register_btrace ("word cast printing", word_cast_on)
val _ = Feedback.register_trace ("word printing", word_pp_mode, 6)
val _ = Feedback.register_btrace ("word pp as 2's comp", int_word_pp)

local
   fun lsr (x, y) =
      if x = Arbnum.zero orelse y = Arbnum.zero
         then x
      else lsr (Arbnum.div2 x, Arbnum.less1 y)
   fun int_word (v, m) =
      if !int_word_pp andalso m <> Arbnum.zero
         then let
                 val top = lsr (v, Arbnum.less1 m)
                 val neg = top = Arbnum.one
                 val nv =
                    if neg then Arbnum.- (Arbnum.pow (Arbnum.two, m), v) else v
              in
                 (neg, nv)
              end
      else (false, v)
   val hexsplit = Arbnum.fromHexString "10000"
   fun f (l, v) =
        if !word_pp_mode = 0 andalso Arbnum.<= (hexsplit, v)
           then "0x" ^ Arbnum.toHexString v
        else if !word_pp_mode = 0 orelse !word_pp_mode = 3
           then Arbnum.toString v
        else if !word_pp_mode = 1
           then "0b" ^ Arbnum.toBinString v
        else if !word_pp_mode = 2
           then if !base_tokens.allow_octal_input
                   orelse Arbnum.< (v, Arbnum.fromInt 8)
                   then "0" ^ Arbnum.toOctString v
                else ( Feedback.HOL_MESG
                         "Octal output is only supported when \
                         \base_tokens.allow_octal_input is true."
                     ; Arbnum.toString v
                     )
        else if !word_pp_mode = 6 andalso l mod 4 = 0
           then "0x" ^ StringCvt.padLeft #"0" (l div 4) (Arbnum.toHexString v)
        else if !word_pp_mode = 4 orelse !word_pp_mode = 6
           then "0x" ^ Arbnum.toHexString v
        else if !word_pp_mode = 5
           then "0b" ^ StringCvt.padLeft #"0" l (Arbnum.toBinString v)
        else raise ERR "output_words_as" "invalid printing mode"
   fun dest_word_type ty =
     let
        val (a, b) = fcpSyntax.dest_cart_type ty
        val _ = a = Type.bool orelse
                    raise ERR "dest_word_type" "not an instance of :bool['a]"
     in
        b
     end
   val dim_of = dest_word_type o Term.type_of
in
   fun words_printer Gs backend sys ppfns gravs d t =
      let
         open Portable term_pp_types smpp
         infix >>
         val {add_string=str, add_break=brk,...} =
            ppfns: term_pp_types.ppstream_funs
         val x = dim_of t
         val (_, n) = dest_comb t
         val m = fcpLib.index_to_num x handle HOL_ERR _ => Arbnum.zero
         val v = numSyntax.dest_numeral n
         val (neg, v) = int_word (v, m)
      in
         (if !Globals.show_types orelse !word_cast_on
             then str "("
          else nothing)
         >> (if neg then str "-" else nothing)
         >> str (f (Arbnum.toInt m, v) ^ "w")
         >> (if !Globals.show_types orelse !word_cast_on
                then brk (1, 2)
                     >> lift pp_type (type_of t)
                     >> str ")"
             else nothing)
      end
      handle HOL_ERR _ => raise term_pp_types.UserPP_Failed
end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "wordspp.words_printer",
           code = words_printer}

(* -------------------------------------------------------------------------
   A pretty-printer that shows the types for ><, w2w and @@
   ------------------------------------------------------------------------- *)

fun words_cast_printer Gs backend syspr ppfns (pg, lg, rg) d t =
   let
      open Portable term_pp_types smpp
      infix >>
      val ppfns : ppstream_funs = ppfns
      val {add_string = str, add_break = brk, ublock,...} = ppfns
      fun stype tm = String.extract (type_to_string (type_of tm), 1, NONE)
      fun delim i act =
         case pg of
            Prec (j, _) => if i <= j then act else nothing
          | _ => nothing
      val (f, x) = strip_comb t
      fun sys g d t = syspr {gravs = g, depth = d, binderp = false} t
   in
      case (dest_thy_const f, x) of
         ({Name = "n2w", Thy = "words", Ty = ty}, [a]) =>
            let
               val prec = Prec (2000, "n2w")
            in
               ublock INCONSISTENT 0
                 (delim 200 (str "(")
                  >> str "(n2w "
                  >> lift pp_type ty
                  >> str ")"
                  >> brk (1, 2)
                  >> sys (prec, prec, prec) (d - 1) a
                  >> delim 200 (str ")"))
            end
       | ({Name = "w2w", Thy = "words", Ty = ty}, [a]) =>
            let
               val prec = Prec (2000, "w2w")
            in
               ublock INCONSISTENT 0
                 (delim 200 (str "(")
                  >> str "(w2w "
                  >> lift pp_type ty
                  >> str ")"
                  >> brk (1, 2)
                  >> sys (prec, prec, prec) (d - 1) a
                  >> delim 200 (str ")"))
           end
       | ({Name = "sw2sw", Thy = "words", Ty = ty}, [a]) =>
            let
               val prec = Prec (2000, "sw2sw")
            in
               ublock INCONSISTENT 0
                 (delim 200 (str "(")
                  >> str "(sw2sw "
                  >> lift pp_type ty
                  >> str ")"
                  >> brk (1, 2)
                  >> sys (prec, prec, prec) (d - 1) a
                  >> delim 200 (str ")"))
            end
       | ({Name = "word_concat", Thy = "words", Ty = ty}, [a, b]) =>
            let
               val prec = Prec (2000, "word_concat")
            in
               ublock INCONSISTENT 0
                 (delim 200 (str "(")
                  >> str "(word_concat "
                  >> lift pp_type ty
                  >> str ")"
                  >> brk (1, 2)
                  >> sys (prec, prec, prec) (d - 1) a
                  >> brk (1, 0)
                  >> sys (prec, prec, prec) (d - 1) b
                  >> delim 200 (str ")"))
            end
       | ({Name = "word_extract", Thy = "words", Ty = ty}, [h, l, a]) =>
            let
               val prec = Prec (2000, "word_extract")
            in
               ublock INCONSISTENT 0
                 (delim 200 (str "(")
                  >> str "("
                  >> str "("
                  >> sys (prec, prec, prec) (d - 1) h
                  >> brk (1, 2)
                  >> str "><"
                  >> brk (1, 2)
                  >> sys (prec, prec, prec) (d - 1) l
                  >> str ")"
                  >> brk (1, 2)
                  >> lift pp_type (type_of (list_mk_comb (f, [h, l])))
                  >> str ")"
                  >> brk (1, 2)
                  >> sys (prec, prec, prec) (d - 1) a
                  >> delim 200 (str ")"))
            end
       | _ => raise term_pp_types.UserPP_Failed
   end
   handle HOL_ERR _ => raise term_pp_types.UserPP_Failed

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "wordspp.words_cast_printer",
           code = words_cast_printer}

end
