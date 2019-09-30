structure HOLset :> HOLset =
struct
  exception NotFound = Redblackset.NotFound
  open Redblackset

  fun pp_holset dpth ipp s =
      let
        open HOLPP
        fun ppi i = ipp (i,dpth - 1)
      in
        if dpth <= 0 then add_string "HOLset{...}"
        else
          block CONSISTENT 0 [
            add_string "HOLset{",
            block INCONSISTENT 7
                  (pr_list ppi [add_string ",",add_break (1,0)] (listItems s)),
            add_string "}"
          ]
      end

end
