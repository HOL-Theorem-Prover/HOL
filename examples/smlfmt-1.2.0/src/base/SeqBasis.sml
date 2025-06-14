(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure SeqBasis:
sig
  val foldl: ('b * 'a -> 'b) -> 'b -> (int * int) -> (int -> 'a) -> 'b
  val foldr: ('b * 'a -> 'b) -> 'b -> (int * int) -> (int -> 'a) -> 'b
  val filter: (int * int) -> (int -> 'a) -> (int -> bool) -> 'a array
end =
struct

  structure A = Array
  structure AS = ArraySlice

  fun foldl g b (lo, hi) f =
    if lo >= hi then b
    else let val b' = g (b, f lo) in foldl g b' (lo + 1, hi) f end

  fun foldr g b (lo, hi) f =
    if lo >= hi then
      b
    else
      let
        val hi' = hi - 1
        val b' = g (b, f hi')
      in
        foldr g b' (lo, hi') f
      end

  fun filter (lo, hi) f pred =
    if hi - lo <= 0 then
      Array.fromList []
    else
      let
        val count = foldl op+ 0 (lo, hi) (fn i => if pred i then 1 else 0)
        val output = Array.array (count, f lo)
      in
        (* 0 <= j < count: output index
         * lo <= i < hi: input index
         *)
        Util.loop (lo, hi) 0 (fn (j, i) =>
          if pred i then (Array.update (output, j, f i); (j + 1)) else j);

        output
      end

end
