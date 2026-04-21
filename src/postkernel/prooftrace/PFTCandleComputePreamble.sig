signature PFTCandleComputePreamble = sig

  (* Emit the Candle compute preamble into an open PFT stream.

     This module emits additional definitions and theorems required for
     Candle's COMPUTE_INIT rule, building on theorems already available
     from replayed HOL4 theories.

     == Prerequisites ==

     Must be called AFTER the following theories have been fully processed
     and their exports SAVEd:
       - bool (provides: COND, LET, T, F)
       - num (provides: num type, 0, SUC)
       - arithmetic (provides: +, -, *, DIV, MOD, <, BIT1, BIT2, NUMERAL,
                     and equations ADD, SUB, MULT, DIV_RECURSIVE,
                     MOD_RECURSIVE, etc.)
       - cv (provides: cv type, Num, Pair, cv_add, cv_sub, cv_mul, cv_div,
             cv_mod, cv_lt, cv_if, cv_fst, cv_snd, cv_ispair, cv_eq,
             and equations cv_add_def, cv_sub_def, CV_EQ, LT_RECURSIVE, etc.)

     This is typically called on first encounter of a compute_prf during
     Candle-mode emission. Since compute_prf can only appear in theories
     that depend on cv_compute (which depends on cv, which depends on
     arithmetic), these prerequisites are always satisfied.

     == Why the interface takes functions as arguments ==

     The preamble is emitted *inline* during PFTEmit's processing of a
     theory trace, not as a separate file. It must integrate with
     PFTEmit's existing state:

       - alloc_ty, alloc_tm, alloc_th, alloc_ci: ID allocators owned by
         PFTEmit. IDs must be globally unique and monotonically increasing
         across the entire trace. The preamble cannot have its own
         allocators.

       - out: The PFTWriter output stream, already open and mid-trace.
         The preamble emits directly into this stream.

       - load_theorem: A function to LOAD a previously SAVEd theorem by
         name, returning its theorem ID in the current trace. This
         abstracts over PFTEmit's handling of LOAD (which may involve
         ID allocation and caching).

     == What gets emitted ==

       1. Definition of BIT0 (not present in HOL4, needed by Candle):
            BIT0 = λn. n + n

       2. Proof of BIT1 in Candle's expected form:
            ⊢ BIT1 n = SUC (n + n)
          Derived from HOL4's BIT1 definition: BIT1 n = n + (n + SUC 0)

       3. Three LESS equations in Candle's structural form:
            ⊢ m < 0 = F
            ⊢ 0 < SUC n = T
            ⊢ SUC m < SUC n = (m < n)
          Derived from HOL4's theorems.

       4. The 62 characteristic equations for COMPUTE_INIT:
            candle$COMPUTE_EQ_1 through candle$COMPUTE_EQ_62
          Most are LOADed from arithmetic/cv theories; some use the
          above transformations.

       5. Numeral translation equations and cache:
          HOL4 uses BIT1/BIT2 encoding, Candle uses BIT0/BIT1.

          Key equations for on-the-fly translation of large numerals:
            - candle$BIT2_eq_BIT0_SUC: BIT2 n = BIT0 (SUC n)
            - candle$SUC_0: SUC _0 = BIT1 _0
            - candle$SUC_BIT0: SUC (BIT0 n) = BIT1 n
            - candle$SUC_BIT1: SUC (BIT1 n) = BIT0 (SUC n)

          Cached forward translations (HOL4 -> Candle) for 0-255:
            - candle$NUM_XLATE_2: BIT2 _0 = BIT0 (BIT1 _0)
            - candle$NUM_XLATE_4: BIT2 (BIT1 _0) = BIT0 (BIT0 (BIT1 _0))
            - etc. (only for values containing BIT2 in HOL4 form)

          Cached reverse translations (Candle -> HOL4) for 0-255:
            - candle$NUM_XLATE_REV_2: BIT0 (BIT1 _0) = BIT2 _0
            - candle$NUM_XLATE_REV_4: BIT0 (BIT0 (BIT1 _0)) = BIT2 (BIT1 _0)
            - etc. (same values as forward translations)

     == Emitted theorem names ==

     All theorems are SAVEd with candle$ prefix:
       - candle$BIT0_DEF
       - candle$BIT1_CANDLE (Candle form)
       - candle$LESS_0, candle$LESS_SUC_0, candle$LESS_SUC_SUC
       - candle$COMPUTE_EQ_1 through candle$COMPUTE_EQ_62
       - candle$BIT2_eq_BIT0_SUC, candle$SUC_0, candle$SUC_BIT0, candle$SUC_BIT1
       - candle$NUM_XLATE_n for n in 2..255 that need translation
  *)

  val emit : { out : PFTWriter.pft_out,
               alloc_ty : unit -> int,
               alloc_tm : unit -> int,
               alloc_th : unit -> int,
               load_theorem : string -> int
             } -> unit

end
