signature PFTCandleComputePreamble = sig

  (* Emit the Candle compute preamble into an open PFT stream.

     == Prerequisites ==

     Must be called AFTER the Candle preamble has been emitted and the
     following theories have been fully processed and their exports SAVEd:
       - bool, num, arithmetic, prim_rec, cv

     == Required loaded theorems ==

     Notation follows Candle naming (see pft-ruleset-candle.md).
     All theorems below are assumed to have empty hypothesis lists and
     free (un-quantified) variables as shown.

     -- Candle preamble pro-formas (see PFTCandlePreamble.sml) ----------

       candle$CONJUNCT1  :  {p ∧ q} ⊢ p              p:bool, q:bool
       candle$CONJUNCT2  :  {p ∧ q} ⊢ q              p:bool, q:bool
       candle$EQT_INTRO  :  ⊢ t = (t = T)             t:bool

     -- Arithmetic -----------------------------------------------------

       arithmetic$BIT1       ⊢ BIT1 n = n + (n + SUC _0)
                            n : num

       arithmetic$BIT2       ⊢ BIT2 n = n + (n + SUC (SUC _0))
                            n : num

       arithmetic$ADD_SUC    ⊢ m + SUC n = SUC (m + n)
                            m : num, n : num

       arithmetic$ADD_0      ⊢ m + NUMERAL _0 = m
                            m : num

       arithmetic$ADD        ⊢ (NUMERAL _0 + n = n) ∧ (SUC m + n = SUC (m + n))
                            m : num, n : num

       arithmetic$ADD_COMM   ⊢ m + n = n + m
                            m : num, n : num

       arithmetic$SUB_0      ⊢ (NUMERAL _0 - m = NUMERAL _0) ∧ (m - NUMERAL _0 = m)
                            m : num

       arithmetic$SUB_MONO_EQ  ⊢ SUC n - SUC m = n - m
                            m : num, n : num

       arithmetic$MULT       ⊢ (NUMERAL _0 * n = NUMERAL _0) ∧ (SUC m * n = m * n + n)
                            m : num, n : num

       arithmetic$NUMERAL_DEF  ⊢ NUMERAL n = n
                            n : num

     -- prim_rec -------------------------------------------------------

       prim_rec$LESS_0       ⊢ NUMERAL _0 < SUC n
                            n : num

       prim_rec$LESS_MONO_EQ  ⊢ SUC m < SUC n = (m < n)
                            m : num, n : num

     -- cv -------------------------------------------------------------

       cv$LT_RECURSIVE       ⊢ (m < NUMERAL _0 = F) ∧ (m < SUC n = IF (m = n) T (m < n))
                            m : num, n : num

       cv$SUC_EQ             ⊢ (SUC m = NUMERAL _0 = F) ∧ (SUC m = SUC n = (m = n))
                            m : num, n : num

       cv$DIV_RECURSIVE      ⊢ m DIV n = COND (n = NUMERAL _0) (NUMERAL _0)
                                (COND (m < n) (NUMERAL _0) (SUC ((m - n) DIV n)))
                            m : num, n : num

       cv$MOD_RECURSIVE      ⊢ m MOD n = COND (n = NUMERAL _0) m
                                (COND (m < n) m ((m - n) MOD n))
                            m : num, n : num

       cv$cv_add_def         ⊢ (Cexp_add (Cexp_num m) (Cexp_num n) = Cexp_num (m + n)) ∧
                               (Cexp_add (Cexp_num m) (Cexp_pair p q) = Cexp_num m) ∧
                               (Cexp_add (Cexp_pair p q) (Cexp_num n) = Cexp_num n) ∧
                               (Cexp_add (Cexp_pair p q) (Cexp_pair r s) = Cexp_num (NUMERAL _0))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_sub_def         ⊢ (Cexp_sub (Cexp_num m) (Cexp_num n) = Cexp_num (m - n)) ∧
                               (Cexp_sub (Cexp_num m) (Cexp_pair p q) = Cexp_num m) ∧
                               (Cexp_sub (Cexp_pair p q) (Cexp_num n) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_sub (Cexp_pair p q) (Cexp_pair r s) = Cexp_num (NUMERAL _0))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_mul_def         ⊢ (Cexp_mul (Cexp_num m) (Cexp_num n) = Cexp_num (m * n)) ∧
                               (Cexp_mul (Cexp_num m) (Cexp_pair p q) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_mul (Cexp_pair p q) (Cexp_num n) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_mul (Cexp_pair p q) (Cexp_pair r s) = Cexp_num (NUMERAL _0))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_div_def         ⊢ (Cexp_div (Cexp_num m) (Cexp_num n) = Cexp_num (m DIV n)) ∧
                               (Cexp_div (Cexp_num m) (Cexp_pair p q) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_div (Cexp_pair p q) (Cexp_num n) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_div (Cexp_pair p q) (Cexp_pair r s) = Cexp_num (NUMERAL _0))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_mod_def         ⊢ (Cexp_mod (Cexp_num m) (Cexp_num n) = Cexp_num (m MOD n)) ∧
                               (Cexp_mod (Cexp_num m) (Cexp_pair p q) = Cexp_num m) ∧
                               (Cexp_mod (Cexp_pair p q) (Cexp_num n) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_mod (Cexp_pair p q) (Cexp_pair r s) = Cexp_num (NUMERAL _0))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_lt_def          ⊢ (Cexp_less (Cexp_num m) (Cexp_num n) =
                                Cexp_num (COND (m < n) (SUC (NUMERAL _0)) (NUMERAL _0))) ∧
                               (Cexp_less (Cexp_num m) (Cexp_pair p q) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_less (Cexp_pair p q) (Cexp_num n) = Cexp_num (NUMERAL _0)) ∧
                               (Cexp_less (Cexp_pair p q) (Cexp_pair r s) = Cexp_num (NUMERAL _0))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_if_def          ⊢ (Cexp_if (Cexp_num (SUC m)) p q = p) ∧
                               (Cexp_if (Cexp_num (NUMERAL _0)) p q = q) ∧
                               (Cexp_if (Cexp_pair r s) p q = q)
                            m : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

       cv$cv_fst_def         ⊢ (Cexp_fst (Cexp_pair p q) = p) ∧
                               (Cexp_fst (Cexp_num m) = Cexp_num (NUMERAL _0))
                            m : num, p : Cexp, q : Cexp

       cv$cv_snd_def         ⊢ (Cexp_snd (Cexp_pair p q) = q) ∧
                               (Cexp_snd (Cexp_num m) = Cexp_num (NUMERAL _0))
                            m : num, p : Cexp, q : Cexp

       cv$cv_ispair_def      ⊢ (Cexp_ispair (Cexp_pair p q) = Cexp_num (SUC (NUMERAL _0))) ∧
                               (Cexp_ispair (Cexp_num m) = Cexp_num (NUMERAL _0))
                            m : num, p : Cexp, q : Cexp

       cv$cv_eq_def          ⊢ Cexp_eq p q = Cexp_num (COND (p = q) (SUC (NUMERAL _0)) (NUMERAL _0))
                            p : Cexp, q : Cexp

       cv$CV_EQ              ⊢ (Cexp_pair p q = Cexp_pair r s = IF (p = r) (q = s) F) ∧
                               (Cexp_pair p q = Cexp_num n = F) ∧
                               (Cexp_num m = Cexp_num n = (m = n))
                            m : num, n : num, p : Cexp, q : Cexp, r : Cexp, s : Cexp

     -- bool -----------------------------------------------------------

       bool$COND_CLAUSES     ⊢ (COND T t1 t2 = t1) ∧ (COND F t1 t2 = t2)
                            t1 : 'a, t2 : 'a

       bool$LET_THM          ⊢ LET f x = f x
                            f : 'a -> 'b, x : 'a

     == Emitted theorems ==

     All SAVEd with candle$ prefix:

       candle$BIT0_DEF         ⊢ BIT0 = λn. n + n
       candle$BIT0             ⊢ BIT0 n = n + n
       candle$BIT1             ⊢ BIT1 n = SUC (n + n)
       candle$LESS_1            ⊢ m < NUMERAL _0 = F
       candle$LESS_2            ⊢ NUMERAL _0 < SUC n = T
       candle$LESS_3            ⊢ SUC m < SUC n = (m < n)
       candle$COMPUTE_EQ_1..62  the 62 characteristic equations
                                (see pft-ruleset-candle.md)
       candle$BIT2_eq_BIT0_SUC  ⊢ BIT2 n = BIT0 (SUC n)
       candle$SUC_0             ⊢ SUC _0 = BIT1 _0
       candle$SUC_BIT0          ⊢ SUC (BIT0 n) = BIT1 n
       candle$SUC_BIT1          ⊢ SUC (BIT1 n) = BIT0 (SUC n)
       candle$NUM_XLATE_n       ⊢ <HOL4 bits for n> = <Candle bits for n>
                                for n in 2..255 whose HOL4 form contains BIT2
       candle$NUM_XLATE_REV_n   ⊢ <Candle bits for n> = <HOL4 bits for n>
                                same n values as above
  *)

  val emit : { out : PFTWriter.pft_out,
               alloc_ty : unit -> int,
               alloc_tm : unit -> int,
               alloc_th : unit -> int,
               load_theorem : string -> int
             } -> unit

end
