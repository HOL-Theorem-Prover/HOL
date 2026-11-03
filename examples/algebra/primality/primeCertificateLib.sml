(* Recursive Lucas certificate checker; see primeCertificateLib.sig.
   PRIME_CERT_CONV data evaluates prime <numeral> to T with a kernel theorem.
   A certificate supplies decimal n, a witness, and prime factors of n-1 with
   positive multiplicities. Supply certificates for subsidiary primes too;
   2 and 3 are built in. Each constructed converter caches successful primality
   proofs, not unchecked data. Missing factors/certificates or failed arithmetic
   obligations prevent construction of the claimed proof. *)

structure primeCertificateLib :> primeCertificateLib =
struct

open HolKernel boolLib bossLib Conv

open cv_stdTheory

(* Normalize certificate arithmetic without changing Boolean structure. *)
val nat_step = FIRST_CONV
  [Arithconv.DIV_CONV, Arithconv.LT_CONV, Arithconv.MUL_CONV,
   Arithconv.NEQ_CONV, Arithconv.SBC_CONV]

fun nat_conv tm =
  if numSyntax.is_numeral tm then REFL tm
  else (SUB_CONV nat_conv THENC TRY_CONV nat_step) tm

val modpow_conv =
  REWR_CONV (GSYM expModTheory.exp_mod_binary_eqn) THENC cv_transLib.cv_eval

type certificate = string * string * (string * int) list
val prime_tm = prim_mk_const {Thy = "divides", Name = "prime"}
val ERR = mk_HOL_ERR "primeCertificateLib"
val numeral = numSyntax.mk_numeral o Arbnum.fromString

fun PRIME_CERT_CONV certificates =
  let
    val certificates = map
      (fn (n,a,fs) =>
        (Arbnum.fromString n,a,
         map (fn (q,e) => (Arbnum.fromString q,e)) fs))
      certificates
    val cache = ref [(Arbnum.two,dividesTheory.PRIME_2),
                     (Arbnum.fromInt 3,dividesTheory.PRIME_3)]
    fun find n [] = raise ERR "PRIME_CERT_CONV"
          ("Missing certificate data for " ^ Arbnum.toString n)
      | find n ((m,a,fs)::rest) =
          if n = m then (a,fs) else find n rest
    fun prime n =
      case List.find (fn (m,_) => n = m) (!cache) of
        SOME (_,th) => th
      | NONE =>
        let
          val (a,factors) = find n certificates
          fun repeat (q,e) =
            if e <= 0 then raise ERR "PRIME_CERT_CONV"
              "Factor multiplicities must be positive"
            else
              if Arbnum.< (q,n) then
                let val q_term = numSyntax.mk_numeral q
                in List.tabulate (e, fn _ => q_term) end
              else raise ERR "PRIME_CERT_CONV"
                "Factors must be smaller than the candidate prime"
          val fs = listSyntax.mk_list
            (List.concat (map repeat factors),numSyntax.num)
          val proofs = map (prime o #1) factors
          val rule = SPECL [numSyntax.mk_numeral n,numeral a,fs]
            primeCertificateTheory.prime_cert_check
          val premise = fst (dest_imp (concl rule))
          val checked = TAC_PROOF (([],premise),
            REWRITE_TAC
              ([listTheory.EVERY_DEF,combinatoricsTheory.PROD] @ proofs) THEN
            CONV_TAC (DEPTH_CONV BETA_CONV) THEN
            CONV_TAC (DEPTH_CONV
              (fn tm =>
                if numSyntax.is_mod tm andalso
                   numSyntax.is_exp (fst (numSyntax.dest_mod tm))
                then modpow_conv tm
                else raise UNCHANGED)
              THENC nat_conv) THEN
            REWRITE_TAC [])
          val th = MP rule checked
          val _ = cache := (n,th) :: !cache
        in th end
  in
    fn tm =>
      let
        val (head,args) = strip_comb tm
        val _ = same_const head prime_tm andalso length args = 1
          orelse raise ERR "PRIME_CERT_CONV" "Expected prime numeral"
        val n = numSyntax.dest_numeral (hd args)
      in EQT_INTRO (prime n) end
  end

end