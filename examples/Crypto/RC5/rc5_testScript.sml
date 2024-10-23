open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib listTheory listLib combinTheory hurdUtils;

open RC5Theory;

val _ = new_theory "rc5_test";

val fcp_ss = std_ss ++ fcpLib.FCP_ss;

Theorem Skeys_l32_r1 :
    (Skeys 32 1):word32 list= [0xB7E15163w;0x15618CB1Cw;0x1F45044D5w;0x29287BE8Ew]
Proof
    EVAL_TAC
QED

Theorem half_messageTest1:
    half_messageDe
       (half_messageEn 0x3w 0x2w [0x2w;0x1w;0x3w;0x1w] (2*1))
       (half_messageEn 0x3w 0x2w [0x2w;0x1w;0x3w;0x1w] (2*1+1))
       [0x2w;0x1w;0x3w;0x1w] (2*1) = 0x2w
Proof
    EVAL_TAC
QED

Theorem half_messageTest2:
    half_messageDe
        (half_messageEn 0x3w 0x2w [0x2w;0x1w] (1))
        (half_messageEn 0x3w 0x2w [0x2w;0x1w] (1+1))
        [0x2w;0x1w] (1) = 0x2w
Proof
    EVAL_TAC
QED
Theorem RoundEn_De_Test:
    RoundDe 1 [0x2w;0x1w;0x3w;0x1w]
       (RoundEn 1 0x3w 0x2w [0x2w;0x1w;0x3w;0x1w])= (0x3w,0x2w)
Proof
    EVAL_TAC
QED






val _ = export_theory();
val _ = html_theory "rc5_test";
