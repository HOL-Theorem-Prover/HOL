app load ["mesonLib", "pairTheory", "numTheory"];

fun M tm = Tactical.prove(tm, mesonLib.MESON_TAC []);

(*---------------------------------------------------------------------------
 * Some of the big formulas are too big for guessing tyvars for. A workaround
 * is to give explicit constraints.
 *---------------------------------------------------------------------------*)

val _ = Globals.guessing_tyvars := false;

(* ------------------------------------------------------------------------- 
 * Trivia
 * ------------------------------------------------------------------------- *)

(* M90: OK *)
M (--`T`--);


(* M90: OK *)
M (--`P \/ ~P`--);


(* ------------------------------------------------------------------------- 
 * Basic existential stuff (bug reported by Michael Norrish)
 * ------------------------------------------------------------------------- *)

M (--`!se:num. ?n:num. f n se se ==> ?m:num. f m 0 0 `--);

(* ------------------------------------------------------------------------- 
 * P50
 * ------------------------------------------------------------------------- *)

val P50 = (--`(!x:'a. F0 a x \/ !y. F0 x y) ==> ?x. !y. F0 x y`--);
M P50;

(* ------------------------------------------------------------------------- 
 * Example from Eric Borm (see long info-hol discussion, September 93).      
 * ------------------------------------------------------------------------- *)

val ERIC = Term
`!P Q R. !x:'a. ?v w. !y (z:'b).
          P x /\ Q y ==> (P v \/ R w) /\ (R z ==> Q v)`;

M ERIC;



(* ------------------------------------------------------------------------- 
 * The classic Los puzzle. (Clausal version MSC006-1 in the TPTP library.)   
 * Note: this is actually in the decidable "AE" subset, though that doesn't  
 * yield a very efficient proof.                                             
 * ------------------------------------------------------------------------- *)

val LOS = (--`(!(x:'a) (y:'a) z. P x y /\ P y z ==> P x z) /\
   (!x (y:'a) z. Q x y /\ Q y z ==> Q x z) /\
   (!x y. P x y ==> P y x) /\
   (!x y. P x y \/ Q x y)
   ==> (!x y. P x y) \/ (!x y. Q x y)`--);

M LOS;;


(* ------------------------------------------------------------------------- 
 * An equality-free version of the Agatha puzzle.                            
 * ------------------------------------------------------------------------- *)

val P55 =
(--`lives(agatha) /\ lives(butler) /\ lives(charles) /\
   (killed(agatha,agatha) \/ killed(butler,agatha) \/
    killed(charles,agatha)) /\
   (!x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (!x. hates(agatha,x) ==> ~hates(charles,x)) /\
   (hates(agatha,agatha) /\ hates(agatha,charles)) /\
   (!x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
   (!x. hates(agatha,x) ==> hates(butler,x)) /\
   (!x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) ==>
   (?x:'person. killed(x,agatha))`--);

M P55;


(* ------------------------------------------------------------------------- 
 * The Steamroller.                                                          
 * ------------------------------------------------------------------------- *)

val P47 = (--`((!x:'a. P1 x ==> P0 x) /\ (?x. P1 x)) /\
   ((!x. P2 x ==> P0 x) /\ (?x. P2 x)) /\
   ((!x. P3 x ==> P0 x) /\ (?x. P3 x)) /\
   ((!x. P4 x ==> P0 x) /\ (?x. P4 x)) /\
   ((!x. P5 x ==> P0 x) /\ (?x. P5 x)) /\
   ((?x. Q1 x) /\ (!x. Q1 x ==> Q0 x)) /\
   (!x. P0 x ==> (!y. Q0 y ==> R x y) \/
    (((!y. P0 y /\ S0 y x /\ ?z. Q0 z /\ R y z) ==> R x y))) /\
   (!x y. P3 y /\ (P5 x \/ P4 x) ==> S0 x y) /\
   (!x y. P3 x /\ P2 y ==> S0 x y) /\
   (!x y. P2 x /\ P1 y ==> S0 x y) /\
   (!x y. P1 x /\ (P2 y \/ Q1 y) ==> ~(R x y)) /\
   (!x y. P3 x /\ P4 y ==> R x y) /\
   (!x y. P3 x /\ P5 y ==> ~(R x y)) /\
   (!x. (P4 x \/ P5 x) ==> ?y. Q0 y /\ R x y)
   ==> ?x y. P0 x /\ P0 y /\ ?z. Q1 z /\ R y z /\ R x y`--);

M P47;


(* ------------------------------------------------------------------------- 
 * Now problems with equality.                                               
 * ------------------------------------------------------------------------- *)

val P48 = M
 (--`((a:'a = b) \/ (c = d)) /\ ((a = c) \/ (b = d)) ==> (a = d) \/ (b = c)`--);
  
(* hol90 - tick *)


(* ------------------------------------------------------------------------- 
 * More problems with equality.                                               
 * ------------------------------------------------------------------------- *)

(* hol90 - no *)
val P49 = (--`(?x y. !z:'a. (z = x) \/ (z = y)) /\
                            P a /\ P b /\ ~(a = b) ==> !x:'a. P x`--);


val P51 = 
 (--`(?z w:'a. !x y:'a. F0 x y = (x = z) /\ (y = w)) ==>
        ?z:'a. !x:'a. (?w:'a. !y:'a. F0 x y = (y = w)) = (x = z)`--);
  

M P51;  

val P52 = 
 (--`(?z w:'a. !x y. F0 x y = (x = z) /\ (y = w)) ==>
        ?w:'a. !y. (?z. !x:'a. F0 x y = (x = z)) = (y = w)`--);
M P52;;


(*** Too slow

val P53 = 
 (--`(?x y. ~(x = y) /\ !z. (z = x) \/ (z = y)) ==>
     ((?z. !x. (?w. !y. F0 x y = (y = w)) = (x = z)) =
      (?w. !y. (?z. !x. F0 x y = (x = z)) = (y = w)))`--);


val P54 = Tactical.prove(GEN_MESON_TAC 
 (--`(!y. ?z. !x. F0 x z = (x = y)) ==>
    ~?w. !x. F0 x w = !u. F0 x u ==> ?y. F0 y u /\ ~ ?z. F0 x u /\ F0 z y`--));


*****)

(* hol90 - yes? (too slow) *)
val P55 = 
 (--`(?x:'a. lives x /\ killed x agatha) /\
   (lives(agatha) /\ lives(butler) /\ lives(charles)) /\
   (!x. lives(x) ==> (x = agatha) \/ (x = butler) \/ (x = charles)) /\
   (!y x. killed x y ==> hates x y) /\
   (!x y. killed x y ==> ~richer x y) /\
   (!x. hates agatha x ==> ~hates charles x) /\
   (!x. ~(x = butler) ==> hates agatha x) /\
   (!x. ~richer x agatha ==> hates butler x) /\
   (!x. hates agatha x ==> hates butler x) /\
   (!x. ?y. ~hates x y) /\
   ~(agatha = butler)
   ==> killed agatha agatha`--);
  

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(* hol90 - yes *)
val P50 = 
 (--`(!x:'a. P(a,x) \/ (!y. P(x,y))) ==> ?x. !y. P(x,y)`--);


(* ========================================================================= *)
(* 100 problems selected from the TPTP library as a test for MESON_TAC.      *)
(* ========================================================================= *)

(*
 * These should all work with the default settings, but some are quite slow
 * (many minutes).
 *
 * A few variable names have been primed to avoid clashing with constants.
 *
 * Here's a list giving typical CPU times, as well as common names and
 * literature references.
 *
 * BOO003-1     34.6    B2 part 1 [McCharen, et al., 1976]; Lemma d [Overbeek, et al., 1976]; prob2_part1.ver1.in [ANL]
 * BOO004-1     36.7    B2 part 2 [McCharen, et al., 1976]; Lemma d [Overbeek, et al., 1976]; prob2_part2.ver1 [ANL]
 * BOO005-1     47.4    B3 part 1 [McCharen, et al., 1976]; B5 [McCharen, et al., 1976]; Lemma d [Overbeek, et al., 1976]; prob3_part1.ver1.in [ANL]
 * BOO006-1     48.4    B3 part 2 [McCharen, et al., 1976]; B6 [McCharen, et al., 1976]; Lemma d [Overbeek, et al., 1976]; prob3_part2.ver1 [ANL]
 * BOO011-1     19.0    B7 [McCharen, et al., 1976]; prob7.ver1 [ANL]
 * CAT001-3     45.2    C1 [McCharen, et al., 1976]; p1.ver3.in [ANL]
 * CAT003-3     10.5    C3 [McCharen, et al., 1976]; p3.ver3.in [ANL]
 * CAT005-1    480.1    C5 [McCharen, et al., 1976]; p5.ver1.in [ANL]
 * CAT007-1     11.9    C7 [McCharen, et al., 1976]; p7.ver1.in [ANL]
 * CAT018-1     81.3    p18.ver1.in [ANL]
 * COL001-2     16.0    C1 [Wos & McCune, 1988]
 * COL023-1      5.1    [McCune & Wos, 1988]
 * COL032-1     15.8    [McCune & Wos, 1988]
 * COL052-2     13.2    bird4.ver2.in [ANL]
 * COL075-2    116.9    [Jech, 1994]
 * COM001-1      1.7    shortburst [Wilson & Minker, 1976]
 * COM002-1      4.4    burstall [Wilson & Minker, 1976]
 * COM002-2      7.4
 * COM003-2     22.1    [Brushi, 1991]
 * COM004-1     45.1
 * GEO003-1     71.7    T3 [McCharen, et al., 1976]; t3.ver1.in [ANL]
 * GEO017-2     78.8    D4.1 [Quaife, 1989]
 * GEO027-3    181.5    D10.1 [Quaife, 1989]
 * GEO058-2    104.0    R4 [Quaife, 1989]
 * GEO079-1      2.4    GEOMETRY THEOREM [Slagle, 1967]
 * GRP001-1     47.8    CADE-11 Competition 1 [Overbeek, 1990]; G1 [McCharen, et al., 1976]; THEOREM 1 [Lusk & McCune, 1993]; wos10 [Wilson & Minker, 1976]; xsquared.ver1.in [ANL]; [Robinson, 1963]
 * GRP008-1     50.4    Problem 4 [Wos, 1965]; wos4 [Wilson & Minker, 1976]
 * GRP013-1     40.2    Problem 11 [Wos, 1965]; wos11 [Wilson & Minker, 1976]
 * GRP037-3     43.8    Problem 17 [Wos, 1965]; wos17 [Wilson & Minker, 1976]
 * GRP031-2      3.2    ls23 [Lawrence & Starkey, 1974]; ls23 [Wilson & Minker, 1976]
 * GRP034-4      2.5    ls26 [Lawrence & Starkey, 1974]; ls26 [Wilson & Minker, 1976]
 * GRP047-2     11.7    [Veroff, 1992]
 * GRP130-1    170.6    Bennett QG8 [TPTP]; QG8 [Slaney, 1993]
 * GRP156-1     48.7    ax_mono1c [Schulz, 1995]
 * GRP168-1    159.1    p01a [Schulz, 1995]
 * HEN003-3     39.9    HP3 [McCharen, et al., 1976]
 * HEN007-2    125.7    H7 [McCharen, et al., 1976]
 * HEN008-4     62.0    H8 [McCharen, et al., 1976]
 * HEN009-5    136.3    H9 [McCharen, et al., 1976]; hp9.ver3.in [ANL]
 * HEN012-3     48.5    new.ver2.in [ANL]
 * LCL010-1    370.9    EC-73 [McCune & Wos, 1992]; ec_yq.in [OTTER]
 * LCL077-2     51.6    morgan.two.ver1.in [ANL]
 * LCL082-1     14.6    IC-1.1 [Wos, et al., 1990]; IC-65 [McCune & Wos, 1992]; ls2 [SETHEO]; S1 [Pfenning, 1988]
 * LCL111-1    585.6    CADE-11 Competition 6 [Overbeek, 1990]; mv25.in [OTTER]; MV-57 [McCune & Wos, 1992]; mv.in part 2 [OTTER]; ovb6 [SETHEO]; THEOREM 6 [Lusk & McCune, 1993]
 * LCL143-1     10.9    Lattice structure theorem 2 [Bonacina, 1991]
 * LCL182-1    271.6    Problem 2.16 [Whitehead & Russell, 1927]
 * LCL200-1     12.0    Problem 2.46 [Whitehead & Russell, 1927]
 * LCL215-1    214.4    Problem 2.62 [Whitehead & Russell, 1927]; Problem 2.63 [Whitehead & Russell, 1927]
 * LCL230-2      0.2    Pelletier 5 [Pelletier, 1986]
 * LDA003-1     68.5    Problem 3 [Jech, 1993]
 * MSC002-1      9.2    DBABHP [Michie, et al., 1972]; DBABHP [Wilson & Minker, 1976]
 * MSC003-1      3.2    HASPARTS-T1 [Wilson & Minker, 1976]
 * MSC004-1      9.3    HASPARTS-T2 [Wilson & Minker, 1976]
 * MSC005-1      1.8    Problem 5.1 [Plaisted, 1982]
 * MSC006-1     39.0    nonob.lop [SETHEO]
 * NUM001-1     14.0    Chang-Lee-10a [Chang, 1970]; ls28 [Lawrence & Starkey, 1974]; ls28 [Wilson & Minker, 1976]
 * NUM021-1     52.3    ls65 [Lawrence & Starkey, 1974]; ls65 [Wilson & Minker, 1976]
 * NUM024-1     64.6    ls75 [Lawrence & Starkey, 1974]; ls75 [Wilson & Minker, 1976]
 * NUM180-1    621.2    LIM2.1 [Quaife]
 * NUM228-1    575.9    TRECDEF4 cor. [Quaife]
 * PLA002-1     37.4    Problem 5.7 [Plaisted, 1982]
 * PLA006-1      7.2    [Segre & Elkan, 1994]
 * PLA017-1    484.8    [Segre & Elkan, 1994]
 * PLA022-1     19.1    [Segre & Elkan, 1994]
 * PLA022-2     19.7    [Segre & Elkan, 1994]
 * PRV001-1     10.3    PV1 [McCharen, et al., 1976]
 * PRV003-1      3.9    E2 [McCharen, et al., 1976]; v2.lop [SETHEO]
 * PRV005-1      4.3    E4 [McCharen, et al., 1976]; v4.lop [SETHEO]
 * PRV006-1      6.0    E5 [McCharen, et al., 1976]; v5.lop [SETHEO]
 * PRV009-1      2.2    Hoares FIND [Bledsoe, 1977]; Problem 5.5 [Plaisted, 1982]
 * PUZ012-1      3.5    Boxes-of-fruit [Wos, 1988]; Boxes-of-fruit [Wos, et al., 1992]; boxes.ver1.in [ANL]
 * PUZ020-1     56.6    knightknave.in [ANL]
 * PUZ025-1     58.4    Problem 35 [Smullyan, 1978]; tandl35.ver1.in [ANL]
 * PUZ029-1      5.1    pigs.ver1.in [ANL]
 * RNG001-3     82.4    EX6-T? [Wilson & Minker, 1976]; ex6.lop [SETHEO]; Example 6a [Fleisig, et al., 1974]; FEX6T1 [SPRFN]; FEX6T2 [SPRFN]
 * RNG001-5    399.8    Problem 21 [Wos, 1965]; wos21 [Wilson & Minker, 1976]
 * RNG011-5      8.4    CADE-11 Competition Eq-10 [Overbeek, 1990]; PROBLEM 10 [Zhang, 1993]; THEOREM EQ-10 [Lusk & McCune, 1993]
 * RNG023-6      9.1    [Stevens, 1987]
 * RNG028-2      9.3    PROOF III [Anantharaman & Hsiang, 1990]
 * RNG038-2     16.2    Problem 27 [Wos, 1965]; wos27 [Wilson & Minker, 1976]
 * RNG040-2    180.5    Problem 29 [Wos, 1965]; wos29 [Wilson & Minker, 1976]
 * RNG041-1     35.8    Problem 30 [Wos, 1965]; wos30 [Wilson & Minker, 1976]
 * ROB010-1    205.0    Lemma 3.3 [Winker, 1990]; RA2 [Lusk & Wos, 1992]
 * ROB013-1     23.6    Lemma 3.5 [Winker, 1990]
 * ROB016-1     15.2    Corollary 3.7 [Winker, 1990]
 * ROB021-1    230.4    [McCune, 1992]
 * SET005-1    192.2    ls108 [Lawrence & Starkey, 1974]; ls108 [Wilson & Minker, 1976]
 * SET009-1     10.5    ls116 [Lawrence & Starkey, 1974]; ls116 [Wilson & Minker, 1976]
 * SET025-4    694.7    Lemma 10 [Boyer, et al, 1986]
 * SET046-5      2.3    p42.in [ANL]; Pelletier 42 [Pelletier, 1986]
 * SET047-5      3.7    p43.in [ANL]; Pelletier 43 [Pelletier, 1986]
 * SYN034-1      2.8    QW [Michie, et al., 1972]; QW [Wilson & Minker, 1976]
 * SYN071-1      1.9    Pelletier 48 [Pelletier, 1986]
 * SYN349-1     61.7    Ch17N5 [Tammet, 1994]
 * SYN352-1      5.5    Ch18N4 [Tammet, 1994]
 * TOP001-2     61.1    Lemma 1a [Wick & McCune, 1989]
 * TOP002-2      0.4    Lemma 1b [Wick & McCune, 1989]
 * TOP004-1    181.6    Lemma 1d [Wick & McCune, 1989]
 * TOP004-2      9.0    Lemma 1d [Wick & McCune, 1989]
 * TOP005-2    139.8    Lemma 1e [Wick & McCune, 1989]
 *)

val BOOL =
(--`(!(X:'a). equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. sum(X,Y,add(X,Y))) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!Y X Z. sum(X,Y,Z) ==> sum(Y,X,Z)) /\
   (!Y X Z. product(X,Y,Z) ==> product(Y,X,Z)) /\
   (!X. sum(additive_identity,X,X)) /\
   (!X. sum(X,additive_identity,X)) /\
   (!X. product(multiplicative_identity,X,X)) /\
   (!X. product(X,multiplicative_identity,X)) /\
   (!Y Z X V3 V1 V2 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ product(X,V3,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(X,V3,V4)) /\
   (!Y Z V3 X V1 V2 V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ product(V3,X,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 V3 X V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(V3,X,V4)) /\
   (!Y Z X V3 V1 V2 V4. sum(X,Y,V1) /\ sum(X,Z,V2) /\ product(Y,Z,V3) /\ sum(X,V3,V4) ==> product(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. sum(X,Y,V1) /\ sum(X,Z,V2) /\ product(Y,Z,V3) /\ product(V1,V2,V4) ==> sum(X,V3,V4)) /\
   (!Y Z V3 X V1 V2 V4. sum(Y,X,V1) /\ sum(Z,X,V2) /\ product(Y,Z,V3) /\ sum(V3,X,V4) ==> product(V1,V2,V4)) /\
   (!Y Z V1 V2 V3 X V4. sum(Y,X,V1) /\ sum(Z,X,V2) /\ product(Y,Z,V3) /\ product(V1,V2,V4) ==> sum(V3,X,V4)) /\
   (!X. sum(inverse(X),X,multiplicative_identity)) /\
   (!X. sum(X,inverse(X),multiplicative_identity)) /\
   (!X. product(inverse(X),X,additive_identity)) /\
   (!X. product(X,inverse(X),additive_identity)) /\
   (!X Y U V. sum(X,Y,U) /\ sum(X,Y,V) ==> equal(U,V)) /\
   (!X Y U V. product(X,Y,U) /\ product(X,Y,V) ==> equal(U,V)) /\
   (!X Y W Z. equal(X,Y) /\ sum(X,W,Z) ==> sum(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ sum(W,X,Z) ==> sum(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ sum(W,Z,X) ==> sum(W,Z,Y)) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!X Y W. equal(X,Y) ==> equal(add(X,W),add(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(add(W,X),add(W,Y))) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y. equal(X,Y) ==> equal(inverse(X),inverse(Y)))`--);;

open Meson;
val BOOL_FACTS = mk_mset[BOOL];

fun MESON msets thms tm = (tm,MESON_TAC msets thms);

(* hol90 - yes *)
val BOO003_1 = MESON [BOOL_FACTS] [] (--`product((x:'a),x,x):bool`--);;

(* hol90 - yes *)
val BOO004_1 = MESON [BOOL_FACTS] [] (--`sum((x:'a),x,x):bool`--);;

(* hol90 - yes *)
val BOO005_1 = MESON [BOOL_FACTS] [] (--`sum((x:'a),(multiplicative_identity:'a),multiplicative_identity):bool`--);;

(* hol90 - yes *)
val BOO006_1 = MESON [BOOL_FACTS] [] (--`product((x:'a),(additive_identity:'a),additive_identity):bool`--);;

(* hol90 - yes *)
val BOO011_1 = MESON [BOOL_FACTS] [] (--`equal((inverse(additive_identity:'a):'a),(multiplicative_identity:'a)):bool`--);;

val CAT001_3 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equivalent(X,Y) ==> there_exists(X)) /\
   (!X Y. equivalent(X,Y) ==> equal(X,Y)) /\
   (!X Y. there_exists(X) /\ equal(X,Y) ==> equivalent(X,Y)) /\
   (!X. there_exists(domain(X)) ==> there_exists(X)) /\
   (!X. there_exists(codomain(X)) ==> there_exists(X)) /\
   (!Y X. there_exists(compose(X,Y)) ==> there_exists(domain(X))) /\
   (!X Y. there_exists(compose(X,Y)) ==> equal(domain(X),codomain(Y))) /\
   (!X Y. there_exists(domain(X)) /\ equal(domain(X),codomain(Y)) ==> there_exists(compose(X,Y))) /\
   (!X Y Z. equal(compose(X,compose(Y,Z)),compose(compose(X,Y),Z))) /\
   (!X. equal(compose(X,domain(X)),X)) /\
   (!X. equal(compose(codomain(X),X),X)) /\
   (!X Y. equivalent(X,Y) ==> there_exists(Y)) /\
   (!X Y. there_exists(X) /\ there_exists(Y) /\ equal(X,Y) ==> equivalent(X,Y)) /\
   (!Y X. there_exists(compose(X,Y)) ==> there_exists(codomain(X))) /\
   (!X Y. there_exists(f1(X,Y)) \/ equal(X,Y)) /\
   (!X Y. equal(X,f1(X,Y)) \/ equal(Y,f1(X,Y)) \/ equal(X,Y)) /\
   (!X Y. equal(X,f1(X,Y)) /\ equal(Y,f1(X,Y)) ==> equal(X,Y)) /\
   (!X Y. equal(X,Y) /\ there_exists(X) ==> there_exists(Y)) /\
   (!X Y Z. equal(X,Y) /\ equivalent(X,Z) ==> equivalent(Y,Z)) /\
   (!X Z Y. equal(X,Y) /\ equivalent(Z,X) ==> equivalent(Z,Y)) /\
   (!X Y. equal(X,Y) ==> equal(domain(X),domain(Y))) /\
   (!X Y. equal(X,Y) ==> equal(codomain(X),codomain(Y))) /\
   (!X Y Z. equal(X,Y) ==> equal(compose(X,Z),compose(Y,Z))) /\
   (!X Z Y. equal(X,Y) ==> equal(compose(Z,X),compose(Z,Y))) /\
   (!A B C. equal(A,B) ==> equal(f1(A,C),f1(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(f1(F',D),f1(F',E))) /\
   (there_exists(compose(a,b))) /\
   (!Y X Z. equal(compose(compose(a,b),X),Y) /\ equal(compose(compose(a,b),Z),Y) ==> equal(X,Z)) /\
   (there_exists(compose(b,h))) /\
   (equal(compose(b,h),compose(b,g))) /\
   (~equal(h,g)) ==> F`--);
  

val CAT003_3 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equivalent(X,Y) ==> there_exists(X)) /\
   (!X Y. equivalent(X,Y) ==> equal(X,Y)) /\
   (!X Y. there_exists(X) /\ equal(X,Y) ==> equivalent(X,Y)) /\
   (!X. there_exists(domain(X)) ==> there_exists(X)) /\
   (!X. there_exists(codomain(X)) ==> there_exists(X)) /\
   (!Y X. there_exists(compose(X,Y)) ==> there_exists(domain(X))) /\
   (!X Y. there_exists(compose(X,Y)) ==> equal(domain(X),codomain(Y))) /\
   (!X Y. there_exists(domain(X)) /\ equal(domain(X),codomain(Y)) ==> there_exists(compose(X,Y))) /\
   (!X Y Z. equal(compose(X,compose(Y,Z)),compose(compose(X,Y),Z))) /\
   (!X. equal(compose(X,domain(X)),X)) /\
   (!X. equal(compose(codomain(X),X),X)) /\
   (!X Y. equivalent(X,Y) ==> there_exists(Y)) /\
   (!X Y. there_exists(X) /\ there_exists(Y) /\ equal(X,Y) ==> equivalent(X,Y)) /\
   (!Y X. there_exists(compose(X,Y)) ==> there_exists(codomain(X))) /\
   (!X Y. there_exists(f1(X,Y)) \/ equal(X,Y)) /\
   (!X Y. equal(X,f1(X,Y)) \/ equal(Y,f1(X,Y)) \/ equal(X,Y)) /\
   (!X Y. equal(X,f1(X,Y)) /\ equal(Y,f1(X,Y)) ==> equal(X,Y)) /\
   (!X Y. equal(X,Y) /\ there_exists(X) ==> there_exists(Y)) /\
   (!X Y Z. equal(X,Y) /\ equivalent(X,Z) ==> equivalent(Y,Z)) /\
   (!X Z Y. equal(X,Y) /\ equivalent(Z,X) ==> equivalent(Z,Y)) /\
   (!X Y. equal(X,Y) ==> equal(domain(X),domain(Y))) /\
   (!X Y. equal(X,Y) ==> equal(codomain(X),codomain(Y))) /\
   (!X Y Z. equal(X,Y) ==> equal(compose(X,Z),compose(Y,Z))) /\
   (!X Z Y. equal(X,Y) ==> equal(compose(Z,X),compose(Z,Y))) /\
   (!A B C. equal(A,B) ==> equal(f1(A,C),f1(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(f1(F',D),f1(F',E))) /\
   (there_exists(compose(a,b))) /\
   (!Y X Z. equal(compose(X,compose(a,b)),Y) /\ equal(compose(Z,compose(a,b)),Y) ==> equal(X,Z)) /\
   (there_exists(h)) /\
   (equal(compose(h,a),compose(g,a))) /\
   (~equal(g,h)) ==> F`--);
  

val CAT005_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. defined(X,Y) ==> product(X,Y,compose(X,Y))) /\
   (!Z X Y. product(X,Y,Z) ==> defined(X,Y)) /\
   (!X Xy Y Z. product(X,Y,Xy) /\ defined(Xy,Z) ==> defined(Y,Z)) /\
   (!Y Xy Z X Yz. product(X,Y,Xy) /\ product(Y,Z,Yz) /\ defined(Xy,Z) ==> defined(X,Yz)) /\
   (!Xy Y Z X Yz Xyz. product(X,Y,Xy) /\ product(Xy,Z,Xyz) /\ product(Y,Z,Yz) ==> product(X,Yz,Xyz)) /\
   (!Z Yz X Y. product(Y,Z,Yz) /\ defined(X,Yz) ==> defined(X,Y)) /\
   (!Y X Yz Xy Z. product(Y,Z,Yz) /\ product(X,Y,Xy) /\ defined(X,Yz) ==> defined(Xy,Z)) /\
   (!Yz X Y Xy Z Xyz. product(Y,Z,Yz) /\ product(X,Yz,Xyz) /\ product(X,Y,Xy) ==> product(Xy,Z,Xyz)) /\
   (!Y X Z. defined(X,Y) /\ defined(Y,Z) /\ identity_map(Y) ==> defined(X,Z)) /\
   (!X. identity_map(domain(X))) /\
   (!X. identity_map(codomain(X))) /\
   (!X. defined(X,domain(X))) /\
   (!X. defined(codomain(X),X)) /\
   (!X. product(X,domain(X),X)) /\
   (!X. product(codomain(X),X,X)) /\
   (!X Y. defined(X,Y) /\ identity_map(X) ==> product(X,Y,Y)) /\
   (!Y X. defined(X,Y) /\ identity_map(Y) ==> product(X,Y,X)) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!X Y Z W. equal(X,Y) /\ product(X,Z,W) ==> product(Y,Z,W)) /\
   (!X Z Y W. equal(X,Y) /\ product(Z,X,W) ==> product(Z,Y,W)) /\
   (!X Z W Y. equal(X,Y) /\ product(Z,W,X) ==> product(Z,W,Y)) /\
   (!X Y. equal(X,Y) ==> equal(domain(X),domain(Y))) /\
   (!X Y. equal(X,Y) ==> equal(codomain(X),codomain(Y))) /\
   (!X Y. equal(X,Y) /\ identity_map(X) ==> identity_map(Y)) /\
   (!X Y Z. equal(X,Y) /\ defined(X,Z) ==> defined(Y,Z)) /\
   (!X Z Y. equal(X,Y) /\ defined(Z,X) ==> defined(Z,Y)) /\
   (!X Z Y. equal(X,Y) ==> equal(compose(Z,X),compose(Z,Y))) /\
   (!X Y Z. equal(X,Y) ==> equal(compose(X,Z),compose(Y,Z))) /\
   (defined(a,d)) /\
   (identity_map(d)) /\
   (~equal(domain(a),d)) ==> F`--);
  

val CAT007_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. defined(X,Y) ==> product(X,Y,compose(X,Y))) /\
   (!Z X Y. product(X,Y,Z) ==> defined(X,Y)) /\
   (!X Xy Y Z. product(X,Y,Xy) /\ defined(Xy,Z) ==> defined(Y,Z)) /\
   (!Y Xy Z X Yz. product(X,Y,Xy) /\ product(Y,Z,Yz) /\ defined(Xy,Z) ==> defined(X,Yz)) /\
   (!Xy Y Z X Yz Xyz. product(X,Y,Xy) /\ product(Xy,Z,Xyz) /\ product(Y,Z,Yz) ==> product(X,Yz,Xyz)) /\
   (!Z Yz X Y. product(Y,Z,Yz) /\ defined(X,Yz) ==> defined(X,Y)) /\
   (!Y X Yz Xy Z. product(Y,Z,Yz) /\ product(X,Y,Xy) /\ defined(X,Yz) ==> defined(Xy,Z)) /\
   (!Yz X Y Xy Z Xyz. product(Y,Z,Yz) /\ product(X,Yz,Xyz) /\ product(X,Y,Xy) ==> product(Xy,Z,Xyz)) /\
   (!Y X Z. defined(X,Y) /\ defined(Y,Z) /\ identity_map(Y) ==> defined(X,Z)) /\
   (!X. identity_map(domain(X))) /\
   (!X. identity_map(codomain(X))) /\
   (!X. defined(X,domain(X))) /\
   (!X. defined(codomain(X),X)) /\
   (!X. product(X,domain(X),X)) /\
   (!X. product(codomain(X),X,X)) /\
   (!X Y. defined(X,Y) /\ identity_map(X) ==> product(X,Y,Y)) /\
   (!Y X. defined(X,Y) /\ identity_map(Y) ==> product(X,Y,X)) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!X Y Z W. equal(X,Y) /\ product(X,Z,W) ==> product(Y,Z,W)) /\
   (!X Z Y W. equal(X,Y) /\ product(Z,X,W) ==> product(Z,Y,W)) /\
   (!X Z W Y. equal(X,Y) /\ product(Z,W,X) ==> product(Z,W,Y)) /\
   (!X Y. equal(X,Y) ==> equal(domain(X),domain(Y))) /\
   (!X Y. equal(X,Y) ==> equal(codomain(X),codomain(Y))) /\
   (!X Y. equal(X,Y) /\ identity_map(X) ==> identity_map(Y)) /\
   (!X Y Z. equal(X,Y) /\ defined(X,Z) ==> defined(Y,Z)) /\
   (!X Z Y. equal(X,Y) /\ defined(Z,X) ==> defined(Z,Y)) /\
   (!X Z Y. equal(X,Y) ==> equal(compose(Z,X),compose(Z,Y))) /\
   (!X Y Z. equal(X,Y) ==> equal(compose(X,Z),compose(Y,Z))) /\
   (equal(domain(a),codomain(b))) /\
   (~defined(a,b)) ==> F`--);
  

val CAT018_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. defined(X,Y) ==> product(X,Y,compose(X,Y))) /\
   (!Z X Y. product(X,Y,Z) ==> defined(X,Y)) /\
   (!X Xy Y Z. product(X,Y,Xy) /\ defined(Xy,Z) ==> defined(Y,Z)) /\
   (!Y Xy Z X Yz. product(X,Y,Xy) /\ product(Y,Z,Yz) /\ defined(Xy,Z) ==> defined(X,Yz)) /\
   (!Xy Y Z X Yz Xyz. product(X,Y,Xy) /\ product(Xy,Z,Xyz) /\ product(Y,Z,Yz) ==> product(X,Yz,Xyz)) /\
   (!Z Yz X Y. product(Y,Z,Yz) /\ defined(X,Yz) ==> defined(X,Y)) /\
   (!Y X Yz Xy Z. product(Y,Z,Yz) /\ product(X,Y,Xy) /\ defined(X,Yz) ==> defined(Xy,Z)) /\
   (!Yz X Y Xy Z Xyz. product(Y,Z,Yz) /\ product(X,Yz,Xyz) /\ product(X,Y,Xy) ==> product(Xy,Z,Xyz)) /\
   (!Y X Z. defined(X,Y) /\ defined(Y,Z) /\ identity_map(Y) ==> defined(X,Z)) /\
   (!X. identity_map(domain(X))) /\
   (!X. identity_map(codomain(X))) /\
   (!X. defined(X,domain(X))) /\
   (!X. defined(codomain(X),X)) /\
   (!X. product(X,domain(X),X)) /\
   (!X. product(codomain(X),X,X)) /\
   (!X Y. defined(X,Y) /\ identity_map(X) ==> product(X,Y,Y)) /\
   (!Y X. defined(X,Y) /\ identity_map(Y) ==> product(X,Y,X)) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!X Y Z W. equal(X,Y) /\ product(X,Z,W) ==> product(Y,Z,W)) /\
   (!X Z Y W. equal(X,Y) /\ product(Z,X,W) ==> product(Z,Y,W)) /\
   (!X Z W Y. equal(X,Y) /\ product(Z,W,X) ==> product(Z,W,Y)) /\
   (!X Y. equal(X,Y) ==> equal(domain(X),domain(Y))) /\
   (!X Y. equal(X,Y) ==> equal(codomain(X),codomain(Y))) /\
   (!X Y. equal(X,Y) /\ identity_map(X) ==> identity_map(Y)) /\
   (!X Y Z. equal(X,Y) /\ defined(X,Z) ==> defined(Y,Z)) /\
   (!X Z Y. equal(X,Y) /\ defined(Z,X) ==> defined(Z,Y)) /\
   (!X Z Y. equal(X,Y) ==> equal(compose(Z,X),compose(Z,Y))) /\
   (!X Y Z. equal(X,Y) ==> equal(compose(X,Z),compose(Y,Z))) /\
   (defined(a,b)) /\
   (defined(b,c)) /\
   (~defined(a,compose(b,c))) ==> F`--);
  

val COL001_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y Z. equal(apply(apply(apply(s,X),Y),Z),apply(apply(X,Z),apply(Y,Z)))) /\
   (!Y X. equal(apply(apply(k,X),Y),X)) /\
   (!X Y Z. equal(apply(apply(apply(b,X),Y),Z),apply(X,apply(Y,Z)))) /\
   (!X. equal(apply(i,X),X)) /\
   (!A B C. equal(A,B) ==> equal(apply(A,C),apply(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(apply(F',D),apply(F',E))) /\
   (!X. equal(apply(apply(apply(s,apply(b,X)),i),apply(apply(s,apply(b,X)),i)),apply(x,apply(apply(apply(s,apply(b,X)),i),apply(apply(s,apply(b,X)),i))))) /\
   (!Y. ~equal(Y,apply(combinator,Y))) ==> F`--);
  

val COL023_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y Z. equal(apply(apply(apply(b,X),Y),Z),apply(X,apply(Y,Z)))) /\
   (!X Y Z. equal(apply(apply(apply(n,X),Y),Z),apply(apply(apply(X,Z),Y),Z))) /\
   (!A B C. equal(A,B) ==> equal(apply(A,C),apply(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(apply(F',D),apply(F',E))) /\
   (!Y. ~equal(Y,apply(combinator,Y))) ==> F`--);
  

val COL032_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(apply(m,X),apply(X,X))) /\
   (!Y X Z. equal(apply(apply(apply(q,X),Y),Z),apply(Y,apply(X,Z)))) /\
   (!A B C. equal(A,B) ==> equal(apply(A,C),apply(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(apply(F',D),apply(F',E))) /\
   (!G H. equal(G,H) ==> equal(f(G),f(H))) /\
   (!Y. ~equal(apply(Y,f(Y)),apply(f(Y),apply(Y,f(Y))))) ==> F`--);
  

val COL052_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y W. equal(response(compose(X,Y),W),response(X,response(Y,W)))) /\
   (!X Y. agreeable(X) ==> equal(response(X,common_bird(Y)),response(Y,common_bird(Y)))) /\
   (!Z X. equal(response(X,Z),response(compatible(X),Z)) ==> agreeable(X)) /\
   (!A B. equal(A,B) ==> equal(common_bird(A),common_bird(B))) /\
   (!C D. equal(C,D) ==> equal(compatible(C),compatible(D))) /\
   (!Q R. equal(Q,R) /\ agreeable(Q) ==> agreeable(R)) /\
   (!A B C. equal(A,B) ==> equal(compose(A,C),compose(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(compose(F',D),compose(F',E))) /\
   (!G H I'. equal(G,H) ==> equal(response(G,I'),response(H,I'))) /\
   (!J L K'. equal(J,K') ==> equal(response(L,J),response(L,K'))) /\
   (agreeable(c)) /\
   (~agreeable(a)) /\
   (equal(c,compose(a,b))) ==> F`--);
  

val COL075_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(apply(apply(k,X),Y),X)) /\
   (!X Y Z. equal(apply(apply(apply(abstraction,X),Y),Z),apply(apply(X,apply(k,Z)),apply(Y,Z)))) /\
   (!D E F'. equal(D,E) ==> equal(apply(D,F'),apply(E,F'))) /\
   (!G I' H. equal(G,H) ==> equal(apply(I',G),apply(I',H))) /\
   (!A B. equal(A,B) ==> equal(b(A),b(B))) /\
   (!C D. equal(C,D) ==> equal(c(C),c(D))) /\
   (!Y. ~equal(apply(apply(Y,b(Y)),c(Y)),apply(b(Y),b(Y)))) ==> F`--);
  

val COM001_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Goal_state Start_state. 
        follows(Goal_state,Start_state)
             ==> succeeds(Goal_state,Start_state)) /\
   (!Goal_state Intermediate_state Start_state. 
         succeeds(Goal_state,Intermediate_state) /\ 
         succeeds(Intermediate_state,Start_state) 
            ==> succeeds(Goal_state,Start_state)) /\
   (!Start_state Label Goal_state. 
      has(Start_state,goto(Label)) /\ labels(Label,Goal_state) 
           ==> succeeds(Goal_state,Start_state)) /\
   (!Start_state Condition Goal_state. 
          has(Start_state,ifthen(Condition,Goal_state)) 
            ==> succeeds(Goal_state,Start_state)) /\
   (labels(loop,p3)) /\
   (has(p3,ifthen(equal(register_j,n),p4))) /\
   (has(p4,goto(out))) /\
   (follows(p5,p4)) /\
   (follows(p8,p3)) /\
   (has(p8,goto(loop))) /\
   (~succeeds(p3,p3)) ==> F`;
  

val COM002_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Goal_state Start_state. follows(Goal_state,Start_state) ==> succeeds(Goal_state,Start_state)) /\
   (!Goal_state Intermediate_state Start_state. succeeds(Goal_state,Intermediate_state) /\ succeeds(Intermediate_state,Start_state) ==> succeeds(Goal_state,Start_state)) /\
   (!Start_state Label Goal_state. has(Start_state,goto(Label)) /\ labels(Label,Goal_state) ==> succeeds(Goal_state,Start_state)) /\
   (!Start_state Condition Goal_state. has(Start_state,ifthen(Condition,Goal_state)) ==> succeeds(Goal_state,Start_state)) /\
   (has(p1,assign(register_j,0))) /\
   (follows(p2,p1)) /\
   (has(p2,assign(register_k,1))) /\
   (labels(loop,p3)) /\
   (follows(p3,p2)) /\
   (has(p3,ifthen(equal(register_j,n),p4))) /\
   (has(p4,goto(out))) /\
   (follows(p5,p4)) /\
   (follows(p6,p3)) /\
   (has(p6,assign(register_k,times(2,register_k)))) /\
   (follows(p7,p6)) /\
   (has(p7,assign(register_j,plus(register_j,1)))) /\
   (follows(p8,p7)) /\
   (has(p8,goto(loop))) /\
   (~succeeds(p3,p3)) ==> F`;
  

val COM002_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Goal_state Start_state. ~(fails(Goal_state,Start_state) /\ follows(Goal_state,Start_state))) /\
   (!Goal_state Intermediate_state Start_state. fails(Goal_state,Start_state) ==> fails(Goal_state,Intermediate_state) \/ fails(Intermediate_state,Start_state)) /\
   (!Start_state Label Goal_state. ~(fails(Goal_state,Start_state) /\ has(Start_state,goto(Label)) /\ labels(Label,Goal_state))) /\
   (!Start_state Condition Goal_state. ~(fails(Goal_state,Start_state) /\ has(Start_state,ifthen(Condition,Goal_state)))) /\
   (has(p1,assign(register_j,0))) /\
   (follows(p2,p1)) /\
   (has(p2,assign(register_k,1))) /\
   (labels(loop,p3)) /\
   (follows(p3,p2)) /\
   (has(p3,ifthen(equal(register_j,n),p4))) /\
   (has(p4,goto(out))) /\
   (follows(p5,p4)) /\
   (follows(p6,p3)) /\
   (has(p6,assign(register_k,times(2,register_k)))) /\
   (follows(p7,p6)) /\
   (has(p7,assign(register_j,plus(register_j,1)))) /\
   (follows(p8,p7)) /\
   (has(p8,goto(loop))) /\
   (fails(p3,p3)) ==> F`;
  

val COM003_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Y Z. program_decides(X) /\ program(Y) ==> decides(X,Y,Z)) /\
   (!X. program_decides(X) \/ program(f2(X))) /\
   (!X. decides(X,f2(X),f1(X)) ==> program_decides(X)) /\
   (!X. program_program_decides(X) ==> program(X)) /\
   (!X. program_program_decides(X) ==> program_decides(X)) /\
   (!X. program(X) /\ program_decides(X) ==> program_program_decides(X)) /\
   (!X. algorithm_program_decides(X) ==> algorithm(X)) /\
   (!X. algorithm_program_decides(X) ==> program_decides(X)) /\
   (!X. algorithm(X) /\ program_decides(X) ==> algorithm_program_decides(X)) /\
   (!Y X. program_halts2(X,Y) ==> program(X)) /\
   (!X Y. program_halts2(X,Y) ==> halts2(X,Y)) /\
   (!X Y. program(X) /\ halts2(X,Y) ==> program_halts2(X,Y)) /\
   (!W X Y Z. halts3_outputs(X,Y,Z,W) ==> halts3(X,Y,Z)) /\
   (!Y Z X W. halts3_outputs(X,Y,Z,W) ==> outputs(X,W)) /\
   (!Y Z X W. halts3(X,Y,Z) /\ outputs(X,W) ==> halts3_outputs(X,Y,Z,W)) /\
   (!Y X. program_not_halts2(X,Y) ==> program(X)) /\
   (!X Y. ~(program_not_halts2(X,Y) /\ halts2(X,Y))) /\
   (!X Y. program(X) ==> program_not_halts2(X,Y) \/ halts2(X,Y)) /\
   (!W X Y. halts2_outputs(X,Y,W) ==> halts2(X,Y)) /\
   (!Y X W. halts2_outputs(X,Y,W) ==> outputs(X,W)) /\
   (!Y X W. halts2(X,Y) /\ outputs(X,W) ==> halts2_outputs(X,Y,W)) /\
   (!X W Y Z. program_halts2_halts3_outputs(X,Y,Z,W) ==> program_halts2(Y,Z)) /\
   (!X Y Z W. program_halts2_halts3_outputs(X,Y,Z,W) ==> halts3_outputs(X,Y,Z,W)) /\
   (!X Y Z W. program_halts2(Y,Z) /\ halts3_outputs(X,Y,Z,W) ==> program_halts2_halts3_outputs(X,Y,Z,W)) /\
   (!X W Y Z. program_not_halts2_halts3_outputs(X,Y,Z,W) ==> program_not_halts2(Y,Z)) /\
   (!X Y Z W. program_not_halts2_halts3_outputs(X,Y,Z,W) ==> halts3_outputs(X,Y,Z,W)) /\
   (!X Y Z W. program_not_halts2(Y,Z) /\ halts3_outputs(X,Y,Z,W) ==> program_not_halts2_halts3_outputs(X,Y,Z,W)) /\
   (!X W Y. program_halts2_halts2_outputs(X,Y,W) ==> program_halts2(Y,Y)) /\
   (!X Y W. program_halts2_halts2_outputs(X,Y,W) ==> halts2_outputs(X,Y,W)) /\
   (!X Y W. program_halts2(Y,Y) /\ halts2_outputs(X,Y,W) ==> program_halts2_halts2_outputs(X,Y,W)) /\
   (!X W Y. program_not_halts2_halts2_outputs(X,Y,W) ==> program_not_halts2(Y,Y)) /\
   (!X Y W. program_not_halts2_halts2_outputs(X,Y,W) ==> halts2_outputs(X,Y,W)) /\
   (!X Y W. program_not_halts2(Y,Y) /\ halts2_outputs(X,Y,W) ==> program_not_halts2_halts2_outputs(X,Y,W)) /\
   (!X. algorithm_program_decides(X) ==> program_program_decides(c1)) /\
   (!W Y Z. program_program_decides(W) ==> program_halts2_halts3_outputs(W,Y,Z,good)) /\
   (!W Y Z. program_program_decides(W) ==> program_not_halts2_halts3_outputs(W,Y,Z,bad)) /\
   (!W. program(W) /\ program_halts2_halts3_outputs(W,f3(W),f3(W),good) /\ program_not_halts2_halts3_outputs(W,f3(W),f3(W),bad) ==> program(c2)) /\
   (!W Y. program(W) /\ program_halts2_halts3_outputs(W,f3(W),f3(W),good) /\ program_not_halts2_halts3_outputs(W,f3(W),f3(W),bad) ==> program_halts2_halts2_outputs(c2,Y,good)) /\
   (!W Y. program(W) /\ program_halts2_halts3_outputs(W,f3(W),f3(W),good) /\ program_not_halts2_halts3_outputs(W,f3(W),f3(W),bad) ==> program_not_halts2_halts2_outputs(c2,Y,bad)) /\
   (!V. program(V) /\ program_halts2_halts2_outputs(V,f4(V),good) /\ program_not_halts2_halts2_outputs(V,f4(V),bad) ==> program(c3)) /\
   (!V Y. program(V) /\ program_halts2_halts2_outputs(V,f4(V),good) /\ program_not_halts2_halts2_outputs(V,f4(V),bad) /\ program_halts2(Y,Y) ==> halts2(c3,Y)) /\
   (!V Y. program(V) /\ program_halts2_halts2_outputs(V,f4(V),good) /\ program_not_halts2_halts2_outputs(V,f4(V),bad) ==> program_not_halts2_halts2_outputs(c3,Y,bad)) /\
   (algorithm_program_decides(c4)) ==> F`;
  

val COM004_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!C D P Q X Y. failure_node(X,or(C,P)) /\ failure_node(Y,or(D,Q)) /\ contradictory(P,Q) /\ siblings(X,Y) ==> failure_node(parent_of(X,Y),or(C,D))) /\
   (!X. contradictory(negate(X),X)) /\
   (!X. contradictory(X,negate(X))) /\
   (!X. siblings(left_child_of(X),right_child_of(X))) /\
   (!D E. equal(D,E) ==> equal(left_child_of(D),left_child_of(E))) /\
   (!F' G. equal(F',G) ==> equal(negate(F'),negate(G))) /\
   (!H I' J. equal(H,I') ==> equal(or(H,J),or(I',J))) /\
   (!K' M L. equal(K',L) ==> equal(or(M,K'),or(M,L))) /\
   (!N O P. equal(N,O) ==> equal(parent_of(N,P),parent_of(O,P))) /\
   (!Q S' R. equal(Q,R) ==> equal(parent_of(S',Q),parent_of(S',R))) /\
   (!T' U. equal(T',U) ==> equal(right_child_of(T'),right_child_of(U))) /\
   (!V W X. equal(V,W) /\ contradictory(V,X) ==> contradictory(W,X)) /\
   (!Y A1 Z. equal(Y,Z) /\ contradictory(A1,Y) ==> contradictory(A1,Z)) /\
   (!B1 C1 D1. equal(B1,C1) /\ failure_node(B1,D1) ==> failure_node(C1,D1)) /\
   (!E1 G1 F1. equal(E1,F1) /\ failure_node(G1,E1) ==> failure_node(G1,F1)) /\
   (!H1 I1 J1. equal(H1,I1) /\ siblings(H1,J1) ==> siblings(I1,J1)) /\
   (!K1 M1 L1. equal(K1,L1) /\ siblings(M1,K1) ==> siblings(M1,L1)) /\
   (failure_node(n_left,or(empty,atom))) /\
   (failure_node(n_right,or(empty,negate(atom)))) /\
   (equal(n_left,left_child_of(n))) /\
   (equal(n_right,right_child_of(n))) /\
   (!Z. ~failure_node(Z,or(empty,empty))) ==> F`;
  

val GEO003_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. between(X,Y,X) ==> equal(X,Y)) /\
   (!V X Y Z. between(X,Y,V) /\ between(Y,Z,V) ==> between(X,Y,Z)) /\
   (!Y X V Z. between(X,Y,Z) /\ between(X,Y,V) ==> equal(X,Y) \/ between(X,Z,V) \/ between(X,V,Z)) /\
   (!Y X. equidistant(X,Y,Y,X)) /\
   (!Z X Y. equidistant(X,Y,Z,Z) ==> equal(X,Y)) /\
   (!X Y Z V V2 W. equidistant(X,Y,Z,V) /\ equidistant(X,Y,V2,W) ==> equidistant(Z,V,V2,W)) /\
   (!W X Z V Y. between(X,W,V) /\ between(Y,V,Z) ==> between(X,outer_pasch(W,X,Y,Z,V),Y)) /\
   (!W X Y Z V. between(X,W,V) /\ between(Y,V,Z) ==> between(Z,W,outer_pasch(W,X,Y,Z,V))) /\
   (!W X Y Z V. between(X,V,W) /\ between(Y,V,Z) ==> equal(X,V) \/ between(X,Z,euclid1(W,X,Y,Z,V))) /\
   (!W X Y Z V. between(X,V,W) /\ between(Y,V,Z) ==> equal(X,V) \/ between(X,Y,euclid2(W,X,Y,Z,V))) /\
   (!W X Y Z V. between(X,V,W) /\ between(Y,V,Z) ==> equal(X,V) \/ between(euclid1(W,X,Y,Z,V),W,euclid2(W,X,Y,Z,V))) /\
   (!X1 Y1 X Y Z V Z1 V1. equidistant(X,Y,X1,Y1) /\ equidistant(Y,Z,Y1,Z1) /\ equidistant(X,V,X1,V1) /\ equidistant(Y,V,Y1,V1) /\ between(X,Y,Z) /\ between(X1,Y1,Z1) ==> equal(X,Y) \/ equidistant(Z,V,Z1,V1)) /\
   (!X Y W V. between(X,Y,extension(X,Y,W,V))) /\
   (!X Y W V. equidistant(Y,extension(X,Y,W,V),W,V)) /\
   (~between(lower_dimension_point_1,lower_dimension_point_2,lower_dimension_point_3)) /\
   (~between(lower_dimension_point_2,lower_dimension_point_3,lower_dimension_point_1)) /\
   (~between(lower_dimension_point_3,lower_dimension_point_1,lower_dimension_point_2)) /\
   (!Z X Y W V. equidistant(X,W,X,V) /\ equidistant(Y,W,Y,V) /\ equidistant(Z,W,Z,V) ==> between(X,Y,Z) \/ between(Y,Z,X) \/ between(Z,X,Y) \/ equal(W,V)) /\
   (!X Y Z X1 Z1 V. equidistant(V,X,V,X1) /\ equidistant(V,Z,V,Z1) /\ between(V,X,Z) /\ between(X,Y,Z) ==> equidistant(V,Y,Z,continuous(X,Y,Z,X1,Z1,V))) /\
   (!X Y Z X1 V Z1. equidistant(V,X,V,X1) /\ equidistant(V,Z,V,Z1) /\ between(V,X,Z) /\ between(X,Y,Z) ==> between(X1,continuous(X,Y,Z,X1,Z1,V),Z1)) /\
   (!X Y W Z. equal(X,Y) /\ between(X,W,Z) ==> between(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ between(W,X,Z) ==> between(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ between(W,Z,X) ==> between(W,Z,Y)) /\
   (!X Y V W Z. equal(X,Y) /\ equidistant(X,V,W,Z) ==> equidistant(Y,V,W,Z)) /\
   (!X V Y W Z. equal(X,Y) /\ equidistant(V,X,W,Z) ==> equidistant(V,Y,W,Z)) /\
   (!X V W Y Z. equal(X,Y) /\ equidistant(V,W,X,Z) ==> equidistant(V,W,Y,Z)) /\
   (!X V W Z Y. equal(X,Y) /\ equidistant(V,W,Z,X) ==> equidistant(V,W,Z,Y)) /\
   (!X Y V1 V2 V3 V4. equal(X,Y) ==> equal(outer_pasch(X,V1,V2,V3,V4),outer_pasch(Y,V1,V2,V3,V4))) /\
   (!X V1 Y V2 V3 V4. equal(X,Y) ==> equal(outer_pasch(V1,X,V2,V3,V4),outer_pasch(V1,Y,V2,V3,V4))) /\
   (!X V1 V2 Y V3 V4. equal(X,Y) ==> equal(outer_pasch(V1,V2,X,V3,V4),outer_pasch(V1,V2,Y,V3,V4))) /\
   (!X V1 V2 V3 Y V4. equal(X,Y) ==> equal(outer_pasch(V1,V2,V3,X,V4),outer_pasch(V1,V2,V3,Y,V4))) /\
   (!X V1 V2 V3 V4 Y. equal(X,Y) ==> equal(outer_pasch(V1,V2,V3,V4,X),outer_pasch(V1,V2,V3,V4,Y))) /\
   (!A B C D E F'. equal(A,B) ==> equal(euclid1(A,C,D,E,F'),euclid1(B,C,D,E,F'))) /\
   (!G I' H J K' L. equal(G,H) ==> equal(euclid1(I',G,J,K',L),euclid1(I',H,J,K',L))) /\
   (!M O P N Q R. equal(M,N) ==> equal(euclid1(O,P,M,Q,R),euclid1(O,P,N,Q,R))) /\
   (!S' U V W T' X. equal(S',T') ==> equal(euclid1(U,V,W,S',X),euclid1(U,V,W,T',X))) /\
   (!Y A1 B1 C1 D1 Z. equal(Y,Z) ==> equal(euclid1(A1,B1,C1,D1,Y),euclid1(A1,B1,C1,D1,Z))) /\
   (!E1 F1 G1 H1 I1 J1. equal(E1,F1) ==> equal(euclid2(E1,G1,H1,I1,J1),euclid2(F1,G1,H1,I1,J1))) /\
   (!K1 M1 L1 N1 O1 P1. equal(K1,L1) ==> equal(euclid2(M1,K1,N1,O1,P1),euclid2(M1,L1,N1,O1,P1))) /\
   (!Q1 S1 T1 R1 U1 V1. equal(Q1,R1) ==> equal(euclid2(S1,T1,Q1,U1,V1),euclid2(S1,T1,R1,U1,V1))) /\
   (!W1 Y1 Z1 A2 X1 B2. equal(W1,X1) ==> equal(euclid2(Y1,Z1,A2,W1,B2),euclid2(Y1,Z1,A2,X1,B2))) /\
   (!C2 E2 F2 G2 H2 D2. equal(C2,D2) ==> equal(euclid2(E2,F2,G2,H2,C2),euclid2(E2,F2,G2,H2,D2))) /\
   (!X Y V1 V2 V3. equal(X,Y) ==> equal(extension(X,V1,V2,V3),extension(Y,V1,V2,V3))) /\
   (!X V1 Y V2 V3. equal(X,Y) ==> equal(extension(V1,X,V2,V3),extension(V1,Y,V2,V3))) /\
   (!X V1 V2 Y V3. equal(X,Y) ==> equal(extension(V1,V2,X,V3),extension(V1,V2,Y,V3))) /\
   (!X V1 V2 V3 Y. equal(X,Y) ==> equal(extension(V1,V2,V3,X),extension(V1,V2,V3,Y))) /\
   (!X Y V1 V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(X,V1,V2,V3,V4,V5),continuous(Y,V1,V2,V3,V4,V5))) /\
   (!X V1 Y V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,X,V2,V3,V4,V5),continuous(V1,Y,V2,V3,V4,V5))) /\
   (!X V1 V2 Y V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,X,V3,V4,V5),continuous(V1,V2,Y,V3,V4,V5))) /\
   (!X V1 V2 V3 Y V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,X,V4,V5),continuous(V1,V2,V3,Y,V4,V5))) /\
   (!X V1 V2 V3 V4 Y V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,X,V5),continuous(V1,V2,V3,V4,Y,V5))) /\
   (!X V1 V2 V3 V4 V5 Y. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,V5,X),continuous(V1,V2,V3,V4,V5,Y))) /\
   (~between(a,b,b)) ==> F`--);
  

val GEO017_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equidistant(X,Y,Y,X)) /\
   (!X Y Z V V2 W. equidistant(X,Y,Z,V) /\ equidistant(X,Y,V2,W) ==> equidistant(Z,V,V2,W)) /\
   (!Z X Y. equidistant(X,Y,Z,Z) ==> equal(X,Y)) /\
   (!X Y W V. between(X,Y,extension(X,Y,W,V))) /\
   (!X Y W V. equidistant(Y,extension(X,Y,W,V),W,V)) /\
   (!X1 Y1 X Y Z V Z1 V1. equidistant(X,Y,X1,Y1) /\ equidistant(Y,Z,Y1,Z1) /\ equidistant(X,V,X1,V1) /\ equidistant(Y,V,Y1,V1) /\ between(X,Y,Z) /\ between(X1,Y1,Z1) ==> equal(X,Y) \/ equidistant(Z,V,Z1,V1)) /\
   (!X Y. between(X,Y,X) ==> equal(X,Y)) /\
   (!U V W X Y. between(U,V,W) /\ between(Y,X,W) ==> between(V,inner_pasch(U,V,W,X,Y),Y)) /\
   (!V W X Y U. between(U,V,W) /\ between(Y,X,W) ==> between(X,inner_pasch(U,V,W,X,Y),U)) /\
   (~between(lower_dimension_point_1,lower_dimension_point_2,lower_dimension_point_3)) /\
   (~between(lower_dimension_point_2,lower_dimension_point_3,lower_dimension_point_1)) /\
   (~between(lower_dimension_point_3,lower_dimension_point_1,lower_dimension_point_2)) /\
   (!Z X Y W V. equidistant(X,W,X,V) /\ equidistant(Y,W,Y,V) /\ equidistant(Z,W,Z,V) ==> between(X,Y,Z) \/ between(Y,Z,X) \/ between(Z,X,Y) \/ equal(W,V)) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(U,V,euclid1(U,V,W,X,Y))) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(U,X,euclid2(U,V,W,X,Y))) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(euclid1(U,V,W,X,Y),Y,euclid2(U,V,W,X,Y))) /\
   (!U V V1 W X X1. equidistant(U,V,U,V1) /\ equidistant(U,X,U,X1) /\ between(U,V,X) /\ between(V,W,X) ==> between(V1,continuous(U,V,V1,W,X,X1),X1)) /\
   (!U V V1 W X X1. equidistant(U,V,U,V1) /\ equidistant(U,X,U,X1) /\ between(U,V,X) /\ between(V,W,X) ==> equidistant(U,W,U,continuous(U,V,V1,W,X,X1))) /\
   (!X Y W Z. equal(X,Y) /\ between(X,W,Z) ==> between(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ between(W,X,Z) ==> between(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ between(W,Z,X) ==> between(W,Z,Y)) /\
   (!X Y V W Z. equal(X,Y) /\ equidistant(X,V,W,Z) ==> equidistant(Y,V,W,Z)) /\
   (!X V Y W Z. equal(X,Y) /\ equidistant(V,X,W,Z) ==> equidistant(V,Y,W,Z)) /\
   (!X V W Y Z. equal(X,Y) /\ equidistant(V,W,X,Z) ==> equidistant(V,W,Y,Z)) /\
   (!X V W Z Y. equal(X,Y) /\ equidistant(V,W,Z,X) ==> equidistant(V,W,Z,Y)) /\
   (!X Y V1 V2 V3 V4. equal(X,Y) ==> equal(inner_pasch(X,V1,V2,V3,V4),inner_pasch(Y,V1,V2,V3,V4))) /\
   (!X V1 Y V2 V3 V4. equal(X,Y) ==> equal(inner_pasch(V1,X,V2,V3,V4),inner_pasch(V1,Y,V2,V3,V4))) /\
   (!X V1 V2 Y V3 V4. equal(X,Y) ==> equal(inner_pasch(V1,V2,X,V3,V4),inner_pasch(V1,V2,Y,V3,V4))) /\
   (!X V1 V2 V3 Y V4. equal(X,Y) ==> equal(inner_pasch(V1,V2,V3,X,V4),inner_pasch(V1,V2,V3,Y,V4))) /\
   (!X V1 V2 V3 V4 Y. equal(X,Y) ==> equal(inner_pasch(V1,V2,V3,V4,X),inner_pasch(V1,V2,V3,V4,Y))) /\
   (!A B C D E F'. equal(A,B) ==> equal(euclid1(A,C,D,E,F'),euclid1(B,C,D,E,F'))) /\
   (!G I' H J K' L. equal(G,H) ==> equal(euclid1(I',G,J,K',L),euclid1(I',H,J,K',L))) /\
   (!M O P N Q R. equal(M,N) ==> equal(euclid1(O,P,M,Q,R),euclid1(O,P,N,Q,R))) /\
   (!S' U V W T' X. equal(S',T') ==> equal(euclid1(U,V,W,S',X),euclid1(U,V,W,T',X))) /\
   (!Y A1 B1 C1 D1 Z. equal(Y,Z) ==> equal(euclid1(A1,B1,C1,D1,Y),euclid1(A1,B1,C1,D1,Z))) /\
   (!E1 F1 G1 H1 I1 J1. equal(E1,F1) ==> equal(euclid2(E1,G1,H1,I1,J1),euclid2(F1,G1,H1,I1,J1))) /\
   (!K1 M1 L1 N1 O1 P1. equal(K1,L1) ==> equal(euclid2(M1,K1,N1,O1,P1),euclid2(M1,L1,N1,O1,P1))) /\
   (!Q1 S1 T1 R1 U1 V1. equal(Q1,R1) ==> equal(euclid2(S1,T1,Q1,U1,V1),euclid2(S1,T1,R1,U1,V1))) /\
   (!W1 Y1 Z1 A2 X1 B2. equal(W1,X1) ==> equal(euclid2(Y1,Z1,A2,W1,B2),euclid2(Y1,Z1,A2,X1,B2))) /\
   (!C2 E2 F2 G2 H2 D2. equal(C2,D2) ==> equal(euclid2(E2,F2,G2,H2,C2),euclid2(E2,F2,G2,H2,D2))) /\
   (!X Y V1 V2 V3. equal(X,Y) ==> equal(extension(X,V1,V2,V3),extension(Y,V1,V2,V3))) /\
   (!X V1 Y V2 V3. equal(X,Y) ==> equal(extension(V1,X,V2,V3),extension(V1,Y,V2,V3))) /\
   (!X V1 V2 Y V3. equal(X,Y) ==> equal(extension(V1,V2,X,V3),extension(V1,V2,Y,V3))) /\
   (!X V1 V2 V3 Y. equal(X,Y) ==> equal(extension(V1,V2,V3,X),extension(V1,V2,V3,Y))) /\
   (!X Y V1 V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(X,V1,V2,V3,V4,V5),continuous(Y,V1,V2,V3,V4,V5))) /\
   (!X V1 Y V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,X,V2,V3,V4,V5),continuous(V1,Y,V2,V3,V4,V5))) /\
   (!X V1 V2 Y V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,X,V3,V4,V5),continuous(V1,V2,Y,V3,V4,V5))) /\
   (!X V1 V2 V3 Y V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,X,V4,V5),continuous(V1,V2,V3,Y,V4,V5))) /\
   (!X V1 V2 V3 V4 Y V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,X,V5),continuous(V1,V2,V3,V4,Y,V5))) /\
   (!X V1 V2 V3 V4 V5 Y. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,V5,X),continuous(V1,V2,V3,V4,V5,Y))) /\
   (equidistant(u,v,w,x)) /\
   (~equidistant(u,v,x,w)) ==> F`--);
  

val GEO027_3 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equidistant(X,Y,Y,X)) /\
   (!X Y Z V V2 W. equidistant(X,Y,Z,V) /\ equidistant(X,Y,V2,W) ==> equidistant(Z,V,V2,W)) /\
   (!Z X Y. equidistant(X,Y,Z,Z) ==> equal(X,Y)) /\
   (!X Y W V. between(X,Y,extension(X,Y,W,V))) /\
   (!X Y W V. equidistant(Y,extension(X,Y,W,V),W,V)) /\
   (!X1 Y1 X Y Z V Z1 V1. equidistant(X,Y,X1,Y1) /\ equidistant(Y,Z,Y1,Z1) /\ equidistant(X,V,X1,V1) /\ equidistant(Y,V,Y1,V1) /\ between(X,Y,Z) /\ between(X1,Y1,Z1) ==> equal(X,Y) \/ equidistant(Z,V,Z1,V1)) /\
   (!X Y. between(X,Y,X) ==> equal(X,Y)) /\
   (!U V W X Y. between(U,V,W) /\ between(Y,X,W) ==> between(V,inner_pasch(U,V,W,X,Y),Y)) /\
   (!V W X Y U. between(U,V,W) /\ between(Y,X,W) ==> between(X,inner_pasch(U,V,W,X,Y),U)) /\
   (~between(lower_dimension_point_1,lower_dimension_point_2,lower_dimension_point_3)) /\
   (~between(lower_dimension_point_2,lower_dimension_point_3,lower_dimension_point_1)) /\
   (~between(lower_dimension_point_3,lower_dimension_point_1,lower_dimension_point_2)) /\
   (!Z X Y W V. equidistant(X,W,X,V) /\ equidistant(Y,W,Y,V) /\ equidistant(Z,W,Z,V) ==> between(X,Y,Z) \/ between(Y,Z,X) \/ between(Z,X,Y) \/ equal(W,V)) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(U,V,euclid1(U,V,W,X,Y))) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(U,X,euclid2(U,V,W,X,Y))) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(euclid1(U,V,W,X,Y),Y,euclid2(U,V,W,X,Y))) /\
   (!U V V1 W X X1. equidistant(U,V,U,V1) /\ equidistant(U,X,U,X1) /\ between(U,V,X) /\ between(V,W,X) ==> between(V1,continuous(U,V,V1,W,X,X1),X1)) /\
   (!U V V1 W X X1. equidistant(U,V,U,V1) /\ equidistant(U,X,U,X1) /\ between(U,V,X) /\ between(V,W,X) ==> equidistant(U,W,U,continuous(U,V,V1,W,X,X1))) /\
   (!X Y W Z. equal(X,Y) /\ between(X,W,Z) ==> between(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ between(W,X,Z) ==> between(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ between(W,Z,X) ==> between(W,Z,Y)) /\
   (!X Y V W Z. equal(X,Y) /\ equidistant(X,V,W,Z) ==> equidistant(Y,V,W,Z)) /\
   (!X V Y W Z. equal(X,Y) /\ equidistant(V,X,W,Z) ==> equidistant(V,Y,W,Z)) /\
   (!X V W Y Z. equal(X,Y) /\ equidistant(V,W,X,Z) ==> equidistant(V,W,Y,Z)) /\
   (!X V W Z Y. equal(X,Y) /\ equidistant(V,W,Z,X) ==> equidistant(V,W,Z,Y)) /\
   (!X Y V1 V2 V3 V4. equal(X,Y) ==> equal(inner_pasch(X,V1,V2,V3,V4),inner_pasch(Y,V1,V2,V3,V4))) /\
   (!X V1 Y V2 V3 V4. equal(X,Y) ==> equal(inner_pasch(V1,X,V2,V3,V4),inner_pasch(V1,Y,V2,V3,V4))) /\
   (!X V1 V2 Y V3 V4. equal(X,Y) ==> equal(inner_pasch(V1,V2,X,V3,V4),inner_pasch(V1,V2,Y,V3,V4))) /\
   (!X V1 V2 V3 Y V4. equal(X,Y) ==> equal(inner_pasch(V1,V2,V3,X,V4),inner_pasch(V1,V2,V3,Y,V4))) /\
   (!X V1 V2 V3 V4 Y. equal(X,Y) ==> equal(inner_pasch(V1,V2,V3,V4,X),inner_pasch(V1,V2,V3,V4,Y))) /\
   (!A B C D E F'. equal(A,B) ==> equal(euclid1(A,C,D,E,F'),euclid1(B,C,D,E,F'))) /\
   (!G I' H J K' L. equal(G,H) ==> equal(euclid1(I',G,J,K',L),euclid1(I',H,J,K',L))) /\
   (!M O P N Q R. equal(M,N) ==> equal(euclid1(O,P,M,Q,R),euclid1(O,P,N,Q,R))) /\
   (!S' U V W T' X. equal(S',T') ==> equal(euclid1(U,V,W,S',X),euclid1(U,V,W,T',X))) /\
   (!Y A1 B1 C1 D1 Z. equal(Y,Z) ==> equal(euclid1(A1,B1,C1,D1,Y),euclid1(A1,B1,C1,D1,Z))) /\
   (!E1 F1 G1 H1 I1 J1. equal(E1,F1) ==> equal(euclid2(E1,G1,H1,I1,J1),euclid2(F1,G1,H1,I1,J1))) /\
   (!K1 M1 L1 N1 O1 P1. equal(K1,L1) ==> equal(euclid2(M1,K1,N1,O1,P1),euclid2(M1,L1,N1,O1,P1))) /\
   (!Q1 S1 T1 R1 U1 V1. equal(Q1,R1) ==> equal(euclid2(S1,T1,Q1,U1,V1),euclid2(S1,T1,R1,U1,V1))) /\
   (!W1 Y1 Z1 A2 X1 B2. equal(W1,X1) ==> equal(euclid2(Y1,Z1,A2,W1,B2),euclid2(Y1,Z1,A2,X1,B2))) /\
   (!C2 E2 F2 G2 H2 D2. equal(C2,D2) ==> equal(euclid2(E2,F2,G2,H2,C2),euclid2(E2,F2,G2,H2,D2))) /\
   (!X Y V1 V2 V3. equal(X,Y) ==> equal(extension(X,V1,V2,V3),extension(Y,V1,V2,V3))) /\
   (!X V1 Y V2 V3. equal(X,Y) ==> equal(extension(V1,X,V2,V3),extension(V1,Y,V2,V3))) /\
   (!X V1 V2 Y V3. equal(X,Y) ==> equal(extension(V1,V2,X,V3),extension(V1,V2,Y,V3))) /\
   (!X V1 V2 V3 Y. equal(X,Y) ==> equal(extension(V1,V2,V3,X),extension(V1,V2,V3,Y))) /\
   (!X Y V1 V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(X,V1,V2,V3,V4,V5),continuous(Y,V1,V2,V3,V4,V5))) /\
   (!X V1 Y V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,X,V2,V3,V4,V5),continuous(V1,Y,V2,V3,V4,V5))) /\
   (!X V1 V2 Y V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,X,V3,V4,V5),continuous(V1,V2,Y,V3,V4,V5))) /\
   (!X V1 V2 V3 Y V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,X,V4,V5),continuous(V1,V2,V3,Y,V4,V5))) /\
   (!X V1 V2 V3 V4 Y V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,X,V5),continuous(V1,V2,V3,V4,Y,V5))) /\
   (!X V1 V2 V3 V4 V5 Y. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,V5,X),continuous(V1,V2,V3,V4,V5,Y))) /\
   (!U V. equal(reflection(U,V),extension(U,V,U,V))) /\
   (!X Y Z. equal(X,Y) ==> equal(reflection(X,Z),reflection(Y,Z))) /\
   (!A1 C1 B1. equal(A1,B1) ==> equal(reflection(C1,A1),reflection(C1,B1))) /\
   (!U V. equidistant(U,V,U,V)) /\
   (!W X U V. equidistant(U,V,W,X) ==> equidistant(W,X,U,V)) /\
   (!V U W X. equidistant(U,V,W,X) ==> equidistant(V,U,W,X)) /\
   (!U V X W. equidistant(U,V,W,X) ==> equidistant(U,V,X,W)) /\
   (!V U X W. equidistant(U,V,W,X) ==> equidistant(V,U,X,W)) /\
   (!W X V U. equidistant(U,V,W,X) ==> equidistant(W,X,V,U)) /\
   (!X W U V. equidistant(U,V,W,X) ==> equidistant(X,W,U,V)) /\
   (!X W V U. equidistant(U,V,W,X) ==> equidistant(X,W,V,U)) /\
   (!W X U V Y Z. equidistant(U,V,W,X) /\ equidistant(W,X,Y,Z) ==> equidistant(U,V,Y,Z)) /\
   (!U V W. equal(V,extension(U,V,W,W))) /\
   (!W X U V Y. equal(Y,extension(U,V,W,X)) ==> between(U,V,Y)) /\
   (!U V. between(U,V,reflection(U,V))) /\
   (!U V. equidistant(V,reflection(U,V),U,V)) /\
   (!U V. equal(U,V) ==> equal(V,reflection(U,V))) /\
   (!U. equal(U,reflection(U,U))) /\
   (!U V. equal(V,reflection(U,V)) ==> equal(U,V)) /\
   (!U V. equidistant(U,U,V,V)) /\
   (!V V1 U W U1 W1. equidistant(U,V,U1,V1) /\ equidistant(V,W,V1,W1) /\ between(U,V,W) /\ between(U1,V1,W1) ==> equidistant(U,W,U1,W1)) /\
   (!U V W X. between(U,V,W) /\ between(U,V,X) /\ equidistant(V,W,V,X) ==> equal(U,V) \/ equal(W,X)) /\
   (between(u,v,w)) /\
   (~equal(u,v)) /\
   (~equal(w,extension(u,v,v,w))) ==> F`--);
  

val GEO058_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equidistant(X,Y,Y,X)) /\
   (!X Y Z V V2 W. equidistant(X,Y,Z,V) /\ equidistant(X,Y,V2,W) ==> equidistant(Z,V,V2,W)) /\
   (!Z X Y. equidistant(X,Y,Z,Z) ==> equal(X,Y)) /\
   (!X Y W V. between(X,Y,extension(X,Y,W,V))) /\
   (!X Y W V. equidistant(Y,extension(X,Y,W,V),W,V)) /\
   (!X1 Y1 X Y Z V Z1 V1. equidistant(X,Y,X1,Y1) /\ equidistant(Y,Z,Y1,Z1) /\ equidistant(X,V,X1,V1) /\ equidistant(Y,V,Y1,V1) /\ between(X,Y,Z) /\ between(X1,Y1,Z1) ==> equal(X,Y) \/ equidistant(Z,V,Z1,V1)) /\
   (!X Y. between(X,Y,X) ==> equal(X,Y)) /\
   (!U V W X Y. between(U,V,W) /\ between(Y,X,W) ==> between(V,inner_pasch(U,V,W,X,Y),Y)) /\
   (!V W X Y U. between(U,V,W) /\ between(Y,X,W) ==> between(X,inner_pasch(U,V,W,X,Y),U)) /\
   (~between(lower_dimension_point_1,lower_dimension_point_2,lower_dimension_point_3)) /\
   (~between(lower_dimension_point_2,lower_dimension_point_3,lower_dimension_point_1)) /\
   (~between(lower_dimension_point_3,lower_dimension_point_1,lower_dimension_point_2)) /\
   (!Z X Y W V. equidistant(X,W,X,V) /\ equidistant(Y,W,Y,V) /\ equidistant(Z,W,Z,V) ==> between(X,Y,Z) \/ between(Y,Z,X) \/ between(Z,X,Y) \/ equal(W,V)) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(U,V,euclid1(U,V,W,X,Y))) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(U,X,euclid2(U,V,W,X,Y))) /\
   (!U V W X Y. between(U,W,Y) /\ between(V,W,X) ==> equal(U,W) \/ between(euclid1(U,V,W,X,Y),Y,euclid2(U,V,W,X,Y))) /\
   (!U V V1 W X X1. equidistant(U,V,U,V1) /\ equidistant(U,X,U,X1) /\ between(U,V,X) /\ between(V,W,X) ==> between(V1,continuous(U,V,V1,W,X,X1),X1)) /\
   (!U V V1 W X X1. equidistant(U,V,U,V1) /\ equidistant(U,X,U,X1) /\ between(U,V,X) /\ between(V,W,X) ==> equidistant(U,W,U,continuous(U,V,V1,W,X,X1))) /\
   (!X Y W Z. equal(X,Y) /\ between(X,W,Z) ==> between(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ between(W,X,Z) ==> between(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ between(W,Z,X) ==> between(W,Z,Y)) /\
   (!X Y V W Z. equal(X,Y) /\ equidistant(X,V,W,Z) ==> equidistant(Y,V,W,Z)) /\
   (!X V Y W Z. equal(X,Y) /\ equidistant(V,X,W,Z) ==> equidistant(V,Y,W,Z)) /\
   (!X V W Y Z. equal(X,Y) /\ equidistant(V,W,X,Z) ==> equidistant(V,W,Y,Z)) /\
   (!X V W Z Y. equal(X,Y) /\ equidistant(V,W,Z,X) ==> equidistant(V,W,Z,Y)) /\
   (!X Y V1 V2 V3 V4. equal(X,Y) ==> equal(inner_pasch(X,V1,V2,V3,V4),inner_pasch(Y,V1,V2,V3,V4))) /\
   (!X V1 Y V2 V3 V4. equal(X,Y) ==> equal(inner_pasch(V1,X,V2,V3,V4),inner_pasch(V1,Y,V2,V3,V4))) /\
   (!X V1 V2 Y V3 V4. equal(X,Y) ==> equal(inner_pasch(V1,V2,X,V3,V4),inner_pasch(V1,V2,Y,V3,V4))) /\
   (!X V1 V2 V3 Y V4. equal(X,Y) ==> equal(inner_pasch(V1,V2,V3,X,V4),inner_pasch(V1,V2,V3,Y,V4))) /\
   (!X V1 V2 V3 V4 Y. equal(X,Y) ==> equal(inner_pasch(V1,V2,V3,V4,X),inner_pasch(V1,V2,V3,V4,Y))) /\
   (!A B C D E F'. equal(A,B) ==> equal(euclid1(A,C,D,E,F'),euclid1(B,C,D,E,F'))) /\
   (!G I' H J K' L. equal(G,H) ==> equal(euclid1(I',G,J,K',L),euclid1(I',H,J,K',L))) /\
   (!M O P N Q R. equal(M,N) ==> equal(euclid1(O,P,M,Q,R),euclid1(O,P,N,Q,R))) /\
   (!S' U V W T' X. equal(S',T') ==> equal(euclid1(U,V,W,S',X),euclid1(U,V,W,T',X))) /\
   (!Y A1 B1 C1 D1 Z. equal(Y,Z) ==> equal(euclid1(A1,B1,C1,D1,Y),euclid1(A1,B1,C1,D1,Z))) /\
   (!E1 F1 G1 H1 I1 J1. equal(E1,F1) ==> equal(euclid2(E1,G1,H1,I1,J1),euclid2(F1,G1,H1,I1,J1))) /\
   (!K1 M1 L1 N1 O1 P1. equal(K1,L1) ==> equal(euclid2(M1,K1,N1,O1,P1),euclid2(M1,L1,N1,O1,P1))) /\
   (!Q1 S1 T1 R1 U1 V1. equal(Q1,R1) ==> equal(euclid2(S1,T1,Q1,U1,V1),euclid2(S1,T1,R1,U1,V1))) /\
   (!W1 Y1 Z1 A2 X1 B2. equal(W1,X1) ==> equal(euclid2(Y1,Z1,A2,W1,B2),euclid2(Y1,Z1,A2,X1,B2))) /\
   (!C2 E2 F2 G2 H2 D2. equal(C2,D2) ==> equal(euclid2(E2,F2,G2,H2,C2),euclid2(E2,F2,G2,H2,D2))) /\
   (!X Y V1 V2 V3. equal(X,Y) ==> equal(extension(X,V1,V2,V3),extension(Y,V1,V2,V3))) /\
   (!X V1 Y V2 V3. equal(X,Y) ==> equal(extension(V1,X,V2,V3),extension(V1,Y,V2,V3))) /\
   (!X V1 V2 Y V3. equal(X,Y) ==> equal(extension(V1,V2,X,V3),extension(V1,V2,Y,V3))) /\
   (!X V1 V2 V3 Y. equal(X,Y) ==> equal(extension(V1,V2,V3,X),extension(V1,V2,V3,Y))) /\
   (!X Y V1 V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(X,V1,V2,V3,V4,V5),continuous(Y,V1,V2,V3,V4,V5))) /\
   (!X V1 Y V2 V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,X,V2,V3,V4,V5),continuous(V1,Y,V2,V3,V4,V5))) /\
   (!X V1 V2 Y V3 V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,X,V3,V4,V5),continuous(V1,V2,Y,V3,V4,V5))) /\
   (!X V1 V2 V3 Y V4 V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,X,V4,V5),continuous(V1,V2,V3,Y,V4,V5))) /\
   (!X V1 V2 V3 V4 Y V5. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,X,V5),continuous(V1,V2,V3,V4,Y,V5))) /\
   (!X V1 V2 V3 V4 V5 Y. equal(X,Y) ==> equal(continuous(V1,V2,V3,V4,V5,X),continuous(V1,V2,V3,V4,V5,Y))) /\
   (!U V. equal(reflection(U,V),extension(U,V,U,V))) /\
   (!X Y Z. equal(X,Y) ==> equal(reflection(X,Z),reflection(Y,Z))) /\
   (!A1 C1 B1. equal(A1,B1) ==> equal(reflection(C1,A1),reflection(C1,B1))) /\
   (equal(v,reflection(u,v))) /\
   (~equal(u,v)) ==> F`--);
  

val GEO079_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!U V W X Y Z. right_angle(U,V,W) /\ right_angle(X,Y,Z) ==> eq(U,V,W,X,Y,Z)) /\
   (!U V W X Y Z. congruent(U,V,W,X,Y,Z) ==> eq(U,V,W,X,Y,Z)) /\
   (!V W U X. trapezoid(U,V,W,X) ==> parallel(V,W,U,X)) /\
   (!U V X Y. parallel(U,V,X,Y) ==> eq(X,V,U,V,X,Y)) /\
   (trapezoid(a,b,c,d)) /\
   (~eq(a,c,b,c,a,d)) ==> F`;
  

val GRP001_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. product(identity,X,X)) /\
   (!X. product(X,identity,X)) /\
   (!X. product(inverse(X),X,identity)) /\
   (!X. product(X,inverse(X),identity)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!X Y. equal(X,Y) ==> equal(inverse(X),inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!X. product(X,X,identity)) /\
   (product(a,b,c)) /\
   (~product(b,a,c)) ==> F`--);
  

val GRP008_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. product(identity,X,X)) /\
   (!X. product(X,identity,X)) /\
   (!X. product(inverse(X),X,identity)) /\
   (!X. product(X,inverse(X),identity)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!X Y. equal(X,Y) ==> equal(inverse(X),inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!A B. equal(A,B) ==> equal(h(A),h(B))) /\
   (!C D. equal(C,D) ==> equal(j(C),j(D))) /\
   (!A B. equal(A,B) /\ q(A) ==> q(B)) /\
   (!B A C. q(A) /\ product(A,B,C) ==> product(B,A,C)) /\
   (!A. product(j(A),A,h(A)) \/ product(A,j(A),h(A)) \/ q(A)) /\
   (!A. product(j(A),A,h(A)) /\ product(A,j(A),h(A)) ==> q(A)) /\
   (~q(identity)) ==> F`--);
  

val GRP013_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. product(identity,X,X)) /\
   (!X. product(X,identity,X)) /\
   (!X. product(inverse(X),X,identity)) /\
   (!X. product(X,inverse(X),identity)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!X Y. equal(X,Y) ==> equal(inverse(X),inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!A. product(A,A,identity)) /\
   (product(a,b,c)) /\
   (product(inverse(a),inverse(b),d)) /\
   (!A C B. product(inverse(A),inverse(B),C) ==> product(A,C,B)) /\
   (~product(c,d,identity)) ==> F`--);
  

val GRP037_3 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. product(identity,X,X)) /\
   (!X. product(X,identity,X)) /\
   (!X. product(inverse(X),X,identity)) /\
   (!X. product(X,inverse(X),identity)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!X Y. equal(X,Y) ==> equal(inverse(X),inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!A B C. subgroup_member(A) /\ subgroup_member(B) /\ product(A,inverse(B),C) ==> subgroup_member(C)) /\
   (!A B. equal(A,B) /\ subgroup_member(A) ==> subgroup_member(B)) /\
   (!A. subgroup_member(A) ==> product(another_identity,A,A)) /\
   (!A. subgroup_member(A) ==> product(A,another_identity,A)) /\
   (!A. subgroup_member(A) ==> product(A,another_inverse(A),another_identity)) /\
   (!A. subgroup_member(A) ==> product(another_inverse(A),A,another_identity)) /\
   (!A. subgroup_member(A) ==> subgroup_member(another_inverse(A))) /\
   (!A B. equal(A,B) ==> equal(another_inverse(A),another_inverse(B))) /\
   (!A C D B. product(A,B,C) /\ product(A,D,C) ==> equal(D,B)) /\
   (!B C D A. product(A,B,C) /\ product(D,B,C) ==> equal(D,A)) /\
   (subgroup_member(a)) /\
   (subgroup_member(another_identity)) /\
   (~equal(inverse(a),another_inverse(a))) ==> F`--);
  

val GRP031_2 = 
 (--`(!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!A. product(A,inverse(A),identity)) /\
   (!A:'a. product(A,identity,A)) /\
   (!A. ~product(A,a,identity)) ==> F`--);
  

val GRP034_4 = 
 (--`(!X Y:'a. product(X,Y,multiply(X,Y))) /\
   (!X. product(identity,X,X)) /\
   (!X. product(X,identity,X)) /\
   (!X. product(X,inverse(X),identity)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!B A C. subgroup_member(A) /\ subgroup_member(B) /\ product(B,inverse(A),C) ==> subgroup_member(C)) /\
   (subgroup_member(a)) /\
   (~subgroup_member(inverse(a))) ==> F`--);
  

val GRP047_2 = 
 (--`(!X:'a. product(identity,X,X)) /\
   (!X. product(inverse(X),X,identity)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y Z W. product(X,Y,Z) /\ product(X,Y,W) ==> equal(Z,W)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (equal(a,b)) /\
   (~equal(multiply(c,a),multiply(c,b))) ==> F`--);
  

val GRP130_1_002 = 
 (--`(group_element(e_1:'a)) /\
   (group_element(e_2)) /\
   (~equal(e_1,e_2)) /\
   (~equal(e_2,e_1)) /\
   (!X Y. group_element(X) /\ group_element(Y) ==> product(X,Y,e_1) \/ product(X,Y,e_2)) /\
   (!X Y W Z. product(X,Y,W) /\ product(X,Y,Z) ==> equal(W,Z)) /\
   (!X Y W Z. product(X,W,Y) /\ product(X,Z,Y) ==> equal(W,Z)) /\
   (!Y X W Z. product(W,Y,X) /\ product(Z,Y,X) ==> equal(W,Z)) /\
   (!Z1 Z2 Y X. product(X,Y,Z1) /\ product(X,Z1,Z2) ==> product(Z2,Y,X)) ==> F`--);
  

val GRP156_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(multiply(identity,X),X)) /\
   (!X. equal(multiply(inverse(X),X),identity)) /\
   (!X Y Z. equal(multiply(multiply(X,Y),Z),multiply(X,multiply(Y,Z)))) /\
   (!A B. equal(A,B) ==> equal(inverse(A),inverse(B))) /\
   (!C D E. equal(C,D) ==> equal(multiply(C,E),multiply(D,E))) /\
   (!F' H G. equal(F',G) ==> equal(multiply(H,F'),multiply(H,G))) /\
   (!Y X. equal(greatest_lower_bound(X,Y),greatest_lower_bound(Y,X))) /\
   (!Y X. equal(least_upper_bound(X,Y),least_upper_bound(Y,X))) /\
   (!X Y Z. equal(greatest_lower_bound(X,greatest_lower_bound(Y,Z)),greatest_lower_bound(greatest_lower_bound(X,Y),Z))) /\
   (!X Y Z. equal(least_upper_bound(X,least_upper_bound(Y,Z)),least_upper_bound(least_upper_bound(X,Y),Z))) /\
   (!X. equal(least_upper_bound(X,X),X)) /\
   (!X. equal(greatest_lower_bound(X,X),X)) /\
   (!Y X. equal(least_upper_bound(X,greatest_lower_bound(X,Y)),X)) /\
   (!Y X. equal(greatest_lower_bound(X,least_upper_bound(X,Y)),X)) /\
   (!Y X Z. equal(multiply(X,least_upper_bound(Y,Z)),least_upper_bound(multiply(X,Y),multiply(X,Z)))) /\
   (!Y X Z. equal(multiply(X,greatest_lower_bound(Y,Z)),greatest_lower_bound(multiply(X,Y),multiply(X,Z)))) /\
   (!Y Z X. equal(multiply(least_upper_bound(Y,Z),X),least_upper_bound(multiply(Y,X),multiply(Z,X)))) /\
   (!Y Z X. equal(multiply(greatest_lower_bound(Y,Z),X),greatest_lower_bound(multiply(Y,X),multiply(Z,X)))) /\
   (!A B C. equal(A,B) ==> equal(greatest_lower_bound(A,C),greatest_lower_bound(B,C))) /\
   (!A C B. equal(A,B) ==> equal(greatest_lower_bound(C,A),greatest_lower_bound(C,B))) /\
   (!A B C. equal(A,B) ==> equal(least_upper_bound(A,C),least_upper_bound(B,C))) /\
   (!A C B. equal(A,B) ==> equal(least_upper_bound(C,A),least_upper_bound(C,B))) /\
   (!A B C. equal(A,B) ==> equal(multiply(A,C),multiply(B,C))) /\
   (!A C B. equal(A,B) ==> equal(multiply(C,A),multiply(C,B))) /\
   (equal(least_upper_bound(a,b),b)) /\
   (~equal(greatest_lower_bound(multiply(a,c),multiply(b,c)),multiply(a,c))) ==> F`--);
  

val GRP168_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(multiply(identity,X),X)) /\
   (!X. equal(multiply(inverse(X),X),identity)) /\
   (!X Y Z. equal(multiply(multiply(X,Y),Z),multiply(X,multiply(Y,Z)))) /\
   (!A B. equal(A,B) ==> equal(inverse(A),inverse(B))) /\
   (!C D E. equal(C,D) ==> equal(multiply(C,E),multiply(D,E))) /\
   (!F' H G. equal(F',G) ==> equal(multiply(H,F'),multiply(H,G))) /\
   (!Y X. equal(greatest_lower_bound(X,Y),greatest_lower_bound(Y,X))) /\
   (!Y X. equal(least_upper_bound(X,Y),least_upper_bound(Y,X))) /\
   (!X Y Z. equal(greatest_lower_bound(X,greatest_lower_bound(Y,Z)),greatest_lower_bound(greatest_lower_bound(X,Y),Z))) /\
   (!X Y Z. equal(least_upper_bound(X,least_upper_bound(Y,Z)),least_upper_bound(least_upper_bound(X,Y),Z))) /\
   (!X. equal(least_upper_bound(X,X),X)) /\
   (!X. equal(greatest_lower_bound(X,X),X)) /\
   (!Y X. equal(least_upper_bound(X,greatest_lower_bound(X,Y)),X)) /\
   (!Y X. equal(greatest_lower_bound(X,least_upper_bound(X,Y)),X)) /\
   (!Y X Z. equal(multiply(X,least_upper_bound(Y,Z)),least_upper_bound(multiply(X,Y),multiply(X,Z)))) /\
   (!Y X Z. equal(multiply(X,greatest_lower_bound(Y,Z)),greatest_lower_bound(multiply(X,Y),multiply(X,Z)))) /\
   (!Y Z X. equal(multiply(least_upper_bound(Y,Z),X),least_upper_bound(multiply(Y,X),multiply(Z,X)))) /\
   (!Y Z X. equal(multiply(greatest_lower_bound(Y,Z),X),greatest_lower_bound(multiply(Y,X),multiply(Z,X)))) /\
   (!A B C. equal(A,B) ==> equal(greatest_lower_bound(A,C),greatest_lower_bound(B,C))) /\
   (!A C B. equal(A,B) ==> equal(greatest_lower_bound(C,A),greatest_lower_bound(C,B))) /\
   (!A B C. equal(A,B) ==> equal(least_upper_bound(A,C),least_upper_bound(B,C))) /\
   (!A C B. equal(A,B) ==> equal(least_upper_bound(C,A),least_upper_bound(C,B))) /\
   (!A B C. equal(A,B) ==> equal(multiply(A,C),multiply(B,C))) /\
   (!A C B. equal(A,B) ==> equal(multiply(C,A),multiply(C,B))) /\
   (equal(least_upper_bound(a,b),b)) /\
   (~equal(least_upper_bound(multiply(inverse(c),multiply(a,c)),multiply(inverse(c),multiply(b,c))),multiply(inverse(c),multiply(b,c)))) ==> F`--);
  

val HEN003_3 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. less_equal(X,Y) ==> equal(divide(X,Y),zero)) /\
   (!X Y. equal(divide(X,Y),zero) ==> less_equal(X,Y)) /\
   (!Y X. less_equal(divide(X,Y),X)) /\
   (!X Y Z. less_equal(divide(divide(X,Z),divide(Y,Z)),divide(divide(X,Y),Z))) /\
   (!X. less_equal(zero,X)) /\
   (!X Y. less_equal(X,Y) /\ less_equal(Y,X) ==> equal(X,Y)) /\
   (!X. less_equal(X,identity)) /\
   (!A B C. equal(A,B) ==> equal(divide(A,C),divide(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(divide(F',D),divide(F',E))) /\
   (!G H I'. equal(G,H) /\ less_equal(G,I') ==> less_equal(H,I')) /\
   (!J L K'. equal(J,K') /\ less_equal(L,J) ==> less_equal(L,K')) /\
   (~equal(divide(a,a),zero)) ==> F`--);
  

val HEN007_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. less_equal(X,Y) ==> quotient(X,Y,zero)) /\
   (!X Y. quotient(X,Y,zero) ==> less_equal(X,Y)) /\
   (!Y Z X. quotient(X,Y,Z) ==> less_equal(Z,X)) /\
   (!Y X V3 V2 V1 Z V4 V5. quotient(X,Y,V1) /\ quotient(Y,Z,V2) /\ quotient(X,Z,V3) /\ quotient(V3,V2,V4) /\ quotient(V1,Z,V5) ==> less_equal(V4,V5)) /\
   (!X. less_equal(zero,X)) /\
   (!X Y. less_equal(X,Y) /\ less_equal(Y,X) ==> equal(X,Y)) /\
   (!X. less_equal(X,identity)) /\
   (!X Y. quotient(X,Y,divide(X,Y))) /\
   (!X Y Z W. quotient(X,Y,Z) /\ quotient(X,Y,W) ==> equal(Z,W)) /\
   (!X Y W Z. equal(X,Y) /\ quotient(X,W,Z) ==> quotient(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ quotient(W,X,Z) ==> quotient(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ quotient(W,Z,X) ==> quotient(W,Z,Y)) /\
   (!X Z Y. equal(X,Y) /\ less_equal(Z,X) ==> less_equal(Z,Y)) /\
   (!X Y Z. equal(X,Y) /\ less_equal(X,Z) ==> less_equal(Y,Z)) /\
   (!X Y W. equal(X,Y) ==> equal(divide(X,W),divide(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(divide(W,X),divide(W,Y))) /\
   (!X. quotient(X,identity,zero)) /\
   (!X. quotient(zero,X,zero)) /\
   (!X. quotient(X,X,zero)) /\
   (!X. quotient(X,zero,X)) /\
   (!Y X Z. less_equal(X,Y) /\ less_equal(Y,Z) ==> less_equal(X,Z)) /\
   (!W1 X Z W2 Y. quotient(X,Y,W1) /\ less_equal(W1,Z) /\ quotient(X,Z,W2) ==> less_equal(W2,Y)) /\
   (less_equal(x,y)) /\
   (quotient(z,y,zQy)) /\
   (quotient(z,x,zQx)) /\
   (~less_equal(zQy,zQx)) ==> F`--);
  

val HEN008_4 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. less_equal(X,Y) ==> equal(divide(X,Y),zero)) /\
   (!X Y. equal(divide(X,Y),zero) ==> less_equal(X,Y)) /\
   (!Y X. less_equal(divide(X,Y),X)) /\
   (!X Y Z. less_equal(divide(divide(X,Z),divide(Y,Z)),divide(divide(X,Y),Z))) /\
   (!X. less_equal(zero,X)) /\
   (!X Y. less_equal(X,Y) /\ less_equal(Y,X) ==> equal(X,Y)) /\
   (!X. less_equal(X,identity)) /\
   (!A B C. equal(A,B) ==> equal(divide(A,C),divide(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(divide(F',D),divide(F',E))) /\
   (!G H I'. equal(G,H) /\ less_equal(G,I') ==> less_equal(H,I')) /\
   (!J L K'. equal(J,K') /\ less_equal(L,J) ==> less_equal(L,K')) /\
   (!X. equal(divide(X,identity),zero)) /\
   (!X. equal(divide(zero,X),zero)) /\
   (!X. equal(divide(X,X),zero)) /\
   (equal(divide(a,zero),a)) /\
   (!Y X Z. less_equal(X,Y) /\ less_equal(Y,Z) ==> less_equal(X,Z)) /\
   (!X Z Y. less_equal(divide(X,Y),Z) ==> less_equal(divide(X,Z),Y)) /\
   (!Y Z X. less_equal(X,Y) ==> less_equal(divide(Z,Y),divide(Z,X))) /\
   (less_equal(a,b)) /\
   (~less_equal(divide(a,c),divide(b,c))) ==> F`--);
  

val HEN009_5 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(divide(divide(X,Y),X),zero)) /\
   (!X Y Z. equal(divide(divide(divide(X,Z),divide(Y,Z)),divide(divide(X,Y),Z)),zero)) /\
   (!X. equal(divide(zero,X),zero)) /\
   (!X Y. equal(divide(X,Y),zero) /\ equal(divide(Y,X),zero) ==> equal(X,Y)) /\
   (!X. equal(divide(X,identity),zero)) /\
   (!A B C. equal(A,B) ==> equal(divide(A,C),divide(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(divide(F',D),divide(F',E))) /\
   (!Y X Z. equal(divide(X,Y),zero) /\ equal(divide(Y,Z),zero) ==> equal(divide(X,Z),zero)) /\
   (!X Z Y. equal(divide(divide(X,Y),Z),zero) ==> equal(divide(divide(X,Z),Y),zero)) /\
   (!Y Z X. equal(divide(X,Y),zero) ==> equal(divide(divide(Z,Y),divide(Z,X)),zero)) /\
   (~equal(divide(identity,a),divide(identity,divide(identity,divide(identity,a))))) /\
   (equal(divide(identity,a),b)) /\
   (equal(divide(identity,b),c)) /\
   (equal(divide(identity,c),d)) /\
   (~equal(b,d)) ==> F`--);
  

val HEN012_3 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. less_equal(X,Y) ==> equal(divide(X,Y),zero)) /\
   (!X Y. equal(divide(X,Y),zero) ==> less_equal(X,Y)) /\
   (!Y X. less_equal(divide(X,Y),X)) /\
   (!X Y Z. less_equal(divide(divide(X,Z),divide(Y,Z)),divide(divide(X,Y),Z))) /\
   (!X. less_equal(zero,X)) /\
   (!X Y. less_equal(X,Y) /\ less_equal(Y,X) ==> equal(X,Y)) /\
   (!X. less_equal(X,identity)) /\
   (!A B C. equal(A,B) ==> equal(divide(A,C),divide(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(divide(F',D),divide(F',E))) /\
   (!G H I'. equal(G,H) /\ less_equal(G,I') ==> less_equal(H,I')) /\
   (!J L K'. equal(J,K') /\ less_equal(L,J) ==> less_equal(L,K')) /\
   (~less_equal(a,a)) ==> F`--);
  

val LCL010_1 = 
 (--`(!X Y:'a. is_a_theorem(equivalent(X,Y)) /\ is_a_theorem(X) ==> is_a_theorem(Y)) /\
   (!X Z Y. is_a_theorem(equivalent(equivalent(X,Y),equivalent(equivalent(X,Z),equivalent(Z,Y))))) /\
   (~is_a_theorem(equivalent(equivalent(a,b),equivalent(equivalent(c,b),equivalent(a,c))))) ==> F`--);
  

val LCL077_2 = 
 (--`(!X Y:'a. is_a_theorem(implies(X,Y)) /\ is_a_theorem(X) ==> is_a_theorem(Y)) /\
   (!Y X. is_a_theorem(implies(X,implies(Y,X)))) /\
   (!Y X Z. is_a_theorem(implies(implies(X,implies(Y,Z)),implies(implies(X,Y),implies(X,Z))))) /\
   (!Y X. is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X)))) /\
   (!X2 X1 X3. is_a_theorem(implies(X1,X2)) /\ is_a_theorem(implies(X2,X3)) ==> is_a_theorem(implies(X1,X3))) /\
   (~is_a_theorem(implies(not(not(a)),a))) ==> F`--);
  

val LCL082_1 = 
 (--`(!X Y:'a. is_a_theorem(implies(X,Y)) /\ is_a_theorem(X) ==> is_a_theorem(Y)) /\
   (!Y Z U X. is_a_theorem(implies(implies(implies(X,Y),Z),implies(implies(Z,X),implies(U,X))))) /\
   (~is_a_theorem(implies(a,implies(b,a)))) ==> F`--);
  

val LCL111_1 = 
 (--`(!X Y:'a. is_a_theorem(implies(X,Y)) /\ is_a_theorem(X) ==> is_a_theorem(Y)) /\
   (!Y X. is_a_theorem(implies(X,implies(Y,X)))) /\
   (!Y X Z. is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))))) /\
   (!Y X. is_a_theorem(implies(implies(implies(X,Y),Y),implies(implies(Y,X),X)))) /\
   (!Y X. is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X)))) /\
   (~is_a_theorem(implies(implies(a,b),implies(implies(c,a),implies(c,b))))) ==> F`--);
  

val LCL143_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(implies(true,X),X)) /\
   (!Y X Z. equal(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z))),true)) /\
   (!Y X. equal(implies(implies(X,Y),Y),implies(implies(Y,X),X))) /\
   (!Y X. equal(implies(implies(not(X),not(Y)),implies(Y,X)),true)) /\
   (!A B C. equal(A,B) ==> equal(implies(A,C),implies(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(implies(F',D),implies(F',E))) /\
   (!G H. equal(G,H) ==> equal(not(G),not(H))) /\
   (!X Y. equal(big_V(X,Y),implies(implies(X,Y),Y))) /\
   (!X Y. equal(big_hat(X,Y),not(big_V(not(X),not(Y))))) /\
   (!X Y. ordered(X,Y) ==> equal(implies(X,Y),true)) /\
   (!X Y. equal(implies(X,Y),true) ==> ordered(X,Y)) /\
   (!A B C. equal(A,B) ==> equal(big_V(A,C),big_V(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(big_V(F',D),big_V(F',E))) /\
   (!G H I'. equal(G,H) ==> equal(big_hat(G,I'),big_hat(H,I'))) /\
   (!J L K'. equal(J,K') ==> equal(big_hat(L,J),big_hat(L,K'))) /\
   (!M N O. equal(M,N) /\ ordered(M,O) ==> ordered(N,O)) /\
   (!P R Q. equal(P,Q) /\ ordered(R,P) ==> ordered(R,Q)) /\
   (ordered(x,y)) /\
   (~ordered(implies(z,x),implies(z,y))) ==> F`--);
  

val LCL182_1 = 
 (--`(!A:'a. axiom(or(not(or(A,A)),A))) /\
   (!B A. axiom(or(not(A),or(B,A)))) /\
   (!B A. axiom(or(not(or(A,B)),or(B,A)))) /\
   (!B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) /\
   (!A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) /\
   (!X. axiom(X) ==> theorem(X)) /\
   (!X Y. axiom(or(not(Y),X)) /\ theorem(Y) ==> theorem(X)) /\
   (!X Y Z. axiom(or(not(X),Y)) /\ theorem(or(not(Y),Z)) ==> theorem(or(not(X),Z))) /\
   (~theorem(or(not(or(not(p),q)),or(not(not(q)),not(p))))) ==> F`--);
  

val LCL200_1 = 
 (--`(!A:'a. axiom(or(not(or(A,A)),A))) /\
   (!B A. axiom(or(not(A),or(B,A)))) /\
   (!B A. axiom(or(not(or(A,B)),or(B,A)))) /\
   (!B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) /\
   (!A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) /\
   (!X. axiom(X) ==> theorem(X)) /\
   (!X Y. axiom(or(not(Y),X)) /\ theorem(Y) ==> theorem(X)) /\
   (!X Y Z. axiom(or(not(X),Y)) /\ theorem(or(not(Y),Z)) ==> theorem(or(not(X),Z))) /\
   (~theorem(or(not(not(or(p,q))),not(q)))) ==> F`--);
  

val LCL215_1 = 
 (--`(!A:'a. axiom(or(not(or(A,A)),A))) /\
   (!B A. axiom(or(not(A),or(B,A)))) /\
   (!B A. axiom(or(not(or(A,B)),or(B,A)))) /\
   (!B A C. axiom(or(not(or(A,or(B,C))),or(B,or(A,C))))) /\
   (!A C B. axiom(or(not(or(not(A),B)),or(not(or(C,A)),or(C,B))))) /\
   (!X. axiom(X) ==> theorem(X)) /\
   (!X Y. axiom(or(not(Y),X)) /\ theorem(Y) ==> theorem(X)) /\
   (!X Y Z. axiom(or(not(X),Y)) /\ theorem(or(not(Y),Z)) ==> theorem(or(not(X),Z))) /\
   (~theorem(or(not(or(not(p),q)),or(not(or(p,q)),q)))) ==> F`--);
  

val LCL230_2 = 
 (--`(q ==> p \/ r) /\
   (~p) /\
   (q) /\
   (~r) ==> F`--);
  

val LDA003_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X Z. equal(f(X,f(Y,Z)),f(f(X,Y),f(X,Z)))) /\
   (!X Y. left(X,f(X,Y))) /\
   (!Y X Z. left(X,Y) /\ left(Y,Z) ==> left(X,Z)) /\
   (equal(2,f(1,1))) /\
   (equal(3,f(2,1))) /\
   (equal(u,f(2,2))) /\
   (!A B C. equal(A,B) ==> equal(f(A,C),f(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(f(F',D),f(F',E))) /\
   (!G H I'. equal(G,H) /\ left(G,I') ==> left(H,I')) /\
   (!J L K'. equal(J,K') /\ left(L,J) ==> left(L,K')) /\
   (~left(3,u)) ==> F`--);
  

val MSC002_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(at(something,here,now)) /\
   (!Place Situation. hand_at(Place,Situation) ==> hand_at(Place,let_go(Situation))) /\
   (!Place Another_place Situation. hand_at(Place,Situation) ==> hand_at(Another_place,go(Another_place,Situation))) /\
   (!Thing Situation. ~held(Thing,let_go(Situation))) /\
   (!Situation Thing. at(Thing,here,Situation) ==> red(Thing)) /\
   (!Thing Place Situation. at(Thing,Place,Situation) ==> at(Thing,Place,let_go(Situation))) /\
   (!Thing Place Situation. at(Thing,Place,Situation) ==> at(Thing,Place,pick_up(Situation))) /\
   (!Thing Place Situation. at(Thing,Place,Situation) ==> grabbed(Thing,pick_up(go(Place,let_go(Situation))))) /\
   (!Thing Situation. red(Thing) /\ put(Thing,there,Situation) ==> answer(Situation)) /\
   (!Place Thing Another_place Situation. at(Thing,Place,Situation) /\ grabbed(Thing,Situation) ==> put(Thing,Another_place,go(Another_place,Situation))) /\
   (!Thing Place Another_place Situation. at(Thing,Place,Situation) ==> held(Thing,Situation) \/ at(Thing,Place,go(Another_place,Situation))) /\
   (!One_place Thing Place Situation. hand_at(One_place,Situation) /\ held(Thing,Situation) ==> at(Thing,Place,go(Place,Situation))) /\
   (!Place Thing Situation. hand_at(Place,Situation) /\ at(Thing,Place,Situation) ==> held(Thing,pick_up(Situation))) /\
   (!Situation. ~answer(Situation)) ==> F`;

val MSC003_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Number_of_small_parts Small_part Big_part Number_of_mid_parts Mid_part. has_parts(Big_part,Number_of_mid_parts,Mid_part) ==> in'(object_in(Big_part,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part) \/ has_parts(Big_part,times(Number_of_mid_parts,Number_of_small_parts),Small_part)) /\
   (!Big_part Mid_part Number_of_mid_parts Number_of_small_parts Small_part. has_parts(Big_part,Number_of_mid_parts,Mid_part) /\ has_parts(object_in(Big_part,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) ==> has_parts(Big_part,times(Number_of_mid_parts,Number_of_small_parts),Small_part)) /\
   (in'(john,boy)) /\
   (!X. in'(X,boy) ==> in'(X,human)) /\
   (!X. in'(X,hand) ==> has_parts(X,5,fingers)) /\
   (!X. in'(X,human) ==> has_parts(X,2,arm)) /\
   (!X. in'(X,arm) ==> has_parts(X,1,hand)) /\
   (~has_parts(john,times(2,1),hand)) ==> F`;
  

val MSC004_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Number_of_small_parts Small_part Big_part Number_of_mid_parts Mid_part. has_parts(Big_part,Number_of_mid_parts,Mid_part) ==> in'(object_in(Big_part,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part) \/ has_parts(Big_part,times(Number_of_mid_parts,Number_of_small_parts),Small_part)) /\
   (!Big_part Mid_part Number_of_mid_parts Number_of_small_parts Small_part. has_parts(Big_part,Number_of_mid_parts,Mid_part) /\ has_parts(object_in(Big_part,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) ==> has_parts(Big_part,times(Number_of_mid_parts,Number_of_small_parts),Small_part)) /\
   (in'(john,boy)) /\
   (!X. in'(X,boy) ==> in'(X,human)) /\
   (!X. in'(X,hand) ==> has_parts(X,5,fingers)) /\
   (!X. in'(X,human) ==> has_parts(X,2,arm)) /\
   (!X. in'(X,arm) ==> has_parts(X,1,hand)) /\
   (~has_parts(john,times(times(2,1),5),fingers)) ==> F`;
  

val MSC005_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(value(truth,truth)) /\
 (value(falsity,falsity)) /\
 (!X Y. value(X,truth) /\ value(Y,truth) ==> value(xor(X,Y),falsity)) /\
 (!X Y. value(X,truth) /\ value(Y,falsity) ==> value(xor(X,Y),truth)) /\
 (!X Y. value(X,falsity) /\ value(Y,truth) ==> value(xor(X,Y),truth)) /\
 (!X Y. value(X,falsity) /\ value(Y,falsity) ==> value(xor(X,Y),falsity)) /\
 (!Value. ~value(xor(xor(xor(xor(truth,falsity),falsity),truth),falsity),Value))
  ==> F`;
  

val MSC006_1 = 
 (--`(!Y X Z:'a. p(X,Y) /\ p(Y,Z) ==> p(X,Z)) /\
   (!Y X Z. q(X,Y) /\ q(Y,Z) ==> q(X,Z)) /\
   (!Y X. q(X,Y) ==> q(Y,X)) /\
   (!X Y. p(X,Y) \/ q(X,Y)) /\
   (~p(a,b)) /\
   (~q(c,d)) ==> F`--);
  

val NUM001_1 = 
 (--`(!A:'a. equal(A,A)) /\
   (!B A C. equal(A,B) /\ equal(B,C) ==> equal(A,C)) /\
   (!B A. equal(add(A,B),add(B,A))) /\
   (!A B C. equal(add(A,add(B,C)),add(add(A,B),C))) /\
   (!B A. equal(subtract(add(A,B),B),A)) /\
   (!A B. equal(A,subtract(add(A,B),B))) /\
   (!A C B. equal(add(subtract(A,B),C),subtract(add(A,C),B))) /\
   (!A C B. equal(subtract(add(A,B),C),add(subtract(A,C),B))) /\
   (!A C B D. equal(A,B) /\ equal(C,add(A,D)) ==> equal(C,add(B,D))) /\
   (!A C D B. equal(A,B) /\ equal(C,add(D,A)) ==> equal(C,add(D,B))) /\
   (!A C B D. equal(A,B) /\ equal(C,subtract(A,D)) ==> equal(C,subtract(B,D))) /\
   (!A C D B. equal(A,B) /\ equal(C,subtract(D,A)) ==> equal(C,subtract(D,B))) /\
   (~equal(add(add(a,b),c),add(a,add(b,c)))) ==> F`--);
  

val NUM021_1 = 
 (--`(!X. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!A. equal(add(A,0),A)) /\
   (!A B. equal(add(A,successor(B)),successor(add(A,B)))) /\
   (!A. equal(multiply(A,0),0)) /\
   (!B A. equal(multiply(A,successor(B)),add(multiply(A,B),A))) /\
   (!A B. equal(successor(A),successor(B)) ==> equal(A,B)) /\
   (!A B. equal(A,B) ==> equal(successor(A),successor(B))) /\
   (!A C B. less(A,B) /\ less(C,A) ==> less(C,B)) /\
   (!A B C. equal(add(successor(A),B),C) ==> less(B,C)) /\
   (!A B. less(A,B) ==> equal(add(successor(predecessor_of_1st_minus_2nd(B,A)),A),B)) /\
   (!A B. divides(A,B) ==> less(A,B) \/ equal(A,B)) /\
   (!A B. less(A,B) ==> divides(A,B)) /\
   (!A B. equal(A,B) ==> divides(A,B)) /\
   (less(b,c)) /\
   (~less(b,a)) /\
   (divides(c,a)) /\
   (!A. ~equal(successor(A),0)) ==> F`--);
  

val NUM024_1 = 
 (--`(!X. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!A. equal(add(A,0),A)) /\
   (!A B. equal(add(A,successor(B)),successor(add(A,B)))) /\
   (!A. equal(multiply(A,0),0)) /\
   (!B A. equal(multiply(A,successor(B)),add(multiply(A,B),A))) /\
   (!A B. equal(successor(A),successor(B)) ==> equal(A,B)) /\
   (!A B. equal(A,B) ==> equal(successor(A),successor(B))) /\
   (!A C B. less(A,B) /\ less(C,A) ==> less(C,B)) /\
   (!A B C. equal(add(successor(A),B),C) ==> less(B,C)) /\
   (!A B. less(A,B) ==> equal(add(successor(predecessor_of_1st_minus_2nd(B,A)),A),B)) /\
   (!B A. equal(add(A,B),add(B,A))) /\
   (!B A C. equal(add(A,B),add(C,B)) ==> equal(A,C)) /\
   (less(a,a)) /\
   (!A. ~equal(successor(A),0)) ==> F`--);
  

val NUM180_1 = 
Lib.with_flag(Globals.guessing_tyvars,false)
 Term
`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X U Y. subclass(X,Y) /\ member(U,X) ==> member(U,Y)) /\
   (!X Y. member(not_subclass_element(X,Y),X) \/ subclass(X,Y)) /\
   (!X Y. member(not_subclass_element(X,Y),Y) ==> subclass(X,Y)) /\
   (!X. subclass(X,universal_class)) /\
   (!X Y. equal(X,Y) ==> subclass(X,Y)) /\
   (!Y X. equal(X,Y) ==> subclass(Y,X)) /\
   (!X Y. subclass(X,Y) /\ subclass(Y,X) ==> equal(X,Y)) /\
   (!X U Y. member(U,unordered_pair(X,Y)) ==> equal(U,X) \/ equal(U,Y)) /\
   (!X Y. member(X,universal_class) ==> member(X,unordered_pair(X,Y))) /\
   (!X Y. member(Y,universal_class) ==> member(Y,unordered_pair(X,Y))) /\
   (!X Y. member(unordered_pair(X,Y),universal_class)) /\
   (!X. equal(unordered_pair(X,X),singleton(X))) /\
   (!X Y. equal(unordered_pair(singleton(X),unordered_pair(X,singleton(Y))),ordered_pair(X,Y))) /\
   (!V Y U X. member(ordered_pair(U,V),cross_product(X,Y)) ==> member(U,X)) /\
   (!U X V Y. member(ordered_pair(U,V),cross_product(X,Y)) ==> member(V,Y)) /\
   (!U V X Y. member(U,X) /\ member(V,Y) ==> member(ordered_pair(U,V),cross_product(X,Y))) /\
   (!X Y Z. member(Z,cross_product(X,Y)) ==> equal(ordered_pair(first(Z),second(Z)),Z)) /\
   (subclass(element_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),element_relation) ==> member(X,Y)) /\
   (!X Y. member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) /\ member(X,Y) ==> member(ordered_pair(X,Y),element_relation)) /\
   (!Y Z X. member(Z,intersection(X,Y)) ==> member(Z,X)) /\
   (!X Z Y. member(Z,intersection(X,Y)) ==> member(Z,Y)) /\
   (!Z X Y. member(Z,X) /\ member(Z,Y) ==> member(Z,intersection(X,Y))) /\
   (!Z X. ~(member(Z,complement(X)) /\ member(Z,X))) /\
   (!Z X. member(Z,universal_class) ==> member(Z,complement(X)) \/ member(Z,X)) /\
   (!X Y. equal(complement(intersection(complement(X),complement(Y))),union(X,Y))) /\
   (!X Y. equal(intersection(complement(intersection(X,Y)),complement(intersection(complement(X),complement(Y)))),difference(X,Y))) /\
   (!Xr X Y. equal(intersection(Xr,cross_product(X,Y)),restrict(Xr,X,Y))) /\
   (!Xr X Y. equal(intersection(cross_product(X,Y),Xr),restrict(Xr,X,Y))) /\
   (!Z X. ~(equal(restrict(X,singleton(Z),universal_class),null_class) /\ member(Z,domain_of(X)))) /\
   (!Z X. member(Z,universal_class) ==> equal(restrict(X,singleton(Z),universal_class),null_class) \/ member(Z,domain_of(X))) /\
   (!X. subclass(rotate(X),cross_product(cross_product(universal_class,universal_class),universal_class))) /\
   (!V W U X. member(ordered_pair(ordered_pair(U,V),W),rotate(X)) ==> member(ordered_pair(ordered_pair(V,W),U),X)) /\
   (!U V W X. member(ordered_pair(ordered_pair(V,W),U),X) /\ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class)) ==> member(ordered_pair(ordered_pair(U,V),W),rotate(X))) /\
   (!X. subclass(flip(X),cross_product(cross_product(universal_class,universal_class),universal_class))) /\
   (!V U W X. member(ordered_pair(ordered_pair(U,V),W),flip(X)) ==> member(ordered_pair(ordered_pair(V,U),W),X)) /\
   (!U V W X. member(ordered_pair(ordered_pair(V,U),W),X) /\ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class)) ==> member(ordered_pair(ordered_pair(U,V),W),flip(X))) /\
   (!Y. equal(domain_of(flip(cross_product(Y,universal_class))),inverse(Y))) /\
   (!Z. equal(domain_of(inverse(Z)),range_of(Z))) /\
   (!Z X Y. equal(first(not_subclass_element(restrict(Z,X,singleton(Y)),null_class)),domain(Z,X,Y))) /\
   (!Z X Y. equal(second(not_subclass_element(restrict(Z,singleton(X),Y),null_class)),range(Z,X,Y))) /\
   (!Xr X. equal(range_of(restrict(Xr,X,universal_class)),image(Xr,X))) /\
   (!X. equal(union(X,singleton(X)),successor(X))) /\
   (subclass(successor_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),successor_relation) ==> equal(successor(X),Y)) /\
   (!X Y. equal(successor(X),Y) /\ member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) ==> member(ordered_pair(X,Y),successor_relation)) /\
   (!X. inductive(X) ==> member(null_class,X)) /\
   (!X. inductive(X) ==> subclass(image(successor_relation,X),X)) /\
   (!X. member(null_class,X) /\ subclass(image(successor_relation,X),X) ==> inductive(X)) /\
   (inductive(omega)) /\
   (!Y. inductive(Y) ==> subclass(omega,Y)) /\
   (member(omega,universal_class)) /\
   (!X. equal(domain_of(restrict(element_relation,universal_class,X)),sum_class(X))) /\
   (!X. member(X,universal_class) ==> member(sum_class(X),universal_class)) /\
   (!X. equal(complement(image(element_relation,complement(X))),power_class(X))) /\
   (!U. member(U,universal_class) ==> member(power_class(U),universal_class)) /\
   (!Yr Xr. subclass(compose(Yr,Xr),cross_product(universal_class,universal_class))) /\
   (!Z Yr Xr Y. member(ordered_pair(Y,Z),compose(Yr,Xr)) ==> member(Z,image(Yr,image(Xr,singleton(Y))))) /\
   (!Y Z Yr Xr. member(Z,image(Yr,image(Xr,singleton(Y)))) /\ member(ordered_pair(Y,Z),cross_product(universal_class,universal_class)) ==> member(ordered_pair(Y,Z),compose(Yr,Xr))) /\
   (!X. single_valued_class(X) ==> subclass(compose(X,inverse(X)),identity_relation)) /\
   (!X. subclass(compose(X,inverse(X)),identity_relation) ==> single_valued_class(X)) /\
   (!Xf. function(Xf) ==> subclass(Xf,cross_product(universal_class,universal_class))) /\
   (!Xf. function(Xf) ==> subclass(compose(Xf,inverse(Xf)),identity_relation)) /\
   (!Xf. subclass(Xf,cross_product(universal_class,universal_class)) /\ subclass(compose(Xf,inverse(Xf)),identity_relation) ==> function(Xf)) /\
   (!Xf X. function(Xf) /\ member(X,universal_class) ==> member(image(Xf,X),universal_class)) /\
   (!X. equal(X,null_class) \/ member(regular(X),X)) /\
   (!X. equal(X,null_class) \/ equal(intersection(X,regular(X)),null_class)) /\
   (!Xf Y. equal(sum_class(image(Xf,singleton(Y))),apply(Xf,Y))) /\
   (function(choice)) /\
   (!Y. member(Y,universal_class) ==> equal(Y,null_class) \/ member(apply(choice,Y),Y)) /\
   (!Xf. one_to_one(Xf) ==> function(Xf)) /\
   (!Xf. one_to_one(Xf) ==> function(inverse(Xf))) /\
   (!Xf. function(inverse(Xf)) /\ function(Xf) ==> one_to_one(Xf)) /\
   (equal(intersection(cross_product(universal_class,universal_class),intersection(cross_product(universal_class,universal_class),complement(compose(complement(element_relation),inverse(element_relation))))),subset_relation)) /\
   (equal(intersection(inverse(subset_relation),subset_relation),identity_relation)) /\
   (!Xr. equal(complement(domain_of(intersection(Xr,identity_relation))),diagonalise(Xr))) /\
   (!X. equal(intersection(domain_of(X),diagonalise(compose(inverse(element_relation),X))),cantor(X))) /\
   (!Xf. operation(Xf) ==> function(Xf)) /\
   (!Xf. operation(Xf) ==> equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))) /\
   (!Xf. operation(Xf) ==> subclass(range_of(Xf),domain_of(domain_of(Xf)))) /\
   (!Xf. function(Xf) /\ equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) /\ subclass(range_of(Xf),domain_of(domain_of(Xf))) ==> operation(Xf)) /\
   (!Xf1 Xf2 Xh. compatible(Xh,Xf1,Xf2) ==> function(Xh)) /\
   (!Xf2 Xf1 Xh. compatible(Xh,Xf1,Xf2) ==> equal(domain_of(domain_of(Xf1)),domain_of(Xh))) /\
   (!Xf1 Xh Xf2. compatible(Xh,Xf1,Xf2) ==> subclass(range_of(Xh),domain_of(domain_of(Xf2)))) /\
   (!Xh Xh1 Xf1 Xf2. function(Xh) /\ equal(domain_of(domain_of(Xf1)),domain_of(Xh)) /\ subclass(range_of(Xh),domain_of(domain_of(Xf2))) ==> compatible(Xh1,Xf1,Xf2)) /\
   (!Xh Xf2 Xf1. homomorphism(Xh,Xf1,Xf2) ==> operation(Xf1)) /\
   (!Xh Xf1 Xf2. homomorphism(Xh,Xf1,Xf2) ==> operation(Xf2)) /\
   (!Xh Xf1 Xf2. homomorphism(Xh,Xf1,Xf2) ==> compatible(Xh,Xf1,Xf2)) /\
   (!Xf2 Xh Xf1 X Y. homomorphism(Xh,Xf1,Xf2) /\ member(ordered_pair(X,Y),domain_of(Xf1)) ==> equal(apply(Xf2,ordered_pair(apply(Xh,X),apply(Xh,Y))),apply(Xh,apply(Xf1,ordered_pair(X,Y))))) /\
   (!Xh Xf1 Xf2. operation(Xf1) /\ operation(Xf2) /\ compatible(Xh,Xf1,Xf2) ==> member(ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2)),domain_of(Xf1)) \/ homomorphism(Xh,Xf1,Xf2)) /\
   (!Xh Xf1 Xf2. operation(Xf1) /\ operation(Xf2) /\ compatible(Xh,Xf1,Xf2) /\ equal(apply(Xf2,ordered_pair(apply(Xh,not_homomorphism1(Xh,Xf1,Xf2)),apply(Xh,not_homomorphism2(Xh,Xf1,Xf2)))),apply(Xh,apply(Xf1,ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2))))) ==> homomorphism(Xh,Xf1,Xf2)) /\
   (!D E F'. equal(D,E) ==> equal(apply(D,F'),apply(E,F'))) /\
   (!G I' H. equal(G,H) ==> equal(apply(I',G),apply(I',H))) /\
   (!J K'. equal(J,K') ==> equal(cantor(J),cantor(K'))) /\
   (!L M. equal(L,M) ==> equal(complement(L),complement(M))) /\
   (!N O P. equal(N,O) ==> equal(compose(N,P),compose(O,P))) /\
   (!Q S' R. equal(Q,R) ==> equal(compose(S',Q),compose(S',R))) /\
   (!T' U V. equal(T',U) ==> equal(cross_product(T',V),cross_product(U,V))) /\
   (!W Y X. equal(W,X) ==> equal(cross_product(Y,W),cross_product(Y,X))) /\
   (!Z A1. equal(Z,A1) ==> equal(diagonalise(Z),diagonalise(A1))) /\
   (!B1 C1 D1. equal(B1,C1) ==> equal(difference(B1,D1),difference(C1,D1))) /\
   (!E1 G1 F1. equal(E1,F1) ==> equal(difference(G1,E1),difference(G1,F1))) /\
   (!H1 I1 J1 K1. equal(H1,I1) ==> equal(domain(H1,J1,K1),domain(I1,J1,K1))) /\
   (!L1 N1 M1 O1. equal(L1,M1) ==> equal(domain(N1,L1,O1),domain(N1,M1,O1))) /\
   (!P1 R1 S1 Q1. equal(P1,Q1) ==> equal(domain(R1,S1,P1),domain(R1,S1,Q1))) /\
   (!T1 U1. equal(T1,U1) ==> equal(domain_of(T1),domain_of(U1))) /\
   (!V1 W1. equal(V1,W1) ==> equal(first(V1),first(W1))) /\
   (!X1 Y1. equal(X1,Y1) ==> equal(flip(X1),flip(Y1))) /\
   (!Z1 A2 B2. equal(Z1,A2) ==> equal(image(Z1,B2),image(A2,B2))) /\
   (!C2 E2 D2. equal(C2,D2) ==> equal(image(E2,C2),image(E2,D2))) /\
   (!F2 G2 H2. equal(F2,G2) ==> equal(intersection(F2,H2),intersection(G2,H2))) /\
   (!I2 K2 J2. equal(I2,J2) ==> equal(intersection(K2,I2),intersection(K2,J2))) /\
   (!L2 M2. equal(L2,M2) ==> equal(inverse(L2),inverse(M2))) /\
   (!N2 O2 P2 Q2. equal(N2,O2) ==> equal(not_homomorphism1(N2,P2,Q2),not_homomorphism1(O2,P2,Q2))) /\
   (!R2 T2 S2 U2. equal(R2,S2) ==> equal(not_homomorphism1(T2,R2,U2),not_homomorphism1(T2,S2,U2))) /\
   (!V2 X2 Y2 W2. equal(V2,W2) ==> equal(not_homomorphism1(X2,Y2,V2),not_homomorphism1(X2,Y2,W2))) /\
   (!Z2 A3 B3 C3. equal(Z2,A3) ==> equal(not_homomorphism2(Z2,B3,C3),not_homomorphism2(A3,B3,C3))) /\
   (!D3 F3 E3 G3. equal(D3,E3) ==> equal(not_homomorphism2(F3,D3,G3),not_homomorphism2(F3,E3,G3))) /\
   (!H3 J3 K3 I3. equal(H3,I3) ==> equal(not_homomorphism2(J3,K3,H3),not_homomorphism2(J3,K3,I3))) /\
   (!L3 M3 N3. equal(L3,M3) ==> equal(not_subclass_element(L3,N3),not_subclass_element(M3,N3))) /\
   (!O3 Q3 P3. equal(O3,P3) ==> equal(not_subclass_element(Q3,O3),not_subclass_element(Q3,P3))) /\
   (!R3 S3 T3. equal(R3,S3) ==> equal(ordered_pair(R3,T3),ordered_pair(S3,T3))) /\
   (!U3 W3 V3. equal(U3,V3) ==> equal(ordered_pair(W3,U3),ordered_pair(W3,V3))) /\
   (!X3 Y3. equal(X3,Y3) ==> equal(power_class(X3),power_class(Y3))) /\
   (!Z3 A4 B4 C4. equal(Z3,A4) ==> equal(range(Z3,B4,C4),range(A4,B4,C4))) /\
   (!D4 F4 E4 G4. equal(D4,E4) ==> equal(range(F4,D4,G4),range(F4,E4,G4))) /\
   (!H4 J4 K4 I4. equal(H4,I4) ==> equal(range(J4,K4,H4),range(J4,K4,I4))) /\
   (!L4 M4. equal(L4,M4) ==> equal(range_of(L4),range_of(M4))) /\
   (!N4 O4. equal(N4,O4) ==> equal(regular(N4),regular(O4))) /\
   (!P4 Q4 R4 S4. equal(P4,Q4) ==> equal(restrict(P4,R4,S4),restrict(Q4,R4,S4))) /\
   (!T4 V4 U4 W4. equal(T4,U4) ==> equal(restrict(V4,T4,W4),restrict(V4,U4,W4))) /\
   (!X4 Z4 A5 Y4. equal(X4,Y4) ==> equal(restrict(Z4,A5,X4),restrict(Z4,A5,Y4))) /\
   (!B5 C5. equal(B5,C5) ==> equal(rotate(B5),rotate(C5))) /\
   (!D5 E5. equal(D5,E5) ==> equal(second(D5),second(E5))) /\
   (!F5 G5. equal(F5,G5) ==> equal(singleton(F5),singleton(G5))) /\
   (!H5 I5. equal(H5,I5) ==> equal(successor(H5),successor(I5))) /\
   (!J5 K5. equal(J5,K5) ==> equal(sum_class(J5),sum_class(K5))) /\
   (!L5 M5 N5. equal(L5,M5) ==> equal(union(L5,N5),union(M5,N5))) /\
   (!O5 Q5 P5. equal(O5,P5) ==> equal(union(Q5,O5),union(Q5,P5))) /\
   (!R5 S5 T5. equal(R5,S5) ==> equal(unordered_pair(R5,T5),unordered_pair(S5,T5))) /\
   (!U5 W5 V5. equal(U5,V5) ==> equal(unordered_pair(W5,U5),unordered_pair(W5,V5))) /\
   (!X5 Y5 Z5 A6. equal(X5,Y5) /\ compatible(X5,Z5,A6) ==> compatible(Y5,Z5,A6)) /\
   (!B6 D6 C6 E6. equal(B6,C6) /\ compatible(D6,B6,E6) ==> compatible(D6,C6,E6)) /\
   (!F6 H6 I6 G6. equal(F6,G6) /\ compatible(H6,I6,F6) ==> compatible(H6,I6,G6)) /\
   (!J6 K6. equal(J6,K6) /\ function(J6) ==> function(K6)) /\
   (!L6 M6 N6 O6. equal(L6,M6) /\ homomorphism(L6,N6,O6) ==> homomorphism(M6,N6,O6)) /\
   (!P6 R6 Q6 S6. equal(P6,Q6) /\ homomorphism(R6,P6,S6) ==> homomorphism(R6,Q6,S6)) /\
   (!T6 V6 W6 U6. equal(T6,U6) /\ homomorphism(V6,W6,T6) ==> homomorphism(V6,W6,U6)) /\
   (!X6 Y6. equal(X6,Y6) /\ inductive(X6) ==> inductive(Y6)) /\
   (!Z6 A7 B7. equal(Z6,A7) /\ member(Z6,B7) ==> member(A7,B7)) /\
   (!C7 E7 D7. equal(C7,D7) /\ member(E7,C7) ==> member(E7,D7)) /\
   (!F7 G7. equal(F7,G7) /\ one_to_one(F7) ==> one_to_one(G7)) /\
   (!H7 I7. equal(H7,I7) /\ operation(H7) ==> operation(I7)) /\
   (!J7 K7. equal(J7,K7) /\ single_valued_class(J7) ==> single_valued_class(K7)) /\
   (!L7 M7 N7. equal(L7,M7) /\ subclass(L7,N7) ==> subclass(M7,N7)) /\
   (!O7 Q7 P7. equal(O7,P7) /\ subclass(Q7,O7) ==> subclass(Q7,P7)) /\
   (!X. subclass(compose_class(X),cross_product(universal_class,universal_class))) /\
   (!X Y Z. member(ordered_pair(Y,Z),compose_class(X)) ==> equal(compose(X,Y),Z)) /\
   (!Y Z X. member(ordered_pair(Y,Z),cross_product(universal_class,universal_class)) /\ equal(compose(X,Y),Z) ==> member(ordered_pair(Y,Z),compose_class(X))) /\
   (subclass(composition_function,cross_product(universal_class,cross_product(universal_class,universal_class)))) /\
   (!X Y Z. member(ordered_pair(X,ordered_pair(Y,Z)),composition_function) ==> equal(compose(X,Y),Z)) /\
   (!X Y. member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) ==> member(ordered_pair(X,ordered_pair(Y,compose(X,Y))),composition_function)) /\
   (subclass(domain_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),domain_relation) ==> equal(domain_of(X),Y)) /\
   (!X. member(X,universal_class) ==> member(ordered_pair(X,domain_of(X)),domain_relation)) /\
   (!X. equal(first(not_subclass_element(compose(X,inverse(X)),identity_relation)),single_valued1(X))) /\
   (!X. equal(second(not_subclass_element(compose(X,inverse(X)),identity_relation)),single_valued2(X))) /\
   (!X. equal(domain(X,image(inverse(X),singleton(single_valued1(X))),single_valued2(X)),single_valued3(X))) /\
   (equal(intersection(complement(compose(element_relation,complement(identity_relation))),element_relation),singleton_relation)) /\
   (subclass(application_function,cross_product(universal_class,cross_product(universal_class,universal_class)))) /\
   (!Z Y X. member(ordered_pair(X,ordered_pair(Y,Z)),application_function) ==> member(Y,domain_of(X))) /\
   (!X Y Z. member(ordered_pair(X,ordered_pair(Y,Z)),application_function) ==> equal(apply(X,Y),Z)) /\
   (!Z X Y. member(ordered_pair(X,ordered_pair(Y,Z)),cross_product(universal_class,cross_product(universal_class,universal_class))) /\ member(Y,domain_of(X)) ==> member(ordered_pair(X,ordered_pair(Y,apply(X,Y))),application_function)) /\
   (!X Y Xf. maps(Xf,X,Y) ==> function(Xf)) /\
   (!Y Xf X. maps(Xf,X,Y) ==> equal(domain_of(Xf),X)) /\
   (!X Xf Y. maps(Xf,X,Y) ==> subclass(range_of(Xf),Y)) /\
   (!Xf Y. function(Xf) /\ subclass(range_of(Xf),Y) ==> maps(Xf,domain_of(Xf),Y)) /\
   (!L M. equal(L,M) ==> equal(compose_class(L),compose_class(M))) /\
   (!N2 O2. equal(N2,O2) ==> equal(single_valued1(N2),single_valued1(O2))) /\
   (!P2 Q2. equal(P2,Q2) ==> equal(single_valued2(P2),single_valued2(Q2))) /\
   (!R2 S2. equal(R2,S2) ==> equal(single_valued3(R2),single_valued3(S2))) /\
   (!X2 Y2 Z2 A3. equal(X2,Y2) /\ maps(X2,Z2,A3) ==> maps(Y2,Z2,A3)) /\
   (!B3 D3 C3 E3. equal(B3,C3) /\ maps(D3,B3,E3) ==> maps(D3,C3,E3)) /\
   (!F3 H3 I3 G3. equal(F3,G3) /\ maps(H3,I3,F3) ==> maps(H3,I3,G3)) /\
   (!X. equal(union(X,inverse(X)),symmetrization_of(X))) /\
   (!X Y. irreflexive(X,Y) ==> subclass(restrict(X,Y,Y),complement(identity_relation))) /\
   (!X Y. subclass(restrict(X,Y,Y),complement(identity_relation)) ==> irreflexive(X,Y)) /\
   (!Y X. connected(X,Y) ==> subclass(cross_product(Y,Y),union(identity_relation,symmetrization_of(X)))) /\
   (!X Y. subclass(cross_product(Y,Y),union(identity_relation,symmetrization_of(X))) ==> connected(X,Y)) /\
   (!Xr Y. transitive(Xr,Y) ==> subclass(compose(restrict(Xr,Y,Y),restrict(Xr,Y,Y)),restrict(Xr,Y,Y))) /\
   (!Xr Y. subclass(compose(restrict(Xr,Y,Y),restrict(Xr,Y,Y)),restrict(Xr,Y,Y)) ==> transitive(Xr,Y)) /\
   (!Xr Y. asymmetric(Xr,Y) ==> equal(restrict(intersection(Xr,inverse(Xr)),Y,Y),null_class)) /\
   (!Xr Y. equal(restrict(intersection(Xr,inverse(Xr)),Y,Y),null_class) ==> asymmetric(Xr,Y)) /\
   (!Xr Y Z. equal(segment(Xr,Y,Z),domain_of(restrict(Xr,Y,singleton(Z))))) /\
   (!X Y. well_ordering(X,Y) ==> connected(X,Y)) /\
   (!Y Xr U. well_ordering(Xr,Y) /\ subclass(U,Y) ==> equal(U,null_class) \/ member(least(Xr,U),U)) /\
   (!Y V Xr U. well_ordering(Xr,Y) /\ subclass(U,Y) /\ member(V,U) ==> member(least(Xr,U),U)) /\
   (!Y Xr U. well_ordering(Xr,Y) /\ subclass(U,Y) ==> equal(segment(Xr,U,least(Xr,U)),null_class)) /\
   (!Y V U Xr. ~(well_ordering(Xr,Y) /\ subclass(U,Y) /\ member(V,U) /\ member(ordered_pair(V,least(Xr,U)),Xr))) /\
   (!Xr Y. connected(Xr,Y) /\ equal(not_well_ordering(Xr,Y),null_class) ==> well_ordering(Xr,Y)) /\
   (!Xr Y. connected(Xr,Y) ==> subclass(not_well_ordering(Xr,Y),Y) \/ well_ordering(Xr,Y)) /\
   (!V Xr Y. member(V,not_well_ordering(Xr,Y)) /\ equal(segment(Xr,not_well_ordering(Xr,Y),V),null_class) /\ connected(Xr,Y) ==> well_ordering(Xr,Y)) /\
   (!Xr Y Z. section(Xr,Y,Z) ==> subclass(Y,Z)) /\
   (!Xr Z Y. section(Xr,Y,Z) ==> subclass(domain_of(restrict(Xr,Z,Y)),Y)) /\
   (!Xr Y Z. subclass(Y,Z) /\ subclass(domain_of(restrict(Xr,Z,Y)),Y) ==> section(Xr,Y,Z)) /\
   (!X. member(X,ordinal_numbers) ==> well_ordering(element_relation,X)) /\
   (!X. member(X,ordinal_numbers) ==> subclass(sum_class(X),X)) /\
   (!X. well_ordering(element_relation,X) /\ subclass(sum_class(X),X) /\ member(X,universal_class) ==> member(X,ordinal_numbers)) /\
   (!X. well_ordering(element_relation,X) /\ subclass(sum_class(X),X) ==> member(X,ordinal_numbers) \/ equal(X,ordinal_numbers)) /\
   (equal(union(singleton(null_class),image(successor_relation,ordinal_numbers)),kind_1_ordinals)) /\
   (equal(intersection(complement(kind_1_ordinals),ordinal_numbers),limit_ordinals)) /\
   (!X. subclass(rest_of(X),cross_product(universal_class,universal_class))) /\
   (!V U X. member(ordered_pair(U,V),rest_of(X)) ==> member(U,domain_of(X))) /\
   (!X U V. member(ordered_pair(U,V),rest_of(X)) ==> equal(restrict(X,U,universal_class),V)) /\
   (!U V X. member(U,domain_of(X)) /\ equal(restrict(X,U,universal_class),V) ==> member(ordered_pair(U,V),rest_of(X))) /\
   (subclass(rest_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),rest_relation) ==> equal(rest_of(X),Y)) /\
   (!X. member(X,universal_class) ==> member(ordered_pair(X,rest_of(X)),rest_relation)) /\
   (!X Z. member(X,recursion_equation_functions(Z)) ==> function(Z)) /\
   (!Z X. member(X,recursion_equation_functions(Z)) ==> function(X)) /\
   (!Z X. member(X,recursion_equation_functions(Z)) ==> member(domain_of(X),ordinal_numbers)) /\
   (!Z X. member(X,recursion_equation_functions(Z)) ==> equal(compose(Z,rest_of(X)),X)) /\
   (!X Z. function(Z) /\ function(X) /\ member(domain_of(X),ordinal_numbers) /\ equal(compose(Z,rest_of(X)),X) ==> member(X,recursion_equation_functions(Z))) /\
   (subclass(union_of_range_map,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),union_of_range_map) ==> equal(sum_class(range_of(X)),Y)) /\
   (!X Y. member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) /\ equal(sum_class(range_of(X)),Y) ==> member(ordered_pair(X,Y),union_of_range_map)) /\
   (!X Y. equal(apply(recursion(X,successor_relation,union_of_range_map),Y),ordinal_add(X,Y))) /\
   (!X Y. equal(recursion(null_class,apply(add_relation,X),union_of_range_map),ordinal_multiply(X,Y))) /\
   (!X. member(X,omega) ==> equal(integer_of(X),X)) /\
   (!X. member(X,omega) \/ equal(integer_of(X),null_class)) /\
   (!D E. equal(D,E) ==> equal(integer_of(D),integer_of(E))) /\
   (!F' G H. equal(F',G) ==> equal(least(F',H),least(G,H))) /\
   (!I' K' J. equal(I',J) ==> equal(least(K',I'),least(K',J))) /\
   (!L M N. equal(L,M) ==> equal(not_well_ordering(L,N),not_well_ordering(M,N))) /\
   (!O Q P. equal(O,P) ==> equal(not_well_ordering(Q,O),not_well_ordering(Q,P))) /\
   (!R S' T'. equal(R,S') ==> equal(ordinal_add(R,T'),ordinal_add(S',T'))) /\
   (!U W V. equal(U,V) ==> equal(ordinal_add(W,U),ordinal_add(W,V))) /\
   (!X Y Z. equal(X,Y) ==> equal(ordinal_multiply(X,Z),ordinal_multiply(Y,Z))) /\
   (!A1 C1 B1. equal(A1,B1) ==> equal(ordinal_multiply(C1,A1),ordinal_multiply(C1,B1))) /\
   (!F1 G1 H1 I1. equal(F1,G1) ==> equal(recursion(F1,H1,I1),recursion(G1,H1,I1))) /\
   (!J1 L1 K1 M1. equal(J1,K1) ==> equal(recursion(L1,J1,M1),recursion(L1,K1,M1))) /\
   (!N1 P1 Q1 O1. equal(N1,O1) ==> equal(recursion(P1,Q1,N1),recursion(P1,Q1,O1))) /\
   (!R1 S1. equal(R1,S1) ==> equal(recursion_equation_functions(R1),recursion_equation_functions(S1))) /\
   (!T1 U1. equal(T1,U1) ==> equal(rest_of(T1),rest_of(U1))) /\
   (!V1 W1 X1 Y1. equal(V1,W1) ==> equal(segment(V1,X1,Y1),segment(W1,X1,Y1))) /\
   (!Z1 B2 A2 C2. equal(Z1,A2) ==> equal(segment(B2,Z1,C2),segment(B2,A2,C2))) /\
   (!D2 F2 G2 E2. equal(D2,E2) ==> equal(segment(F2,G2,D2),segment(F2,G2,E2))) /\
   (!H2 I2. equal(H2,I2) ==> equal(symmetrization_of(H2),symmetrization_of(I2))) /\
   (!J2 K2 L2. equal(J2,K2) /\ asymmetric(J2,L2) ==> asymmetric(K2,L2)) /\
   (!M2 O2 N2. equal(M2,N2) /\ asymmetric(O2,M2) ==> asymmetric(O2,N2)) /\
   (!P2 Q2 R2. equal(P2,Q2) /\ connected(P2,R2) ==> connected(Q2,R2)) /\
   (!S2 U2 T2. equal(S2,T2) /\ connected(U2,S2) ==> connected(U2,T2)) /\
   (!V2 W2 X2. equal(V2,W2) /\ irreflexive(V2,X2) ==> irreflexive(W2,X2)) /\
   (!Y2 A3 Z2. equal(Y2,Z2) /\ irreflexive(A3,Y2) ==> irreflexive(A3,Z2)) /\
   (!B3 C3 D3 E3. equal(B3,C3) /\ section(B3,D3,E3) ==> section(C3,D3,E3)) /\
   (!F3 H3 G3 I3. equal(F3,G3) /\ section(H3,F3,I3) ==> section(H3,G3,I3)) /\
   (!J3 L3 M3 K3. equal(J3,K3) /\ section(L3,M3,J3) ==> section(L3,M3,K3)) /\
   (!N3 O3 P3. equal(N3,O3) /\ transitive(N3,P3) ==> transitive(O3,P3)) /\
   (!Q3 S3 R3. equal(Q3,R3) /\ transitive(S3,Q3) ==> transitive(S3,R3)) /\
   (!T3 U3 V3. equal(T3,U3) /\ well_ordering(T3,V3) ==> well_ordering(U3,V3)) /\
   (!W3 Y3 X3. equal(W3,X3) /\ well_ordering(Y3,W3) ==> well_ordering(Y3,X3)) /\
   (~subclass(limit_ordinals,ordinal_numbers)) ==> F`;
  

val NUM228_1 = 
Lib.with_flag(Globals.guessing_tyvars,false)
 Term
`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X U Y. subclass(X,Y) /\ member(U,X) ==> member(U,Y)) /\
   (!X Y. member(not_subclass_element(X,Y),X) \/ subclass(X,Y)) /\
   (!X Y. member(not_subclass_element(X,Y),Y) ==> subclass(X,Y)) /\
   (!X. subclass(X,universal_class)) /\
   (!X Y. equal(X,Y) ==> subclass(X,Y)) /\
   (!Y X. equal(X,Y) ==> subclass(Y,X)) /\
   (!X Y. subclass(X,Y) /\ subclass(Y,X) ==> equal(X,Y)) /\
   (!X U Y. member(U,unordered_pair(X,Y)) ==> equal(U,X) \/ equal(U,Y)) /\
   (!X Y. member(X,universal_class) ==> member(X,unordered_pair(X,Y))) /\
   (!X Y. member(Y,universal_class) ==> member(Y,unordered_pair(X,Y))) /\
   (!X Y. member(unordered_pair(X,Y),universal_class)) /\
   (!X. equal(unordered_pair(X,X),singleton(X))) /\
   (!X Y. equal(unordered_pair(singleton(X),unordered_pair(X,singleton(Y))),ordered_pair(X,Y))) /\
   (!V Y U X. member(ordered_pair(U,V),cross_product(X,Y)) ==> member(U,X)) /\
   (!U X V Y. member(ordered_pair(U,V),cross_product(X,Y)) ==> member(V,Y)) /\
   (!U V X Y. member(U,X) /\ member(V,Y) ==> member(ordered_pair(U,V),cross_product(X,Y))) /\
   (!X Y Z. member(Z,cross_product(X,Y)) ==> equal(ordered_pair(first(Z),second(Z)),Z)) /\
   (subclass(element_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),element_relation) ==> member(X,Y)) /\
   (!X Y. member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) /\ member(X,Y) ==> member(ordered_pair(X,Y),element_relation)) /\
   (!Y Z X. member(Z,intersection(X,Y)) ==> member(Z,X)) /\
   (!X Z Y. member(Z,intersection(X,Y)) ==> member(Z,Y)) /\
   (!Z X Y. member(Z,X) /\ member(Z,Y) ==> member(Z,intersection(X,Y))) /\
   (!Z X. ~(member(Z,complement(X)) /\ member(Z,X))) /\
   (!Z X. member(Z,universal_class) ==> member(Z,complement(X)) \/ member(Z,X)) /\
   (!X Y. equal(complement(intersection(complement(X),complement(Y))),union(X,Y))) /\
   (!X Y. equal(intersection(complement(intersection(X,Y)),complement(intersection(complement(X),complement(Y)))),difference(X,Y))) /\
   (!Xr X Y. equal(intersection(Xr,cross_product(X,Y)),restrict(Xr,X,Y))) /\
   (!Xr X Y. equal(intersection(cross_product(X,Y),Xr),restrict(Xr,X,Y))) /\
   (!Z X. ~(equal(restrict(X,singleton(Z),universal_class),null_class) /\ member(Z,domain_of(X)))) /\
   (!Z X. member(Z,universal_class) ==> equal(restrict(X,singleton(Z),universal_class),null_class) \/ member(Z,domain_of(X))) /\
   (!X. subclass(rotate(X),cross_product(cross_product(universal_class,universal_class),universal_class))) /\
   (!V W U X. member(ordered_pair(ordered_pair(U,V),W),rotate(X)) ==> member(ordered_pair(ordered_pair(V,W),U),X)) /\
   (!U V W X. member(ordered_pair(ordered_pair(V,W),U),X) /\ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class)) ==> member(ordered_pair(ordered_pair(U,V),W),rotate(X))) /\
   (!X. subclass(flip(X),cross_product(cross_product(universal_class,universal_class),universal_class))) /\
   (!V U W X. member(ordered_pair(ordered_pair(U,V),W),flip(X)) ==> member(ordered_pair(ordered_pair(V,U),W),X)) /\
   (!U V W X. member(ordered_pair(ordered_pair(V,U),W),X) /\ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class)) ==> member(ordered_pair(ordered_pair(U,V),W),flip(X))) /\
   (!Y. equal(domain_of(flip(cross_product(Y,universal_class))),inverse(Y))) /\
   (!Z. equal(domain_of(inverse(Z)),range_of(Z))) /\
   (!Z X Y. equal(first(not_subclass_element(restrict(Z,X,singleton(Y)),null_class)),domain(Z,X,Y))) /\
   (!Z X Y. equal(second(not_subclass_element(restrict(Z,singleton(X),Y),null_class)),range(Z,X,Y))) /\
   (!Xr X. equal(range_of(restrict(Xr,X,universal_class)),image(Xr,X))) /\
   (!X. equal(union(X,singleton(X)),successor(X))) /\
   (subclass(successor_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),successor_relation) ==> equal(successor(X),Y)) /\
   (!X Y. equal(successor(X),Y) /\ member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) ==> member(ordered_pair(X,Y),successor_relation)) /\
   (!X. inductive(X) ==> member(null_class,X)) /\
   (!X. inductive(X) ==> subclass(image(successor_relation,X),X)) /\
   (!X. member(null_class,X) /\ subclass(image(successor_relation,X),X) ==> inductive(X)) /\
   (inductive(omega)) /\
   (!Y. inductive(Y) ==> subclass(omega,Y)) /\
   (member(omega,universal_class)) /\
   (!X. equal(domain_of(restrict(element_relation,universal_class,X)),sum_class(X))) /\
   (!X. member(X,universal_class) ==> member(sum_class(X),universal_class)) /\
   (!X. equal(complement(image(element_relation,complement(X))),power_class(X))) /\
   (!U. member(U,universal_class) ==> member(power_class(U),universal_class)) /\
   (!Yr Xr. subclass(compose(Yr,Xr),cross_product(universal_class,universal_class))) /\
   (!Z Yr Xr Y. member(ordered_pair(Y,Z),compose(Yr,Xr)) ==> member(Z,image(Yr,image(Xr,singleton(Y))))) /\
   (!Y Z Yr Xr. member(Z,image(Yr,image(Xr,singleton(Y)))) /\ member(ordered_pair(Y,Z),cross_product(universal_class,universal_class)) ==> member(ordered_pair(Y,Z),compose(Yr,Xr))) /\
   (!X. single_valued_class(X) ==> subclass(compose(X,inverse(X)),identity_relation)) /\
   (!X. subclass(compose(X,inverse(X)),identity_relation) ==> single_valued_class(X)) /\
   (!Xf. function(Xf) ==> subclass(Xf,cross_product(universal_class,universal_class))) /\
   (!Xf. function(Xf) ==> subclass(compose(Xf,inverse(Xf)),identity_relation)) /\
   (!Xf. subclass(Xf,cross_product(universal_class,universal_class)) /\ subclass(compose(Xf,inverse(Xf)),identity_relation) ==> function(Xf)) /\
   (!Xf X. function(Xf) /\ member(X,universal_class) ==> member(image(Xf,X),universal_class)) /\
   (!X. equal(X,null_class) \/ member(regular(X),X)) /\
   (!X. equal(X,null_class) \/ equal(intersection(X,regular(X)),null_class)) /\
   (!Xf Y. equal(sum_class(image(Xf,singleton(Y))),apply(Xf,Y))) /\
   (function(choice)) /\
   (!Y. member(Y,universal_class) ==> equal(Y,null_class) \/ member(apply(choice,Y),Y)) /\
   (!Xf. one_to_one(Xf) ==> function(Xf)) /\
   (!Xf. one_to_one(Xf) ==> function(inverse(Xf))) /\
   (!Xf. function(inverse(Xf)) /\ function(Xf) ==> one_to_one(Xf)) /\
   (equal(intersection(cross_product(universal_class,universal_class),intersection(cross_product(universal_class,universal_class),complement(compose(complement(element_relation),inverse(element_relation))))),subset_relation)) /\
   (equal(intersection(inverse(subset_relation),subset_relation),identity_relation)) /\
   (!Xr. equal(complement(domain_of(intersection(Xr,identity_relation))),diagonalise(Xr))) /\
   (!X. equal(intersection(domain_of(X),diagonalise(compose(inverse(element_relation),X))),cantor(X))) /\
   (!Xf. operation(Xf) ==> function(Xf)) /\
   (!Xf. operation(Xf) ==> equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))) /\
   (!Xf. operation(Xf) ==> subclass(range_of(Xf),domain_of(domain_of(Xf)))) /\
   (!Xf. function(Xf) /\ equal(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) /\ subclass(range_of(Xf),domain_of(domain_of(Xf))) ==> operation(Xf)) /\
   (!Xf1 Xf2 Xh. compatible(Xh,Xf1,Xf2) ==> function(Xh)) /\
   (!Xf2 Xf1 Xh. compatible(Xh,Xf1,Xf2) ==> equal(domain_of(domain_of(Xf1)),domain_of(Xh))) /\
   (!Xf1 Xh Xf2. compatible(Xh,Xf1,Xf2) ==> subclass(range_of(Xh),domain_of(domain_of(Xf2)))) /\
   (!Xh Xh1 Xf1 Xf2. function(Xh) /\ equal(domain_of(domain_of(Xf1)),domain_of(Xh)) /\ subclass(range_of(Xh),domain_of(domain_of(Xf2))) ==> compatible(Xh1,Xf1,Xf2)) /\
   (!Xh Xf2 Xf1. homomorphism(Xh,Xf1,Xf2) ==> operation(Xf1)) /\
   (!Xh Xf1 Xf2. homomorphism(Xh,Xf1,Xf2) ==> operation(Xf2)) /\
   (!Xh Xf1 Xf2. homomorphism(Xh,Xf1,Xf2) ==> compatible(Xh,Xf1,Xf2)) /\
   (!Xf2 Xh Xf1 X Y. homomorphism(Xh,Xf1,Xf2) /\ member(ordered_pair(X,Y),domain_of(Xf1)) ==> equal(apply(Xf2,ordered_pair(apply(Xh,X),apply(Xh,Y))),apply(Xh,apply(Xf1,ordered_pair(X,Y))))) /\
   (!Xh Xf1 Xf2. operation(Xf1) /\ operation(Xf2) /\ compatible(Xh,Xf1,Xf2) ==> member(ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2)),domain_of(Xf1)) \/ homomorphism(Xh,Xf1,Xf2)) /\
   (!Xh Xf1 Xf2. operation(Xf1) /\ operation(Xf2) /\ compatible(Xh,Xf1,Xf2) /\ equal(apply(Xf2,ordered_pair(apply(Xh,not_homomorphism1(Xh,Xf1,Xf2)),apply(Xh,not_homomorphism2(Xh,Xf1,Xf2)))),apply(Xh,apply(Xf1,ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2))))) ==> homomorphism(Xh,Xf1,Xf2)) /\
   (!D E F'. equal(D,E) ==> equal(apply(D,F'),apply(E,F'))) /\
   (!G I' H. equal(G,H) ==> equal(apply(I',G),apply(I',H))) /\
   (!J K'. equal(J,K') ==> equal(cantor(J),cantor(K'))) /\
   (!L M. equal(L,M) ==> equal(complement(L),complement(M))) /\
   (!N O P. equal(N,O) ==> equal(compose(N,P),compose(O,P))) /\
   (!Q S' R. equal(Q,R) ==> equal(compose(S',Q),compose(S',R))) /\
   (!T' U V. equal(T',U) ==> equal(cross_product(T',V),cross_product(U,V))) /\
   (!W Y X. equal(W,X) ==> equal(cross_product(Y,W),cross_product(Y,X))) /\
   (!Z A1. equal(Z,A1) ==> equal(diagonalise(Z),diagonalise(A1))) /\
   (!B1 C1 D1. equal(B1,C1) ==> equal(difference(B1,D1),difference(C1,D1))) /\
   (!E1 G1 F1. equal(E1,F1) ==> equal(difference(G1,E1),difference(G1,F1))) /\
   (!H1 I1 J1 K1. equal(H1,I1) ==> equal(domain(H1,J1,K1),domain(I1,J1,K1))) /\
   (!L1 N1 M1 O1. equal(L1,M1) ==> equal(domain(N1,L1,O1),domain(N1,M1,O1))) /\
   (!P1 R1 S1 Q1. equal(P1,Q1) ==> equal(domain(R1,S1,P1),domain(R1,S1,Q1))) /\
   (!T1 U1. equal(T1,U1) ==> equal(domain_of(T1),domain_of(U1))) /\
   (!V1 W1. equal(V1,W1) ==> equal(first(V1),first(W1))) /\
   (!X1 Y1. equal(X1,Y1) ==> equal(flip(X1),flip(Y1))) /\
   (!Z1 A2 B2. equal(Z1,A2) ==> equal(image(Z1,B2),image(A2,B2))) /\
   (!C2 E2 D2. equal(C2,D2) ==> equal(image(E2,C2),image(E2,D2))) /\
   (!F2 G2 H2. equal(F2,G2) ==> equal(intersection(F2,H2),intersection(G2,H2))) /\
   (!I2 K2 J2. equal(I2,J2) ==> equal(intersection(K2,I2),intersection(K2,J2))) /\
   (!L2 M2. equal(L2,M2) ==> equal(inverse(L2),inverse(M2))) /\
   (!N2 O2 P2 Q2. equal(N2,O2) ==> equal(not_homomorphism1(N2,P2,Q2),not_homomorphism1(O2,P2,Q2))) /\
   (!R2 T2 S2 U2. equal(R2,S2) ==> equal(not_homomorphism1(T2,R2,U2),not_homomorphism1(T2,S2,U2))) /\
   (!V2 X2 Y2 W2. equal(V2,W2) ==> equal(not_homomorphism1(X2,Y2,V2),not_homomorphism1(X2,Y2,W2))) /\
   (!Z2 A3 B3 C3. equal(Z2,A3) ==> equal(not_homomorphism2(Z2,B3,C3),not_homomorphism2(A3,B3,C3))) /\
   (!D3 F3 E3 G3. equal(D3,E3) ==> equal(not_homomorphism2(F3,D3,G3),not_homomorphism2(F3,E3,G3))) /\
   (!H3 J3 K3 I3. equal(H3,I3) ==> equal(not_homomorphism2(J3,K3,H3),not_homomorphism2(J3,K3,I3))) /\
   (!L3 M3 N3. equal(L3,M3) ==> equal(not_subclass_element(L3,N3),not_subclass_element(M3,N3))) /\
   (!O3 Q3 P3. equal(O3,P3) ==> equal(not_subclass_element(Q3,O3),not_subclass_element(Q3,P3))) /\
   (!R3 S3 T3. equal(R3,S3) ==> equal(ordered_pair(R3,T3),ordered_pair(S3,T3))) /\
   (!U3 W3 V3. equal(U3,V3) ==> equal(ordered_pair(W3,U3),ordered_pair(W3,V3))) /\
   (!X3 Y3. equal(X3,Y3) ==> equal(power_class(X3),power_class(Y3))) /\
   (!Z3 A4 B4 C4. equal(Z3,A4) ==> equal(range(Z3,B4,C4),range(A4,B4,C4))) /\
   (!D4 F4 E4 G4. equal(D4,E4) ==> equal(range(F4,D4,G4),range(F4,E4,G4))) /\
   (!H4 J4 K4 I4. equal(H4,I4) ==> equal(range(J4,K4,H4),range(J4,K4,I4))) /\
   (!L4 M4. equal(L4,M4) ==> equal(range_of(L4),range_of(M4))) /\
   (!N4 O4. equal(N4,O4) ==> equal(regular(N4),regular(O4))) /\
   (!P4 Q4 R4 S4. equal(P4,Q4) ==> equal(restrict(P4,R4,S4),restrict(Q4,R4,S4))) /\
   (!T4 V4 U4 W4. equal(T4,U4) ==> equal(restrict(V4,T4,W4),restrict(V4,U4,W4))) /\
   (!X4 Z4 A5 Y4. equal(X4,Y4) ==> equal(restrict(Z4,A5,X4),restrict(Z4,A5,Y4))) /\
   (!B5 C5. equal(B5,C5) ==> equal(rotate(B5),rotate(C5))) /\
   (!D5 E5. equal(D5,E5) ==> equal(second(D5),second(E5))) /\
   (!F5 G5. equal(F5,G5) ==> equal(singleton(F5),singleton(G5))) /\
   (!H5 I5. equal(H5,I5) ==> equal(successor(H5),successor(I5))) /\
   (!J5 K5. equal(J5,K5) ==> equal(sum_class(J5),sum_class(K5))) /\
   (!L5 M5 N5. equal(L5,M5) ==> equal(union(L5,N5),union(M5,N5))) /\
   (!O5 Q5 P5. equal(O5,P5) ==> equal(union(Q5,O5),union(Q5,P5))) /\
   (!R5 S5 T5. equal(R5,S5) ==> equal(unordered_pair(R5,T5),unordered_pair(S5,T5))) /\
   (!U5 W5 V5. equal(U5,V5) ==> equal(unordered_pair(W5,U5),unordered_pair(W5,V5))) /\
   (!X5 Y5 Z5 A6. equal(X5,Y5) /\ compatible(X5,Z5,A6) ==> compatible(Y5,Z5,A6)) /\
   (!B6 D6 C6 E6. equal(B6,C6) /\ compatible(D6,B6,E6) ==> compatible(D6,C6,E6)) /\
   (!F6 H6 I6 G6. equal(F6,G6) /\ compatible(H6,I6,F6) ==> compatible(H6,I6,G6)) /\
   (!J6 K6. equal(J6,K6) /\ function(J6) ==> function(K6)) /\
   (!L6 M6 N6 O6. equal(L6,M6) /\ homomorphism(L6,N6,O6) ==> homomorphism(M6,N6,O6)) /\
   (!P6 R6 Q6 S6. equal(P6,Q6) /\ homomorphism(R6,P6,S6) ==> homomorphism(R6,Q6,S6)) /\
   (!T6 V6 W6 U6. equal(T6,U6) /\ homomorphism(V6,W6,T6) ==> homomorphism(V6,W6,U6)) /\
   (!X6 Y6. equal(X6,Y6) /\ inductive(X6) ==> inductive(Y6)) /\
   (!Z6 A7 B7. equal(Z6,A7) /\ member(Z6,B7) ==> member(A7,B7)) /\
   (!C7 E7 D7. equal(C7,D7) /\ member(E7,C7) ==> member(E7,D7)) /\
   (!F7 G7. equal(F7,G7) /\ one_to_one(F7) ==> one_to_one(G7)) /\
   (!H7 I7. equal(H7,I7) /\ operation(H7) ==> operation(I7)) /\
   (!J7 K7. equal(J7,K7) /\ single_valued_class(J7) ==> single_valued_class(K7)) /\
   (!L7 M7 N7. equal(L7,M7) /\ subclass(L7,N7) ==> subclass(M7,N7)) /\
   (!O7 Q7 P7. equal(O7,P7) /\ subclass(Q7,O7) ==> subclass(Q7,P7)) /\
   (!X. subclass(compose_class(X),cross_product(universal_class,universal_class))) /\
   (!X Y Z. member(ordered_pair(Y,Z),compose_class(X)) ==> equal(compose(X,Y),Z)) /\
   (!Y Z X. member(ordered_pair(Y,Z),cross_product(universal_class,universal_class)) /\ equal(compose(X,Y),Z) ==> member(ordered_pair(Y,Z),compose_class(X))) /\
   (subclass(composition_function,cross_product(universal_class,cross_product(universal_class,universal_class)))) /\
   (!X Y Z. member(ordered_pair(X,ordered_pair(Y,Z)),composition_function) ==> equal(compose(X,Y),Z)) /\
   (!X Y. member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) ==> member(ordered_pair(X,ordered_pair(Y,compose(X,Y))),composition_function)) /\
   (subclass(domain_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),domain_relation) ==> equal(domain_of(X),Y)) /\
   (!X. member(X,universal_class) ==> member(ordered_pair(X,domain_of(X)),domain_relation)) /\
   (!X. equal(first(not_subclass_element(compose(X,inverse(X)),identity_relation)),single_valued1(X))) /\
   (!X. equal(second(not_subclass_element(compose(X,inverse(X)),identity_relation)),single_valued2(X))) /\
   (!X. equal(domain(X,image(inverse(X),singleton(single_valued1(X))),single_valued2(X)),single_valued3(X))) /\
   (equal(intersection(complement(compose(element_relation,complement(identity_relation))),element_relation),singleton_relation)) /\
   (subclass(application_function,cross_product(universal_class,cross_product(universal_class,universal_class)))) /\
   (!Z Y X. member(ordered_pair(X,ordered_pair(Y,Z)),application_function) ==> member(Y,domain_of(X))) /\
   (!X Y Z. member(ordered_pair(X,ordered_pair(Y,Z)),application_function) ==> equal(apply(X,Y),Z)) /\
   (!Z X Y. member(ordered_pair(X,ordered_pair(Y,Z)),cross_product(universal_class,cross_product(universal_class,universal_class))) /\ member(Y,domain_of(X)) ==> member(ordered_pair(X,ordered_pair(Y,apply(X,Y))),application_function)) /\
   (!X Y Xf. maps(Xf,X,Y) ==> function(Xf)) /\
   (!Y Xf X. maps(Xf,X,Y) ==> equal(domain_of(Xf),X)) /\
   (!X Xf Y. maps(Xf,X,Y) ==> subclass(range_of(Xf),Y)) /\
   (!Xf Y. function(Xf) /\ subclass(range_of(Xf),Y) ==> maps(Xf,domain_of(Xf),Y)) /\
   (!L M. equal(L,M) ==> equal(compose_class(L),compose_class(M))) /\
   (!N2 O2. equal(N2,O2) ==> equal(single_valued1(N2),single_valued1(O2))) /\
   (!P2 Q2. equal(P2,Q2) ==> equal(single_valued2(P2),single_valued2(Q2))) /\
   (!R2 S2. equal(R2,S2) ==> equal(single_valued3(R2),single_valued3(S2))) /\
   (!X2 Y2 Z2 A3. equal(X2,Y2) /\ maps(X2,Z2,A3) ==> maps(Y2,Z2,A3)) /\
   (!B3 D3 C3 E3. equal(B3,C3) /\ maps(D3,B3,E3) ==> maps(D3,C3,E3)) /\
   (!F3 H3 I3 G3. equal(F3,G3) /\ maps(H3,I3,F3) ==> maps(H3,I3,G3)) /\
   (!X. equal(union(X,inverse(X)),symmetrization_of(X))) /\
   (!X Y. irreflexive(X,Y) ==> subclass(restrict(X,Y,Y),complement(identity_relation))) /\
   (!X Y. subclass(restrict(X,Y,Y),complement(identity_relation)) ==> irreflexive(X,Y)) /\
   (!Y X. connected(X,Y) ==> subclass(cross_product(Y,Y),union(identity_relation,symmetrization_of(X)))) /\
   (!X Y. subclass(cross_product(Y,Y),union(identity_relation,symmetrization_of(X))) ==> connected(X,Y)) /\
   (!Xr Y. transitive(Xr,Y) ==> subclass(compose(restrict(Xr,Y,Y),restrict(Xr,Y,Y)),restrict(Xr,Y,Y))) /\
   (!Xr Y. subclass(compose(restrict(Xr,Y,Y),restrict(Xr,Y,Y)),restrict(Xr,Y,Y)) ==> transitive(Xr,Y)) /\
   (!Xr Y. asymmetric(Xr,Y) ==> equal(restrict(intersection(Xr,inverse(Xr)),Y,Y),null_class)) /\
   (!Xr Y. equal(restrict(intersection(Xr,inverse(Xr)),Y,Y),null_class) ==> asymmetric(Xr,Y)) /\
   (!Xr Y Z. equal(segment(Xr,Y,Z),domain_of(restrict(Xr,Y,singleton(Z))))) /\
   (!X Y. well_ordering(X,Y) ==> connected(X,Y)) /\
   (!Y Xr U. well_ordering(Xr,Y) /\ subclass(U,Y) ==> equal(U,null_class) \/ member(least(Xr,U),U)) /\
   (!Y V Xr U. well_ordering(Xr,Y) /\ subclass(U,Y) /\ member(V,U) ==> member(least(Xr,U),U)) /\
   (!Y Xr U. well_ordering(Xr,Y) /\ subclass(U,Y) ==> equal(segment(Xr,U,least(Xr,U)),null_class)) /\
   (!Y V U Xr. ~(well_ordering(Xr,Y) /\ subclass(U,Y) /\ member(V,U) /\ member(ordered_pair(V,least(Xr,U)),Xr))) /\
   (!Xr Y. connected(Xr,Y) /\ equal(not_well_ordering(Xr,Y),null_class) ==> well_ordering(Xr,Y)) /\
   (!Xr Y. connected(Xr,Y) ==> subclass(not_well_ordering(Xr,Y),Y) \/ well_ordering(Xr,Y)) /\
   (!V Xr Y. member(V,not_well_ordering(Xr,Y)) /\ equal(segment(Xr,not_well_ordering(Xr,Y),V),null_class) /\ connected(Xr,Y) ==> well_ordering(Xr,Y)) /\
   (!Xr Y Z. section(Xr,Y,Z) ==> subclass(Y,Z)) /\
   (!Xr Z Y. section(Xr,Y,Z) ==> subclass(domain_of(restrict(Xr,Z,Y)),Y)) /\
   (!Xr Y Z. subclass(Y,Z) /\ subclass(domain_of(restrict(Xr,Z,Y)),Y) ==> section(Xr,Y,Z)) /\
   (!X. member(X,ordinal_numbers) ==> well_ordering(element_relation,X)) /\
   (!X. member(X,ordinal_numbers) ==> subclass(sum_class(X),X)) /\
   (!X. well_ordering(element_relation,X) /\ subclass(sum_class(X),X) /\ member(X,universal_class) ==> member(X,ordinal_numbers)) /\
   (!X. well_ordering(element_relation,X) /\ subclass(sum_class(X),X) ==> member(X,ordinal_numbers) \/ equal(X,ordinal_numbers)) /\
   (equal(union(singleton(null_class),image(successor_relation,ordinal_numbers)),kind_1_ordinals)) /\
   (equal(intersection(complement(kind_1_ordinals),ordinal_numbers),limit_ordinals)) /\
   (!X. subclass(rest_of(X),cross_product(universal_class,universal_class))) /\
   (!V U X. member(ordered_pair(U,V),rest_of(X)) ==> member(U,domain_of(X))) /\
   (!X U V. member(ordered_pair(U,V),rest_of(X)) ==> equal(restrict(X,U,universal_class),V)) /\
   (!U V X. member(U,domain_of(X)) /\ equal(restrict(X,U,universal_class),V) ==> member(ordered_pair(U,V),rest_of(X))) /\
   (subclass(rest_relation,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),rest_relation) ==> equal(rest_of(X),Y)) /\
   (!X. member(X,universal_class) ==> member(ordered_pair(X,rest_of(X)),rest_relation)) /\
   (!X Z. member(X,recursion_equation_functions(Z)) ==> function(Z)) /\
   (!Z X. member(X,recursion_equation_functions(Z)) ==> function(X)) /\
   (!Z X. member(X,recursion_equation_functions(Z)) ==> member(domain_of(X),ordinal_numbers)) /\
   (!Z X. member(X,recursion_equation_functions(Z)) ==> equal(compose(Z,rest_of(X)),X)) /\
   (!X Z. function(Z) /\ function(X) /\ member(domain_of(X),ordinal_numbers) /\ equal(compose(Z,rest_of(X)),X) ==> member(X,recursion_equation_functions(Z))) /\
   (subclass(union_of_range_map,cross_product(universal_class,universal_class))) /\
   (!X Y. member(ordered_pair(X,Y),union_of_range_map) ==> equal(sum_class(range_of(X)),Y)) /\
   (!X Y. member(ordered_pair(X,Y),cross_product(universal_class,universal_class)) /\ equal(sum_class(range_of(X)),Y) ==> member(ordered_pair(X,Y),union_of_range_map)) /\
   (!X Y. equal(apply(recursion(X,successor_relation,union_of_range_map),Y),ordinal_add(X,Y))) /\
   (!X Y. equal(recursion(null_class,apply(add_relation,X),union_of_range_map),ordinal_multiply(X,Y))) /\
   (!X. member(X,omega) ==> equal(integer_of(X),X)) /\
   (!X. member(X,omega) \/ equal(integer_of(X),null_class)) /\
   (!D E. equal(D,E) ==> equal(integer_of(D),integer_of(E))) /\
   (!F' G H. equal(F',G) ==> equal(least(F',H),least(G,H))) /\
   (!I' K' J. equal(I',J) ==> equal(least(K',I'),least(K',J))) /\
   (!L M N. equal(L,M) ==> equal(not_well_ordering(L,N),not_well_ordering(M,N))) /\
   (!O Q P. equal(O,P) ==> equal(not_well_ordering(Q,O),not_well_ordering(Q,P))) /\
   (!R S' T'. equal(R,S') ==> equal(ordinal_add(R,T'),ordinal_add(S',T'))) /\
   (!U W V. equal(U,V) ==> equal(ordinal_add(W,U),ordinal_add(W,V))) /\
   (!X Y Z. equal(X,Y) ==> equal(ordinal_multiply(X,Z),ordinal_multiply(Y,Z))) /\
   (!A1 C1 B1. equal(A1,B1) ==> equal(ordinal_multiply(C1,A1),ordinal_multiply(C1,B1))) /\
   (!F1 G1 H1 I1. equal(F1,G1) ==> equal(recursion(F1,H1,I1),recursion(G1,H1,I1))) /\
   (!J1 L1 K1 M1. equal(J1,K1) ==> equal(recursion(L1,J1,M1),recursion(L1,K1,M1))) /\
   (!N1 P1 Q1 O1. equal(N1,O1) ==> equal(recursion(P1,Q1,N1),recursion(P1,Q1,O1))) /\
   (!R1 S1. equal(R1,S1) ==> equal(recursion_equation_functions(R1),recursion_equation_functions(S1))) /\
   (!T1 U1. equal(T1,U1) ==> equal(rest_of(T1),rest_of(U1))) /\
   (!V1 W1 X1 Y1. equal(V1,W1) ==> equal(segment(V1,X1,Y1),segment(W1,X1,Y1))) /\
   (!Z1 B2 A2 C2. equal(Z1,A2) ==> equal(segment(B2,Z1,C2),segment(B2,A2,C2))) /\
   (!D2 F2 G2 E2. equal(D2,E2) ==> equal(segment(F2,G2,D2),segment(F2,G2,E2))) /\
   (!H2 I2. equal(H2,I2) ==> equal(symmetrization_of(H2),symmetrization_of(I2))) /\
   (!J2 K2 L2. equal(J2,K2) /\ asymmetric(J2,L2) ==> asymmetric(K2,L2)) /\
   (!M2 O2 N2. equal(M2,N2) /\ asymmetric(O2,M2) ==> asymmetric(O2,N2)) /\
   (!P2 Q2 R2. equal(P2,Q2) /\ connected(P2,R2) ==> connected(Q2,R2)) /\
   (!S2 U2 T2. equal(S2,T2) /\ connected(U2,S2) ==> connected(U2,T2)) /\
   (!V2 W2 X2. equal(V2,W2) /\ irreflexive(V2,X2) ==> irreflexive(W2,X2)) /\
   (!Y2 A3 Z2. equal(Y2,Z2) /\ irreflexive(A3,Y2) ==> irreflexive(A3,Z2)) /\
   (!B3 C3 D3 E3. equal(B3,C3) /\ section(B3,D3,E3) ==> section(C3,D3,E3)) /\
   (!F3 H3 G3 I3. equal(F3,G3) /\ section(H3,F3,I3) ==> section(H3,G3,I3)) /\
   (!J3 L3 M3 K3. equal(J3,K3) /\ section(L3,M3,J3) ==> section(L3,M3,K3)) /\
   (!N3 O3 P3. equal(N3,O3) /\ transitive(N3,P3) ==> transitive(O3,P3)) /\
   (!Q3 S3 R3. equal(Q3,R3) /\ transitive(S3,Q3) ==> transitive(S3,R3)) /\
   (!T3 U3 V3. equal(T3,U3) /\ well_ordering(T3,V3) ==> well_ordering(U3,V3)) /\
   (!W3 Y3 X3. equal(W3,X3) /\ well_ordering(Y3,W3) ==> well_ordering(Y3,X3)) /\
   (~function(z)) /\
   (~equal(recursion_equation_functions(z),null_class)) ==> F`;
  

val PLA002_1 = 
 (--`(!Situation1 Situation2. warm(Situation1) \/ cold(Situation2)) /\
   (!Situation. at(a:'a,Situation) ==> at(b,walk(b,Situation))) /\
   (!Situation. at(a,Situation) ==> at(b,drive(b,Situation))) /\
   (!Situation. at(b,Situation) ==> at(a,walk(a,Situation))) /\
   (!Situation. at(b,Situation) ==> at(a,drive(a,Situation))) /\
   (!Situation. cold(Situation) /\ at(b,Situation) ==> at(c,skate(c,Situation))) /\
   (!Situation. cold(Situation) /\ at(c,Situation) ==> at(b,skate(b,Situation))) /\
   (!Situation. warm(Situation) /\ at(b,Situation) ==> at(d,climb(d,Situation))) /\
   (!Situation. warm(Situation) /\ at(d,Situation) ==> at(b,climb(b,Situation))) /\
   (!Situation. at(c,Situation) ==> at(d,go(d,Situation))) /\
   (!Situation. at(d,Situation) ==> at(c,go(c,Situation))) /\
   (!Situation. at(c,Situation) ==> at(e,go(e,Situation))) /\
   (!Situation. at(e,Situation) ==> at(c,go(c,Situation))) /\
   (!Situation. at(d,Situation) ==> at(f,go(f,Situation))) /\
   (!Situation:'a. at(f,Situation) ==> at(d,go(d,Situation))) /\
   (at(f,s0)) /\
   (!S'. ~at(a,S')) ==> F`--);
  

val PLA006_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Y State. holds(X,State) /\ holds(Y,State) ==> holds(and'(X,Y),State)) /\
   (!State X. holds(empty,State) /\ holds(clear(X),State) /\ differ(X,table) ==> holds(holding(X),do(pickup(X),State))) /\
   (!Y X State. holds(on(X,Y),State) /\ holds(clear(X),State) /\ holds(empty,State) ==> holds(clear(Y),do(pickup(X),State))) /\
   (!Y State X Z. holds(on(X,Y),State) /\ differ(X,Z) ==> holds(on(X,Y),do(pickup(Z),State))) /\
   (!State X Z. holds(clear(X),State) /\ differ(X,Z) ==> holds(clear(X),do(pickup(Z),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(empty,do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(on(X,Y),do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(clear(X),do(putdown(X,Y),State))) /\
   (!Z W X Y State. holds(on(X,Y),State) ==> holds(on(X,Y),do(putdown(Z,W),State))) /\
   (!X State Z Y. holds(clear(Z),State) /\ differ(Z,Y) ==> holds(clear(Z),do(putdown(X,Y),State))) /\
   (!Y X. differ(Y,X) ==> differ(X,Y)) /\
   (differ(a,b)) /\
   (differ(a,c)) /\
   (differ(a,d)) /\
   (differ(a,table)) /\
   (differ(b,c)) /\
   (differ(b,d)) /\
   (differ(b,table)) /\
   (differ(c,d)) /\
   (differ(c,table)) /\
   (differ(d,table)) /\
   (holds(on(a,table),s0)) /\
   (holds(on(b,table),s0)) /\
   (holds(on(c,d),s0)) /\
   (holds(on(d,table),s0)) /\
   (holds(clear(a),s0)) /\
   (holds(clear(b),s0)) /\
   (holds(clear(c),s0)) /\
   (holds(empty,s0)) /\
   (!State. holds(clear(table),State)) /\
   (!State. ~holds(on(c,table),State)) ==> F`;
  

val PLA017_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Y State. holds(X,State) /\ holds(Y,State) ==> holds(and'(X,Y),State)) /\
   (!State X. holds(empty,State) /\ holds(clear(X),State) /\ differ(X,table) ==> holds(holding(X),do(pickup(X),State))) /\
   (!Y X State. holds(on(X,Y),State) /\ holds(clear(X),State) /\ holds(empty,State) ==> holds(clear(Y),do(pickup(X),State))) /\
   (!Y State X Z. holds(on(X,Y),State) /\ differ(X,Z) ==> holds(on(X,Y),do(pickup(Z),State))) /\
   (!State X Z. holds(clear(X),State) /\ differ(X,Z) ==> holds(clear(X),do(pickup(Z),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(empty,do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(on(X,Y),do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(clear(X),do(putdown(X,Y),State))) /\
   (!Z W X Y State. holds(on(X,Y),State) ==> holds(on(X,Y),do(putdown(Z,W),State))) /\
   (!X State Z Y. holds(clear(Z),State) /\ differ(Z,Y) ==> holds(clear(Z),do(putdown(X,Y),State))) /\
   (!Y X. differ(Y,X) ==> differ(X,Y)) /\
   (differ(a,b)) /\
   (differ(a,c)) /\
   (differ(a,d)) /\
   (differ(a,table)) /\
   (differ(b,c)) /\
   (differ(b,d)) /\
   (differ(b,table)) /\
   (differ(c,d)) /\
   (differ(c,table)) /\
   (differ(d,table)) /\
   (holds(on(a,table),s0)) /\
   (holds(on(b,table),s0)) /\
   (holds(on(c,d),s0)) /\
   (holds(on(d,table),s0)) /\
   (holds(clear(a),s0)) /\
   (holds(clear(b),s0)) /\
   (holds(clear(c),s0)) /\
   (holds(empty,s0)) /\
   (!State. holds(clear(table),State)) /\
   (!State. ~holds(on(a,c),State)) ==> F`;
  

val PLA022_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Y State. holds(X,State) /\ holds(Y,State) ==> holds(and'(X,Y),State)) /\
   (!State X. holds(empty,State) /\ holds(clear(X),State) /\ differ(X,table) ==> holds(holding(X),do(pickup(X),State))) /\
   (!Y X State. holds(on(X,Y),State) /\ holds(clear(X),State) /\ holds(empty,State) ==> holds(clear(Y),do(pickup(X),State))) /\
   (!Y State X Z. holds(on(X,Y),State) /\ differ(X,Z) ==> holds(on(X,Y),do(pickup(Z),State))) /\
   (!State X Z. holds(clear(X),State) /\ differ(X,Z) ==> holds(clear(X),do(pickup(Z),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(empty,do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(on(X,Y),do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(clear(X),do(putdown(X,Y),State))) /\
   (!Z W X Y State. holds(on(X,Y),State) ==> holds(on(X,Y),do(putdown(Z,W),State))) /\
   (!X State Z Y. holds(clear(Z),State) /\ differ(Z,Y) ==> holds(clear(Z),do(putdown(X,Y),State))) /\
   (!Y X. differ(Y,X) ==> differ(X,Y)) /\
   (differ(a,b)) /\
   (differ(a,c)) /\
   (differ(a,d)) /\
   (differ(a,table)) /\
   (differ(b,c)) /\
   (differ(b,d)) /\
   (differ(b,table)) /\
   (differ(c,d)) /\
   (differ(c,table)) /\
   (differ(d,table)) /\
   (holds(on(a,table),s0)) /\
   (holds(on(b,table),s0)) /\
   (holds(on(c,d),s0)) /\
   (holds(on(d,table),s0)) /\
   (holds(clear(a),s0)) /\
   (holds(clear(b),s0)) /\
   (holds(clear(c),s0)) /\
   (holds(empty,s0)) /\
   (!State. holds(clear(table),State)) /\
   (!State. ~holds(and'(on(c,d),on(a,c)),State)) ==> F`;


val PLA022_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Y State. holds(X,State) /\ holds(Y,State) ==> holds(and'(X,Y),State)) /\
   (!State X. holds(empty,State) /\ holds(clear(X),State) /\ differ(X,table) ==> holds(holding(X),do(pickup(X),State))) /\
   (!Y X State. holds(on(X,Y),State) /\ holds(clear(X),State) /\ holds(empty,State) ==> holds(clear(Y),do(pickup(X),State))) /\
   (!Y State X Z. holds(on(X,Y),State) /\ differ(X,Z) ==> holds(on(X,Y),do(pickup(Z),State))) /\
   (!State X Z. holds(clear(X),State) /\ differ(X,Z) ==> holds(clear(X),do(pickup(Z),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(empty,do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(on(X,Y),do(putdown(X,Y),State))) /\
   (!X Y State. holds(holding(X),State) /\ holds(clear(Y),State) ==> holds(clear(X),do(putdown(X,Y),State))) /\
   (!Z W X Y State. holds(on(X,Y),State) ==> holds(on(X,Y),do(putdown(Z,W),State))) /\
   (!X State Z Y. holds(clear(Z),State) /\ differ(Z,Y) ==> holds(clear(Z),do(putdown(X,Y),State))) /\
   (!Y X. differ(Y,X) ==> differ(X,Y)) /\
   (differ(a,b)) /\
   (differ(a,c)) /\
   (differ(a,d)) /\
   (differ(a,table)) /\
   (differ(b,c)) /\
   (differ(b,d)) /\
   (differ(b,table)) /\
   (differ(c,d)) /\
   (differ(c,table)) /\
   (differ(d,table)) /\
   (holds(on(a,table),s0)) /\
   (holds(on(b,table),s0)) /\
   (holds(on(c,d),s0)) /\
   (holds(on(d,table),s0)) /\
   (holds(clear(a),s0)) /\
   (holds(clear(b),s0)) /\
   (holds(clear(c),s0)) /\
   (holds(empty,s0)) /\
   (!State. holds(clear(table),State)) /\
   (!State. ~holds(and'(on(a,c),on(c,d)),State)) ==> F`;


val PRV001_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Y Z. q1(X,Y,Z) /\ less_or_equal(X,Y) ==> q2(X,Y,Z)) /\
 (!X Y Z. q1(X,Y,Z) ==> less_or_equal(X,Y) \/ q3(X,Y,Z)) /\
 (!Z X Y. q2(X,Y,Z) ==> q4(X,Y,Y)) /\
 (!Z Y X. q3(X,Y,Z) ==> q4(X,Y,X)) /\
 (!X. less_or_equal(X,X)) /\
 (!X Y. less_or_equal(X,Y) /\ less_or_equal(Y,X) ==> equal(X,Y)) /\
 (!Y X Z. less_or_equal(X,Y) /\ less_or_equal(Y,Z) ==> less_or_equal(X,Z)) /\
 (!Y X. less_or_equal(X,Y) \/ less_or_equal(Y,X)) /\
 (!X Y. equal(X,Y) ==> less_or_equal(X,Y)) /\
 (!X Y Z. equal(X,Y) /\ less_or_equal(X,Z) ==> less_or_equal(Y,Z)) /\
 (!X Z Y. equal(X,Y) /\ less_or_equal(Z,X) ==> less_or_equal(Z,Y)) /\
 (q1(a,b,c)) /\
 (!W. ~(q4(a,b,W) /\ less_or_equal(a,W) /\ less_or_equal(b,W) /\ less_or_equal(W,a))) /\
 (!W. ~(q4(a,b,W) /\ less_or_equal(a,W) /\ less_or_equal(b,W) /\
       less_or_equal(W,b))) 
  ==> F`;
  

val PRV003_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(predecessor(successor(X)),X)) /\
   (!X. equal(successor(predecessor(X)),X)) /\
   (!X Y. equal(predecessor(X),predecessor(Y)) ==> equal(X,Y)) /\
   (!X Y. equal(successor(X),successor(Y)) ==> equal(X,Y)) /\
   (!X. less_than(predecessor(X),X)) /\
   (!X. less_than(X,successor(X))) /\
   (!X Y Z. less_than(X,Y) /\ less_than(Y,Z) ==> less_than(X,Z)) /\
   (!X Y. less_than(X,Y) \/ less_than(Y,X) \/ equal(X,Y)) /\
   (!X. ~less_than(X,X)) /\
   (!Y X. ~(less_than(X,Y) /\ less_than(Y,X))) /\
   (!Y X Z. equal(X,Y) /\ less_than(X,Z) ==> less_than(Y,Z)) /\
   (!Y Z X. equal(X,Y) /\ less_than(Z,X) ==> less_than(Z,Y)) /\
   (!X Y. equal(X,Y) ==> equal(predecessor(X),predecessor(Y))) /\
   (!X Y. equal(X,Y) ==> equal(successor(X),successor(Y))) /\
   (!X Y. equal(X,Y) ==> equal(a(X),a(Y))) /\
   (~less_than(n,j)) /\
   (less_than(k,j)) /\
   (~less_than(k,i)) /\
   (less_than(i,n)) /\
   (less_than(a(j),a(k))) /\
   (!X. less_than(X,j) /\ less_than(a(X),a(k)) ==> less_than(X,i)) /\
   (!X. less_than(one,i) /\ less_than(a(X),a(predecessor(i))) ==> less_than(X,i) \/ less_than(n,X)) /\
   (!X. ~(less_than(one,X) /\ less_than(X,i) /\ less_than(a(X),a(predecessor(X))))) /\
   (less_than(j,i)) ==> F`--);
  

val PRV005_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(predecessor(successor(X)),X)) /\
   (!X. equal(successor(predecessor(X)),X)) /\
   (!X Y. equal(predecessor(X),predecessor(Y)) ==> equal(X,Y)) /\
   (!X Y. equal(successor(X),successor(Y)) ==> equal(X,Y)) /\
   (!X. less_than(predecessor(X),X)) /\
   (!X. less_than(X,successor(X))) /\
   (!X Y Z. less_than(X,Y) /\ less_than(Y,Z) ==> less_than(X,Z)) /\
   (!X Y. less_than(X,Y) \/ less_than(Y,X) \/ equal(X,Y)) /\
   (!X. ~less_than(X,X)) /\
   (!Y X. ~(less_than(X,Y) /\ less_than(Y,X))) /\
   (!Y X Z. equal(X,Y) /\ less_than(X,Z) ==> less_than(Y,Z)) /\
   (!Y Z X. equal(X,Y) /\ less_than(Z,X) ==> less_than(Z,Y)) /\
   (!X Y. equal(X,Y) ==> equal(predecessor(X),predecessor(Y))) /\
   (!X Y. equal(X,Y) ==> equal(successor(X),successor(Y))) /\
   (!X Y. equal(X,Y) ==> equal(a(X),a(Y))) /\
   (~less_than(n,k)) /\
   (~less_than(k,l)) /\
   (~less_than(k,i)) /\
   (less_than(l,n)) /\
   (less_than(one,l)) /\
   (less_than(a(k),a(predecessor(l)))) /\
   (!X. less_than(X,successor(n)) /\ less_than(a(X),a(k)) ==> less_than(X,l)) /\
   (!X. less_than(one,l) /\ less_than(a(X),a(predecessor(l))) ==> less_than(X,l) \/ less_than(n,X)) /\
   (!X. ~(less_than(one,X) /\ less_than(X,l) /\ less_than(a(X),a(predecessor(X))))) ==> F`--);
  

val PRV006_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(predecessor(successor(X)),X)) /\
   (!X. equal(successor(predecessor(X)),X)) /\
   (!X Y. equal(predecessor(X),predecessor(Y)) ==> equal(X,Y)) /\
   (!X Y. equal(successor(X),successor(Y)) ==> equal(X,Y)) /\
   (!X. less_than(predecessor(X),X)) /\
   (!X. less_than(X,successor(X))) /\
   (!X Y Z. less_than(X,Y) /\ less_than(Y,Z) ==> less_than(X,Z)) /\
   (!X Y. less_than(X,Y) \/ less_than(Y,X) \/ equal(X,Y)) /\
   (!X. ~less_than(X,X)) /\
   (!Y X. ~(less_than(X,Y) /\ less_than(Y,X))) /\
   (!Y X Z. equal(X,Y) /\ less_than(X,Z) ==> less_than(Y,Z)) /\
   (!Y Z X. equal(X,Y) /\ less_than(Z,X) ==> less_than(Z,Y)) /\
   (!X Y. equal(X,Y) ==> equal(predecessor(X),predecessor(Y))) /\
   (!X Y. equal(X,Y) ==> equal(successor(X),successor(Y))) /\
   (!X Y. equal(X,Y) ==> equal(a(X),a(Y))) /\
   (~less_than(n,m)) /\
   (less_than(i,m)) /\
   (less_than(i,n)) /\
   (~less_than(i,one)) /\
   (less_than(a(i),a(m))) /\
   (!X. less_than(X,successor(n)) /\ less_than(a(X),a(m)) ==> less_than(X,i)) /\
   (!X. less_than(one,i) /\ less_than(a(X),a(predecessor(i))) ==> less_than(X,i) \/ less_than(n,X)) /\
   (!X. ~(less_than(one,X) /\ less_than(X,i) /\ less_than(a(X),a(predecessor(X))))) ==> F`--);
  

val PRV009_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Y X. less_or_equal(X,Y) \/ less(Y,X)) /\
   (less(j,i)) /\
   (less_or_equal(m,p)) /\
   (less_or_equal(p,q)) /\
   (less_or_equal(q,n)) /\
   (!X Y. less_or_equal(m,X) /\ less(X,i) /\ less(j,Y) /\ less_or_equal(Y,n) ==> less_or_equal(a(X),a(Y))) /\
   (!X Y. less_or_equal(m,X) /\ less_or_equal(X,Y) /\ less_or_equal(Y,j) ==> less_or_equal(a(X),a(Y))) /\
   (!X Y. less_or_equal(i,X) /\ less_or_equal(X,Y) /\ less_or_equal(Y,n) ==> less_or_equal(a(X),a(Y))) /\
   (~less_or_equal(a(p),a(q))) ==> F`;
  

val PUZ012_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X. equal_fruits(X,X)) /\
   (!X. equal_boxes(X,X)) /\
   (!X Y. ~(label(X,Y) /\ contains(X,Y))) /\
   (!X. contains(boxa,X) \/ contains(boxb,X) \/ contains(boxc,X)) /\
   (!X. contains(X,apples) \/ contains(X,bananas) \/ contains(X,oranges)) /\
   (!X Y Z. contains(X,Y) /\ contains(X,Z) ==> equal_fruits(Y,Z)) /\
   (!Y X Z. contains(X,Y) /\ contains(Z,Y) ==> equal_boxes(X,Z)) /\
   (~equal_boxes(boxa,boxb)) /\
   (~equal_boxes(boxb,boxc)) /\
   (~equal_boxes(boxa,boxc)) /\
   (~equal_fruits(apples,bananas)) /\
   (~equal_fruits(bananas,oranges)) /\
   (~equal_fruits(apples,oranges)) /\
   (label(boxa,apples)) /\
   (label(boxb,oranges)) /\
   (label(boxc,bananas)) /\
   (contains(boxb,apples)) /\
   (~(contains(boxa,bananas) /\ contains(boxc,oranges))) ==> F`;
  

val PUZ020_1 = 
Term`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!A B. equal(A,B) ==> equal(statement_by(A),statement_by(B))) /\
   (!X. person(X) ==> knight(X) \/ knave(X)) /\
   (!X. ~(person(X) /\ knight(X) /\ knave(X))) /\
   (!X Y. says(X,Y) /\ a_truth(Y) ==> a_truth(Y)) /\
   (!X Y. ~(says(X,Y) /\ equal(X,Y))) /\
   (!Y X. says(X,Y) ==> equal(Y,statement_by(X))) /\
   (!X Y. ~(person(X) /\ equal(X,statement_by(Y)))) /\
   (!X. person(X) /\ a_truth(statement_by(X)) ==> knight(X)) /\
   (!X. person(X) ==> a_truth(statement_by(X)) \/ knave(X)) /\
   (!X Y. equal(X,Y) /\ knight(X) ==> knight(Y)) /\
   (!X Y. equal(X,Y) /\ knave(X) ==> knave(Y)) /\
   (!X Y. equal(X,Y) /\ person(X) ==> person(Y)) /\
   (!X Y Z. equal(X,Y) /\ says(X,Z) ==> says(Y,Z)) /\
   (!X Z Y. equal(X,Y) /\ says(Z,X) ==> says(Z,Y)) /\
   (!X Y. equal(X,Y) /\ a_truth(X) ==> a_truth(Y)) /\
   (!X Y. knight(X) /\ says(X,Y) ==> a_truth(Y)) /\
   (!X Y. ~(knave(X) /\ says(X,Y) /\ a_truth(Y))) /\
   (person(husband)) /\
   (person(wife)) /\
   (~equal(husband,wife)) /\
   (says(husband,statement_by(husband))) /\
   (a_truth(statement_by(husband)) /\ knight(husband) ==> knight(wife)) /\
   (knight(husband) ==> a_truth(statement_by(husband))) /\
   (a_truth(statement_by(husband)) \/ knight(wife)) /\
   (knight(wife) ==> a_truth(statement_by(husband))) /\
   (~knight(husband)) ==> F`;


val PUZ025_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X. a_truth(truthteller(X)) \/ a_truth(liar(X))) /\
   (!X. ~(a_truth(truthteller(X)) /\ a_truth(liar(X)))) /\
   (!Truthteller Statement. a_truth(truthteller(Truthteller)) /\ a_truth(says(Truthteller,Statement)) ==> a_truth(Statement)) /\
   (!Liar Statement. ~(a_truth(liar(Liar)) /\ a_truth(says(Liar,Statement)) /\ a_truth(Statement))) /\
   (!Statement Truthteller. a_truth(Statement) /\ a_truth(says(Truthteller,Statement)) ==> a_truth(truthteller(Truthteller))) /\
   (!Statement Liar. a_truth(says(Liar,Statement)) ==> a_truth(Statement) \/ a_truth(liar(Liar))) /\
   (!Z X Y. people(X,Y,Z) /\ a_truth(liar(X)) /\ a_truth(liar(Y)) ==> a_truth(equal_type(X,Y))) /\
   (!Z X Y. people(X,Y,Z) /\ a_truth(truthteller(X)) /\ a_truth(truthteller(Y)) ==> a_truth(equal_type(X,Y))) /\
   (!X Y. a_truth(equal_type(X,Y)) /\ a_truth(truthteller(X)) ==> a_truth(truthteller(Y))) /\
   (!X Y. a_truth(equal_type(X,Y)) /\ a_truth(liar(X)) ==> a_truth(liar(Y))) /\
   (!X Y. a_truth(truthteller(X)) ==> a_truth(equal_type(X,Y)) \/ a_truth(liar(Y))) /\
   (!X Y. a_truth(liar(X)) ==> a_truth(equal_type(X,Y)) \/ a_truth(truthteller(Y))) /\
   (!Y X. a_truth(equal_type(X,Y)) ==> a_truth(equal_type(Y,X))) /\
   (!X Y. ask_1_if_2(X,Y) /\ a_truth(truthteller(X)) /\ a_truth(Y) ==> answer(yes)) /\
   (!X Y. ask_1_if_2(X,Y) /\ a_truth(truthteller(X)) ==> a_truth(Y) \/ answer(no)) /\
   (!X Y. ask_1_if_2(X,Y) /\ a_truth(liar(X)) /\ a_truth(Y) ==> answer(no)) /\
   (!X Y. ask_1_if_2(X,Y) /\ a_truth(liar(X)) ==> a_truth(Y) \/ answer(yes)) /\
   (people(b,c,a)) /\
   (people(a,b,a)) /\
   (people(a,c,b)) /\
   (people(c,b,a)) /\
   (a_truth(says(a,equal_type(b,c)))) /\
   (ask_1_if_2(c,equal_type(a,b))) /\
   (!Answer. ~answer(Answer)) ==> F`;


val PUZ029_1 = 
 (--`(!X:'a. dances_on_tightropes(X) \/ eats_pennybuns(X) \/ old(X)) /\
   (!X. pig(X) /\ liable_to_giddiness(X) ==> treated_with_respect(X)) /\
   (!X. wise(X) /\ balloonist(X) ==> has_umbrella(X)) /\
   (!X. ~(looks_ridiculous(X) /\ eats_pennybuns(X) /\ eats_lunch_in_public(X))) /\
   (!X. balloonist(X) /\ young(X) ==> liable_to_giddiness(X)) /\
   (!X. fat(X) /\ looks_ridiculous(X) ==> dances_on_tightropes(X) \/ eats_lunch_in_public(X)) /\
   (!X. ~(liable_to_giddiness(X) /\ wise(X) /\ dances_on_tightropes(X))) /\
   (!X. pig(X) /\ has_umbrella(X) ==> looks_ridiculous(X)) /\
   (!X. treated_with_respect(X) ==> dances_on_tightropes(X) \/ fat(X)) /\
   (!X. young(X) \/ old(X)) /\
   (!X. ~(young(X) /\ old(X))) /\
   (wise(piggy)) /\
   (young(piggy)) /\
   (pig(piggy)) /\
   (balloonist(piggy)) ==> F`--);
  

val RNG001_3 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X. sum(additive_identity,X,X)) /\
   (!X. sum(additive_inverse(X),X,additive_identity)) /\
   (!Y U Z X V W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(U,Z,W) ==> sum(X,V,W)) /\
   (!Y X V U Z W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(X,V,W) ==> sum(U,Z,W)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!Y Z X V3 V1 V2 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ product(X,V3,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(X,V3,V4)) /\
   (~product(a,additive_identity,additive_identity)) ==> F`;
  

val RNG001_5 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. sum(additive_identity,X,X)) /\
   (!X. sum(X,additive_identity,X)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y. sum(X,Y,add(X,Y))) /\
   (!X. sum(additive_inverse(X),X,additive_identity)) /\
   (!X. sum(X,additive_inverse(X),additive_identity)) /\
   (!Y U Z X V W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(U,Z,W) ==> sum(X,V,W)) /\
   (!Y X V U Z W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(X,V,W) ==> sum(U,Z,W)) /\
   (!Y X Z. sum(X,Y,Z) ==> sum(Y,X,Z)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!Y Z X V3 V1 V2 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ product(X,V3,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(X,V3,V4)) /\
   (!Y Z V3 X V1 V2 V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ product(V3,X,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 V3 X V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(V3,X,V4)) /\
   (!X Y U V. sum(X,Y,U) /\ sum(X,Y,V) ==> equal(U,V)) /\
   (!X Y U V. product(X,Y,U) /\ product(X,Y,V) ==> equal(U,V)) /\
   (!X Y. equal(X,Y) ==> equal(additive_inverse(X),additive_inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(add(X,W),add(Y,W))) /\
   (!X Y W Z. equal(X,Y) /\ sum(X,W,Z) ==> sum(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ sum(W,X,Z) ==> sum(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ sum(W,Z,X) ==> sum(W,Z,Y)) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (~product(a,additive_identity,additive_identity)) ==> F`--);
  

val RNG011_5 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!A B C. equal(A,B) ==> equal(add(A,C),add(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(add(F',D),add(F',E))) /\
   (!G H. equal(G,H) ==> equal(additive_inverse(G),additive_inverse(H))) /\
   (!I' J K'. equal(I',J) ==> equal(multiply(I',K'),multiply(J,K'))) /\
   (!L N M. equal(L,M) ==> equal(multiply(N,L),multiply(N,M))) /\
   (!A B C D. equal(A,B) ==> equal(associator(A,C,D),associator(B,C,D))) /\
   (!E G F' H. equal(E,F') ==> equal(associator(G,E,H),associator(G,F',H))) /\
   (!I' K' L J. equal(I',J) ==> equal(associator(K',L,I'),associator(K',L,J))) /\
   (!M N O. equal(M,N) ==> equal(commutator(M,O),commutator(N,O))) /\
   (!P R Q. equal(P,Q) ==> equal(commutator(R,P),commutator(R,Q))) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(add(X,Y),Z),add(X,add(Y,Z)))) /\
   (!X. equal(add(X,additive_identity),X)) /\
   (!X. equal(add(additive_identity,X),X)) /\
   (!X. equal(add(X,additive_inverse(X)),additive_identity)) /\
   (!X. equal(add(additive_inverse(X),X),additive_identity)) /\
   (equal(additive_inverse(additive_identity),additive_identity)) /\
   (!X Y. equal(add(X,add(additive_inverse(X),Y)),Y)) /\
   (!X Y. equal(additive_inverse(add(X,Y)),add(additive_inverse(X),additive_inverse(Y)))) /\
   (!X. equal(additive_inverse(additive_inverse(X)),X)) /\
   (!X. equal(multiply(X,additive_identity),additive_identity)) /\
   (!X. equal(multiply(additive_identity,X),additive_identity)) /\
   (!X Y. equal(multiply(additive_inverse(X),additive_inverse(Y)),multiply(X,Y))) /\
   (!X Y. equal(multiply(X,additive_inverse(Y)),additive_inverse(multiply(X,Y)))) /\
   (!X Y. equal(multiply(additive_inverse(X),Y),additive_inverse(multiply(X,Y)))) /\
   (!Y X Z. equal(multiply(X,add(Y,Z)),add(multiply(X,Y),multiply(X,Z)))) /\
   (!X Y Z. equal(multiply(add(X,Y),Z),add(multiply(X,Z),multiply(Y,Z)))) /\
   (!X Y. equal(multiply(multiply(X,Y),Y),multiply(X,multiply(Y,Y)))) /\
   (!X Y Z. equal(associator(X,Y,Z),add(multiply(multiply(X,Y),Z),additive_inverse(multiply(X,multiply(Y,Z)))))) /\
   (!X Y. equal(commutator(X,Y),add(multiply(Y,X),additive_inverse(multiply(X,Y))))) /\
   (!X Y. equal(multiply(multiply(associator(X,X,Y),X),associator(X,X,Y)),additive_identity)) /\
   (~equal(multiply(multiply(associator(a,a,b),a),associator(a,a,b)),additive_identity)) ==> F`--);
  

val RNG023_6 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(X,add(Y,Z)),add(add(X,Y),Z))) /\
   (!X. equal(add(additive_identity,X),X)) /\
   (!X. equal(add(X,additive_identity),X)) /\
   (!X. equal(multiply(additive_identity,X),additive_identity)) /\
   (!X. equal(multiply(X,additive_identity),additive_identity)) /\
   (!X. equal(add(additive_inverse(X),X),additive_identity)) /\
   (!X. equal(add(X,additive_inverse(X)),additive_identity)) /\
   (!Y X Z. equal(multiply(X,add(Y,Z)),add(multiply(X,Y),multiply(X,Z)))) /\
   (!X Y Z. equal(multiply(add(X,Y),Z),add(multiply(X,Z),multiply(Y,Z)))) /\
   (!X. equal(additive_inverse(additive_inverse(X)),X)) /\
   (!X Y. equal(multiply(multiply(X,Y),Y),multiply(X,multiply(Y,Y)))) /\
   (!X Y. equal(multiply(multiply(X,X),Y),multiply(X,multiply(X,Y)))) /\
   (!X Y Z. equal(associator(X,Y,Z),add(multiply(multiply(X,Y),Z),additive_inverse(multiply(X,multiply(Y,Z)))))) /\
   (!X Y. equal(commutator(X,Y),add(multiply(Y,X),additive_inverse(multiply(X,Y))))) /\
   (!D E F'. equal(D,E) ==> equal(add(D,F'),add(E,F'))) /\
   (!G I' H. equal(G,H) ==> equal(add(I',G),add(I',H))) /\
   (!J K'. equal(J,K') ==> equal(additive_inverse(J),additive_inverse(K'))) /\
   (!L M N O. equal(L,M) ==> equal(associator(L,N,O),associator(M,N,O))) /\
   (!P R Q S'. equal(P,Q) ==> equal(associator(R,P,S'),associator(R,Q,S'))) /\
   (!T' V W U. equal(T',U) ==> equal(associator(V,W,T'),associator(V,W,U))) /\
   (!X Y Z. equal(X,Y) ==> equal(commutator(X,Z),commutator(Y,Z))) /\
   (!A1 C1 B1. equal(A1,B1) ==> equal(commutator(C1,A1),commutator(C1,B1))) /\
   (!D1 E1 F1. equal(D1,E1) ==> equal(multiply(D1,F1),multiply(E1,F1))) /\
   (!G1 I1 H1. equal(G1,H1) ==> equal(multiply(I1,G1),multiply(I1,H1))) /\
   (~equal(associator(x,x,y),additive_identity)) ==> F`--);
  

val RNG028_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. equal(add(additive_identity,X),X)) /\
   (!X. equal(multiply(additive_identity,X),additive_identity)) /\
   (!X. equal(multiply(X,additive_identity),additive_identity)) /\
   (!X. equal(add(additive_inverse(X),X),additive_identity)) /\
   (!X Y. equal(additive_inverse(add(X,Y)),add(additive_inverse(X),additive_inverse(Y)))) /\
   (!X. equal(additive_inverse(additive_inverse(X)),X)) /\
   (!Y X Z. equal(multiply(X,add(Y,Z)),add(multiply(X,Y),multiply(X,Z)))) /\
   (!X Y Z. equal(multiply(add(X,Y),Z),add(multiply(X,Z),multiply(Y,Z)))) /\
   (!X Y. equal(multiply(multiply(X,Y),Y),multiply(X,multiply(Y,Y)))) /\
   (!X Y. equal(multiply(multiply(X,X),Y),multiply(X,multiply(X,Y)))) /\
   (!X Y. equal(multiply(additive_inverse(X),Y),additive_inverse(multiply(X,Y)))) /\
   (!X Y. equal(multiply(X,additive_inverse(Y)),additive_inverse(multiply(X,Y)))) /\
   (equal(additive_inverse(additive_identity),additive_identity)) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(X,add(Y,Z)),add(add(X,Y),Z))) /\
   (!Z X Y. equal(add(X,Z),add(Y,Z)) ==> equal(X,Y)) /\
   (!Z X Y. equal(add(Z,X),add(Z,Y)) ==> equal(X,Y)) /\
   (!D E F'. equal(D,E) ==> equal(add(D,F'),add(E,F'))) /\
   (!G I' H. equal(G,H) ==> equal(add(I',G),add(I',H))) /\
   (!J K'. equal(J,K') ==> equal(additive_inverse(J),additive_inverse(K'))) /\
   (!D1 E1 F1. equal(D1,E1) ==> equal(multiply(D1,F1),multiply(E1,F1))) /\
   (!G1 I1 H1. equal(G1,H1) ==> equal(multiply(I1,G1),multiply(I1,H1))) /\
   (!X Y Z. equal(associator(X,Y,Z),add(multiply(multiply(X,Y),Z),additive_inverse(multiply(X,multiply(Y,Z)))))) /\
   (!L M N O. equal(L,M) ==> equal(associator(L,N,O),associator(M,N,O))) /\
   (!P R Q S'. equal(P,Q) ==> equal(associator(R,P,S'),associator(R,Q,S'))) /\
   (!T' V W U. equal(T',U) ==> equal(associator(V,W,T'),associator(V,W,U))) /\
   (!X Y. ~equal(multiply(multiply(Y,X),Y),multiply(Y,multiply(X,Y)))) /\
   (!X Y Z. ~equal(associator(Y,X,Z),additive_inverse(associator(X,Y,Z)))) /\
   (!X Y Z. ~equal(associator(Z,Y,X),additive_inverse(associator(X,Y,Z)))) /\
   (~equal(multiply(multiply(cx,multiply(cy,cx)),cz),multiply(cx,multiply(cy,multiply(cx,cz))))) ==> F`--);
  

val RNG038_2 = 
 Term
`(!X:'a. sum(X,additive_identity,X)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y. sum(X,Y,add(X,Y))) /\
   (!X. sum(X,additive_inverse(X),additive_identity)) /\
   (!Y U Z X V W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(U,Z,W) ==> sum(X,V,W)) /\
   (!Y X V U Z W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(X,V,W) ==> sum(U,Z,W)) /\
   (!Y X Z. sum(X,Y,Z) ==> sum(Y,X,Z)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!Y Z X V3 V1 V2 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ product(X,V3,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(X,V3,V4)) /\
   (!Y Z V3 X V1 V2 V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ product(V3,X,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 V3 X V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(V3,X,V4)) /\
   (!X Y U V. sum(X,Y,U) /\ sum(X,Y,V) ==> equal(U,V)) /\
   (!X Y U V. product(X,Y,U) /\ product(X,Y,V) ==> equal(U,V)) /\
   (!X Y. equal(X,Y) ==> equal(additive_inverse(X),additive_inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(add(X,W),add(Y,W))) /\
   (!X Y W Z. equal(X,Y) /\ sum(X,W,Z) ==> sum(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ sum(W,X,Z) ==> sum(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ sum(W,Z,X) ==> sum(W,Z,Y)) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!X. product(additive_identity,X,additive_identity)) /\
   (!X. product(X,additive_identity,additive_identity)) /\
   (!X Y. equal(X,additive_identity) ==> product(X,h(X,Y),Y)) /\
   (product(a,b,additive_identity)) /\
   (~equal(a,additive_identity)) /\
   (~equal(b,additive_identity)) ==> F`;
  

val RNG040_2 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X Y. equal(X,Y) ==> equal(additive_inverse(X),additive_inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(add(X,W),add(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(add(W,X),add(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ sum(X,W,Z) ==> sum(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ sum(W,X,Z) ==> sum(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ sum(W,Z,X) ==> sum(W,Z,Y)) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!X. sum(additive_identity,X,X)) /\
   (!X. sum(X,additive_identity,X)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y. sum(X,Y,add(X,Y))) /\
   (!X. sum(additive_inverse(X),X,additive_identity)) /\
   (!X. sum(X,additive_inverse(X),additive_identity)) /\
   (!Y U Z X V W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(U,Z,W) ==> sum(X,V,W)) /\
   (!Y X V U Z W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(X,V,W) ==> sum(U,Z,W)) /\
   (!Y X Z. sum(X,Y,Z) ==> sum(Y,X,Z)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!Y Z X V3 V1 V2 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ product(X,V3,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(X,V3,V4)) /\
   (!X Y U V. sum(X,Y,U) /\ sum(X,Y,V) ==> equal(U,V)) /\
   (!X Y U V. product(X,Y,U) /\ product(X,Y,V) ==> equal(U,V)) /\
   (!A. product(A,multiplicative_identity,A)) /\
   (!A. product(multiplicative_identity,A,A)) /\
   (!A. product(A,h(A),multiplicative_identity) \/ equal(A,additive_identity)) /\
   (!A. product(h(A),A,multiplicative_identity) \/ equal(A,additive_identity)) /\
   (!B A C. product(A,B,C) ==> product(B,A,C)) /\
   (!A B. equal(A,B) ==> equal(h(A),h(B))) /\
   (sum(b,c,d)) /\
   (product(d,a,additive_identity)) /\
   (product(b,a,l)) /\
   (product(c,a,n)) /\
   (~sum(l,n,additive_identity)) ==> F`--);
  

val RNG041_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!X. sum(additive_identity,X,X)) /\
   (!X. sum(X,additive_identity,X)) /\
   (!X Y. product(X,Y,multiply(X,Y))) /\
   (!X Y. sum(X,Y,add(X,Y))) /\
   (!X. sum(additive_inverse(X),X,additive_identity)) /\
   (!X. sum(X,additive_inverse(X),additive_identity)) /\
   (!Y U Z X V W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(U,Z,W) ==> sum(X,V,W)) /\
   (!Y X V U Z W. sum(X,Y,U) /\ sum(Y,Z,V) /\ sum(X,V,W) ==> sum(U,Z,W)) /\
   (!Y X Z. sum(X,Y,Z) ==> sum(Y,X,Z)) /\
   (!Y U Z X V W. product(X,Y,U) /\ product(Y,Z,V) /\ product(U,Z,W) ==> product(X,V,W)) /\
   (!Y X V U Z W. product(X,Y,U) /\ product(Y,Z,V) /\ product(X,V,W) ==> product(U,Z,W)) /\
   (!Y Z X V3 V1 V2 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ product(X,V3,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 X V3 V4. product(X,Y,V1) /\ product(X,Z,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(X,V3,V4)) /\
   (!Y Z V3 X V1 V2 V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ product(V3,X,V4) ==> sum(V1,V2,V4)) /\
   (!Y Z V1 V2 V3 X V4. product(Y,X,V1) /\ product(Z,X,V2) /\ sum(Y,Z,V3) /\ sum(V1,V2,V4) ==> product(V3,X,V4)) /\
   (!X Y U V. sum(X,Y,U) /\ sum(X,Y,V) ==> equal(U,V)) /\
   (!X Y U V. product(X,Y,U) /\ product(X,Y,V) ==> equal(U,V)) /\
   (!X Y. equal(X,Y) ==> equal(additive_inverse(X),additive_inverse(Y))) /\
   (!X Y W. equal(X,Y) ==> equal(add(X,W),add(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(add(W,X),add(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ sum(X,W,Z) ==> sum(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ sum(W,X,Z) ==> sum(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ sum(W,Z,X) ==> sum(W,Z,Y)) /\
   (!X Y W. equal(X,Y) ==> equal(multiply(X,W),multiply(Y,W))) /\
   (!X W Y. equal(X,Y) ==> equal(multiply(W,X),multiply(W,Y))) /\
   (!X Y W Z. equal(X,Y) /\ product(X,W,Z) ==> product(Y,W,Z)) /\
   (!X W Y Z. equal(X,Y) /\ product(W,X,Z) ==> product(W,Y,Z)) /\
   (!X W Z Y. equal(X,Y) /\ product(W,Z,X) ==> product(W,Z,Y)) /\
   (!A B. equal(A,B) ==> equal(h(A),h(B))) /\
   (!A. product(additive_identity,A,additive_identity)) /\
   (!A. product(A,additive_identity,additive_identity)) /\
   (!A. product(A,multiplicative_identity,A)) /\
   (!A. product(multiplicative_identity,A,A)) /\
   (!A. product(A,h(A),multiplicative_identity) \/ equal(A,additive_identity)) /\
   (!A. product(h(A),A,multiplicative_identity) \/ equal(A,additive_identity)) /\
   (product(a,b,additive_identity)) /\
   (~equal(a,additive_identity)) /\
   (~equal(b,additive_identity)) ==> F`--);
  

val ROB010_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(add(X,Y),Z),add(X,add(Y,Z)))) /\
   (!Y X. equal(negate(add(negate(add(X,Y)),negate(add(X,negate(Y))))),X)) /\
   (!A B C. equal(A,B) ==> equal(add(A,C),add(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(add(F',D),add(F',E))) /\
   (!G H. equal(G,H) ==> equal(negate(G),negate(H))) /\
   (equal(negate(add(a,negate(b))),c)) /\
   (~equal(negate(add(c,negate(add(b,a)))),a)) ==> F`--);
  

val ROB013_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(add(X,Y),Z),add(X,add(Y,Z)))) /\
   (!Y X. equal(negate(add(negate(add(X,Y)),negate(add(X,negate(Y))))),X)) /\
   (!A B C. equal(A,B) ==> equal(add(A,C),add(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(add(F',D),add(F',E))) /\
   (!G H. equal(G,H) ==> equal(negate(G),negate(H))) /\
   (equal(negate(add(a,b)),c)) /\
   (~equal(negate(add(c,negate(add(negate(b),a)))),a)) ==> F`--);
  

val ROB016_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(add(X,Y),Z),add(X,add(Y,Z)))) /\
   (!Y X. equal(negate(add(negate(add(X,Y)),negate(add(X,negate(Y))))),X)) /\
   (!A B C. equal(A,B) ==> equal(add(A,C),add(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(add(F',D),add(F',E))) /\
   (!G H. equal(G,H) ==> equal(negate(G),negate(H))) /\
   (!J K' L. equal(J,K') ==> equal(multiply(J,L),multiply(K',L))) /\
   (!M O N. equal(M,N) ==> equal(multiply(O,M),multiply(O,N))) /\
   (!P Q. equal(P,Q) ==> equal(successor(P),successor(Q))) /\
   (!R S'. equal(R,S') /\ positive_integer(R) ==> positive_integer(S')) /\
   (!X. equal(multiply(one,X),X)) /\
   (!V X. positive_integer(X) ==> equal(multiply(successor(V),X),add(X,multiply(V,X)))) /\
   (positive_integer(one)) /\
   (!X. positive_integer(X) ==> positive_integer(successor(X))) /\
   (equal(negate(add(d,e)),negate(e))) /\
   (positive_integer(k)) /\
   (!Vk X Y. equal(negate(add(negate(Y),negate(add(X,negate(Y))))),X) /\ positive_integer(Vk) ==> equal(negate(add(Y,multiply(Vk,add(X,negate(add(X,negate(Y))))))),negate(Y))) /\
   (~equal(negate(add(e,multiply(k,add(d,negate(add(d,negate(e))))))),negate(e))) ==> F`--);
  

val ROB021_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. equal(add(X,Y),add(Y,X))) /\
   (!X Y Z. equal(add(add(X,Y),Z),add(X,add(Y,Z)))) /\
   (!Y X. equal(negate(add(negate(add(X,Y)),negate(add(X,negate(Y))))),X)) /\
   (!A B C. equal(A,B) ==> equal(add(A,C),add(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(add(F',D),add(F',E))) /\
   (!G H. equal(G,H) ==> equal(negate(G),negate(H))) /\
   (!X Y. equal(negate(X),negate(Y)) ==> equal(X,Y)) /\
   (~equal(add(negate(add(a,negate(b))),negate(add(negate(a),negate(b)))),b)) ==> F`--);
  

val SET005_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Subset Element Superset. member(Element,Subset) /\ subset(Subset,Superset) ==> member(Element,Superset)) /\
   (!Superset Subset. subset(Subset,Superset) \/ member(member_of_1_not_of_2(Subset,Superset),Subset)) /\
   (!Subset Superset. member(member_of_1_not_of_2(Subset,Superset),Superset) ==> subset(Subset,Superset)) /\
   (!Subset Superset. equal_sets(Subset,Superset) ==> subset(Subset,Superset)) /\
   (!Subset Superset. equal_sets(Superset,Subset) ==> subset(Subset,Superset)) /\
   (!Set2 Set1. subset(Set1,Set2) /\ subset(Set2,Set1) ==> equal_sets(Set2,Set1)) /\
   (!Set2 Intersection Element Set1. intersection(Set1,Set2,Intersection) /\ member(Element,Intersection) ==> member(Element,Set1)) /\
   (!Set1 Intersection Element Set2. intersection(Set1,Set2,Intersection) /\ member(Element,Intersection) ==> member(Element,Set2)) /\
   (!Set2 Set1 Element Intersection. intersection(Set1,Set2,Intersection) /\ member(Element,Set2) /\ member(Element,Set1) ==> member(Element,Intersection)) /\
   (!Set2 Intersection Set1. member(h(Set1,Set2,Intersection),Intersection) \/ intersection(Set1,Set2,Intersection) \/ member(h(Set1,Set2,Intersection),Set1)) /\
   (!Set1 Intersection Set2. member(h(Set1,Set2,Intersection),Intersection) \/ intersection(Set1,Set2,Intersection) \/ member(h(Set1,Set2,Intersection),Set2)) /\
   (!Set1 Set2 Intersection. member(h(Set1,Set2,Intersection),Intersection) /\ member(h(Set1,Set2,Intersection),Set2) /\ member(h(Set1,Set2,Intersection),Set1) ==> intersection(Set1,Set2,Intersection)) /\
   (intersection(a,b,aIb)) /\
   (intersection(b,c,bIc)) /\
   (intersection(a,bIc,aIbIc)) /\
   (~intersection(aIb,c,aIbIc)) ==> F`;
  

val SET009_1 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Subset Element Superset. member(Element,Subset) /\ subset(Subset,Superset) ==> member(Element,Superset)) /\
   (!Superset Subset. subset(Subset,Superset) \/ member(member_of_1_not_of_2(Subset,Superset),Subset)) /\
   (!Subset Superset. member(member_of_1_not_of_2(Subset,Superset),Superset) ==> subset(Subset,Superset)) /\
   (!Subset Superset. equal_sets(Subset,Superset) ==> subset(Subset,Superset)) /\
   (!Subset Superset. equal_sets(Superset,Subset) ==> subset(Subset,Superset)) /\
   (!Set2 Set1. subset(Set1,Set2) /\ subset(Set2,Set1) ==> equal_sets(Set2,Set1)) /\
   (!Set2 Difference Element Set1. difference(Set1,Set2,Difference) /\ member(Element,Difference) ==> member(Element,Set1)) /\
   (!Element A_set Set1 Set2. ~(member(Element,Set1) /\ member(Element,Set2) /\ difference(A_set,Set1,Set2))) /\
   (!Set1 Difference Element Set2. member(Element,Set1) /\ difference(Set1,Set2,Difference) ==> member(Element,Difference) \/ member(Element,Set2)) /\
   (!Set1 Set2 Difference. difference(Set1,Set2,Difference) \/ member(k(Set1,Set2,Difference),Set1) \/ member(k(Set1,Set2,Difference),Difference)) /\
   (!Set1 Set2 Difference. member(k(Set1,Set2,Difference),Set2) ==> member(k(Set1,Set2,Difference),Difference) \/ difference(Set1,Set2,Difference)) /\
   (!Set1 Set2 Difference. member(k(Set1,Set2,Difference),Difference) /\ member(k(Set1,Set2,Difference),Set1) ==> member(k(Set1,Set2,Difference),Set2) \/ difference(Set1,Set2,Difference)) /\
   (subset(d,a)) /\
   (difference(b,a,bDa)) /\
   (difference(b,d,bDd)) /\
   (~subset(bDa,bDd)) ==> F`;
  

val SET025_4 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (!Y X. member(X,Y) ==> little_set(X)) /\
   (!X Y. little_set(f1(X,Y)) \/ equal(X,Y)) /\
   (!X Y. member(f1(X,Y),X) \/ member(f1(X,Y),Y) \/ equal(X,Y)) /\
   (!X Y. member(f1(X,Y),X) /\ member(f1(X,Y),Y) ==> equal(X,Y)) /\
   (!X U Y. member(U,non_ordered_pair(X,Y)) ==> equal(U,X) \/ equal(U,Y)) /\
   (!Y U X. little_set(U) /\ equal(U,X) ==> member(U,non_ordered_pair(X,Y))) /\
   (!X U Y. little_set(U) /\ equal(U,Y) ==> member(U,non_ordered_pair(X,Y))) /\
   (!X Y. little_set(non_ordered_pair(X,Y))) /\
   (!X. equal(singleton_set(X),non_ordered_pair(X,X))) /\
   (!X Y. equal(ordered_pair(X,Y),non_ordered_pair(singleton_set(X),non_ordered_pair(X,Y)))) /\
   (!X. ordered_pair_predicate(X) ==> little_set(f2(X))) /\
   (!X. ordered_pair_predicate(X) ==> little_set(f3(X))) /\
   (!X. ordered_pair_predicate(X) ==> equal(X,ordered_pair(f2(X),f3(X)))) /\
   (!X Y Z. little_set(Y) /\ little_set(Z) /\ equal(X,ordered_pair(Y,Z)) ==> ordered_pair_predicate(X)) /\
   (!Z X. member(Z,first(X)) ==> little_set(f4(Z,X))) /\
   (!Z X. member(Z,first(X)) ==> little_set(f5(Z,X))) /\
   (!Z X. member(Z,first(X)) ==> equal(X,ordered_pair(f4(Z,X),f5(Z,X)))) /\
   (!Z X. member(Z,first(X)) ==> member(Z,f4(Z,X))) /\
   (!X V Z U. little_set(U) /\ little_set(V) /\ equal(X,ordered_pair(U,V)) /\ member(Z,U) ==> member(Z,first(X))) /\
   (!Z X. member(Z,second(X)) ==> little_set(f6(Z,X))) /\
   (!Z X. member(Z,second(X)) ==> little_set(f7(Z,X))) /\
   (!Z X. member(Z,second(X)) ==> equal(X,ordered_pair(f6(Z,X),f7(Z,X)))) /\
   (!Z X. member(Z,second(X)) ==> member(Z,f7(Z,X))) /\
   (!X U Z V. little_set(U) /\ little_set(V) /\ equal(X,ordered_pair(U,V)) /\ member(Z,V) ==> member(Z,second(X))) /\
   (!Z. member(Z,estin) ==> ordered_pair_predicate(Z)) /\
   (!Z. member(Z,estin) ==> member(first(Z),second(Z))) /\
   (!Z. little_set(Z) /\ ordered_pair_predicate(Z) /\ member(first(Z),second(Z)) ==> member(Z,estin)) /\
   (!Y Z X. member(Z,intersection(X,Y)) ==> member(Z,X)) /\
   (!X Z Y. member(Z,intersection(X,Y)) ==> member(Z,Y)) /\
   (!X Z Y. member(Z,X) /\ member(Z,Y) ==> member(Z,intersection(X,Y))) /\
   (!Z X. ~(member(Z,complement(X)) /\ member(Z,X))) /\
   (!Z X. little_set(Z) ==> member(Z,complement(X)) \/ member(Z,X)) /\
   (!X Y. equal(union(X,Y),complement(intersection(complement(X),complement(Y))))) /\
   (!Z X. member(Z,domain_of(X)) ==> ordered_pair_predicate(f8(Z,X))) /\
   (!Z X. member(Z,domain_of(X)) ==> member(f8(Z,X),X)) /\
   (!Z X. member(Z,domain_of(X)) ==> equal(Z,first(f8(Z,X)))) /\
   (!X Z Xp. little_set(Z) /\ ordered_pair_predicate(Xp) /\ member(Xp,X) /\ equal(Z,first(Xp)) ==> member(Z,domain_of(X))) /\
   (!X Y Z. member(Z,cross_product(X,Y)) ==> ordered_pair_predicate(Z)) /\
   (!Y Z X. member(Z,cross_product(X,Y)) ==> member(first(Z),X)) /\
   (!X Z Y. member(Z,cross_product(X,Y)) ==> member(second(Z),Y)) /\
   (!X Z Y. little_set(Z) /\ ordered_pair_predicate(Z) /\ member(first(Z),X) /\ member(second(Z),Y) ==> member(Z,cross_product(X,Y))) /\
   (!X Z. member(Z,converse(X)) ==> ordered_pair_predicate(Z)) /\
   (!Z X. member(Z,converse(X)) ==> member(ordered_pair(second(Z),first(Z)),X)) /\
   (!Z X. little_set(Z) /\ ordered_pair_predicate(Z) /\ member(ordered_pair(second(Z),first(Z)),X) ==> member(Z,converse(X))) /\
   (!Z X. member(Z,rotate_right(X)) ==> little_set(f9(Z,X))) /\
   (!Z X. member(Z,rotate_right(X)) ==> little_set(f10(Z,X))) /\
   (!Z X. member(Z,rotate_right(X)) ==> little_set(f11(Z,X))) /\
   (!Z X. member(Z,rotate_right(X)) ==> equal(Z,ordered_pair(f9(Z,X),ordered_pair(f10(Z,X),f11(Z,X))))) /\
   (!Z X. member(Z,rotate_right(X)) ==> member(ordered_pair(f10(Z,X),ordered_pair(f11(Z,X),f9(Z,X))),X)) /\
   (!Z V W U X. little_set(Z) /\ little_set(U) /\ little_set(V) /\ little_set(W) /\ equal(Z,ordered_pair(U,ordered_pair(V,W))) /\ member(ordered_pair(V,ordered_pair(W,U)),X) ==> member(Z,rotate_right(X))) /\
   (!Z X. member(Z,flip_range_of(X)) ==> little_set(f12(Z,X))) /\
   (!Z X. member(Z,flip_range_of(X)) ==> little_set(f13(Z,X))) /\
   (!Z X. member(Z,flip_range_of(X)) ==> little_set(f14(Z,X))) /\
   (!Z X. member(Z,flip_range_of(X)) ==> equal(Z,ordered_pair(f12(Z,X),ordered_pair(f13(Z,X),f14(Z,X))))) /\
   (!Z X. member(Z,flip_range_of(X)) ==> member(ordered_pair(f12(Z,X),ordered_pair(f14(Z,X),f13(Z,X))),X)) /\
   (!Z U W V X. little_set(Z) /\ little_set(U) /\ little_set(V) /\ little_set(W) /\ equal(Z,ordered_pair(U,ordered_pair(V,W))) /\ member(ordered_pair(U,ordered_pair(W,V)),X) ==> member(Z,flip_range_of(X))) /\
   (!X. equal(successor(X),union(X,singleton_set(X)))) /\
   (!Z. ~member(Z,empty_set)) /\
   (!Z. little_set(Z) ==> member(Z,universal_set)) /\
   (little_set(infinity)) /\
   (member(empty_set,infinity)) /\
   (!X. member(X,infinity) ==> member(successor(X),infinity)) /\
   (!Z X. member(Z,sigma(X)) ==> member(f16(Z,X),X)) /\
   (!Z X. member(Z,sigma(X)) ==> member(Z,f16(Z,X))) /\
   (!X Z Y. member(Y,X) /\ member(Z,Y) ==> member(Z,sigma(X))) /\
   (!U. little_set(U) ==> little_set(sigma(U))) /\
   (!X U Y. subset(X,Y) /\ member(U,X) ==> member(U,Y)) /\
   (!Y X. subset(X,Y) \/ member(f17(X,Y),X)) /\
   (!X Y. member(f17(X,Y),Y) ==> subset(X,Y)) /\
   (!X Y. proper_subset(X,Y) ==> subset(X,Y)) /\
   (!X Y. ~(proper_subset(X,Y) /\ equal(X,Y))) /\
   (!X Y. subset(X,Y) ==> proper_subset(X,Y) \/ equal(X,Y)) /\
   (!Z X. member(Z,powerset(X)) ==> subset(Z,X)) /\
   (!Z X. little_set(Z) /\ subset(Z,X) ==> member(Z,powerset(X))) /\
   (!U. little_set(U) ==> little_set(powerset(U))) /\
   (!Z X. relation(Z) /\ member(X,Z) ==> ordered_pair_predicate(X)) /\
   (!Z. relation(Z) \/ member(f18(Z),Z)) /\
   (!Z. ordered_pair_predicate(f18(Z)) ==> relation(Z)) /\
   (!U X V W. single_valued_set(X) /\ little_set(U) /\ little_set(V) /\ little_set(W) /\ member(ordered_pair(U,V),X) /\ member(ordered_pair(U,W),X) ==> equal(V,W)) /\
   (!X. single_valued_set(X) \/ little_set(f19(X))) /\
   (!X. single_valued_set(X) \/ little_set(f20(X))) /\
   (!X. single_valued_set(X) \/ little_set(f21(X))) /\
   (!X. single_valued_set(X) \/ member(ordered_pair(f19(X),f20(X)),X)) /\
   (!X. single_valued_set(X) \/ member(ordered_pair(f19(X),f21(X)),X)) /\
   (!X. equal(f20(X),f21(X)) ==> single_valued_set(X)) /\
   (!Xf. function(Xf) ==> relation(Xf)) /\
   (!Xf. function(Xf) ==> single_valued_set(Xf)) /\
   (!Xf. relation(Xf) /\ single_valued_set(Xf) ==> function(Xf)) /\
   (!Z X Xf. member(Z,image(X,Xf)) ==> ordered_pair_predicate(f22(Z,X,Xf))) /\
   (!Z X Xf. member(Z,image(X,Xf)) ==> member(f22(Z,X,Xf),Xf)) /\
   (!Z Xf X. member(Z,image(X,Xf)) ==> member(first(f22(Z,X,Xf)),X)) /\
   (!X Xf Z. member(Z,image(X,Xf)) ==> equal(second(f22(Z,X,Xf)),Z)) /\
   (!Xf X Y Z. little_set(Z) /\ ordered_pair_predicate(Y) /\ member(Y,Xf) /\ member(first(Y),X) /\ equal(second(Y),Z) ==> member(Z,image(X,Xf))) /\
   (!X Xf. little_set(X) /\ function(Xf) ==> little_set(image(X,Xf))) /\
   (!X U Y. ~(disjoint(X,Y) /\ member(U,X) /\ member(U,Y))) /\
   (!Y X. disjoint(X,Y) \/ member(f23(X,Y),X)) /\
   (!X Y. disjoint(X,Y) \/ member(f23(X,Y),Y)) /\
   (!X. equal(X,empty_set) \/ member(f24(X),X)) /\
   (!X. equal(X,empty_set) \/ disjoint(f24(X),X)) /\
   (function(f25)) /\
   (!X. little_set(X) ==> equal(X,empty_set) \/ member(f26(X),X)) /\
   (!X. little_set(X) ==> equal(X,empty_set) \/ member(ordered_pair(X,f26(X)),f25)) /\
   (!Z X. member(Z,range_of(X)) ==> ordered_pair_predicate(f27(Z,X))) /\
   (!Z X. member(Z,range_of(X)) ==> member(f27(Z,X),X)) /\
   (!Z X. member(Z,range_of(X)) ==> equal(Z,second(f27(Z,X)))) /\
   (!X Z Xp. little_set(Z) /\ ordered_pair_predicate(Xp) /\ member(Xp,X) /\ equal(Z,second(Xp)) ==> member(Z,range_of(X))) /\
   (!Z. member(Z,identity_relation) ==> ordered_pair_predicate(Z)) /\
   (!Z. member(Z,identity_relation) ==> equal(first(Z),second(Z))) /\
   (!Z. little_set(Z) /\ ordered_pair_predicate(Z) /\ equal(first(Z),second(Z)) ==> member(Z,identity_relation)) /\
   (!X Y. equal(restrict(X,Y),intersection(X,cross_product(Y,universal_set)))) /\
   (!Xf. one_to_one_function(Xf) ==> function(Xf)) /\
   (!Xf. one_to_one_function(Xf) ==> function(converse(Xf))) /\
   (!Xf. function(Xf) /\ function(converse(Xf)) ==> one_to_one_function(Xf)) /\
   (!Z Xf Y. member(Z,apply(Xf,Y)) ==> ordered_pair_predicate(f28(Z,Xf,Y))) /\
   (!Z Y Xf. member(Z,apply(Xf,Y)) ==> member(f28(Z,Xf,Y),Xf)) /\
   (!Z Xf Y. member(Z,apply(Xf,Y)) ==> equal(first(f28(Z,Xf,Y)),Y)) /\
   (!Z Xf Y. member(Z,apply(Xf,Y)) ==> member(Z,second(f28(Z,Xf,Y)))) /\
   (!Xf Y Z W. ordered_pair_predicate(W) /\ member(W,Xf) /\ equal(first(W),Y) /\ member(Z,second(W)) ==> member(Z,apply(Xf,Y))) /\
   (!Xf X Y. equal(apply_to_two_arguments(Xf,X,Y),apply(Xf,ordered_pair(X,Y)))) /\
   (!X Y Xf. maps(Xf,X,Y) ==> function(Xf)) /\
   (!Y Xf X. maps(Xf,X,Y) ==> equal(domain_of(Xf),X)) /\
   (!X Xf Y. maps(Xf,X,Y) ==> subset(range_of(Xf),Y)) /\
   (!X Xf Y. function(Xf) /\ equal(domain_of(Xf),X) /\ subset(range_of(Xf),Y) ==> maps(Xf,X,Y)) /\
   (!Xf Xs. closed(Xs,Xf) ==> little_set(Xs)) /\
   (!Xs Xf. closed(Xs,Xf) ==> little_set(Xf)) /\
   (!Xf Xs. closed(Xs,Xf) ==> maps(Xf,cross_product(Xs,Xs),Xs)) /\
   (!Xf Xs. little_set(Xs) /\ little_set(Xf) /\ maps(Xf,cross_product(Xs,Xs),Xs) ==> closed(Xs,Xf)) /\
   (!Z Xf Xg. member(Z,composition(Xf,Xg)) ==> little_set(f29(Z,Xf,Xg))) /\
   (!Z Xf Xg. member(Z,composition(Xf,Xg)) ==> little_set(f30(Z,Xf,Xg))) /\
   (!Z Xf Xg. member(Z,composition(Xf,Xg)) ==> little_set(f31(Z,Xf,Xg))) /\
   (!Z Xf Xg. member(Z,composition(Xf,Xg)) ==> equal(Z,ordered_pair(f29(Z,Xf,Xg),f30(Z,Xf,Xg)))) /\
   (!Z Xg Xf. member(Z,composition(Xf,Xg)) ==> member(ordered_pair(f29(Z,Xf,Xg),f31(Z,Xf,Xg)),Xf)) /\
   (!Z Xf Xg. member(Z,composition(Xf,Xg)) ==> member(ordered_pair(f31(Z,Xf,Xg),f30(Z,Xf,Xg)),Xg)) /\
   (!Z X Xf W Y Xg. little_set(Z) /\ little_set(X) /\ little_set(Y) /\ little_set(W) /\ equal(Z,ordered_pair(X,Y)) /\ member(ordered_pair(X,W),Xf) /\ member(ordered_pair(W,Y),Xg) ==> member(Z,composition(Xf,Xg))) /\
   (!Xh Xs2 Xf2 Xs1 Xf1. homomorphism(Xh,Xs1,Xf1,Xs2,Xf2) ==> closed(Xs1,Xf1)) /\
   (!Xh Xs1 Xf1 Xs2 Xf2. homomorphism(Xh,Xs1,Xf1,Xs2,Xf2) ==> closed(Xs2,Xf2)) /\
   (!Xf1 Xf2 Xh Xs1 Xs2. homomorphism(Xh,Xs1,Xf1,Xs2,Xf2) ==> maps(Xh,Xs1,Xs2)) /\
   (!Xs2 Xs1 Xf1 Xf2 X Xh Y. homomorphism(Xh,Xs1,Xf1,Xs2,Xf2) /\ member(X,Xs1) /\ member(Y,Xs1) ==> equal(apply(Xh,apply_to_two_arguments(Xf1,X,Y)),apply_to_two_arguments(Xf2,apply(Xh,X),apply(Xh,Y)))) /\
   (!Xh Xf1 Xs2 Xf2 Xs1. closed(Xs1,Xf1) /\ closed(Xs2,Xf2) /\ maps(Xh,Xs1,Xs2) ==> homomorphism(Xh,Xs1,Xf1,Xs2,Xf2) \/ member(f32(Xh,Xs1,Xf1,Xs2,Xf2),Xs1)) /\
   (!Xh Xf1 Xs2 Xf2 Xs1. closed(Xs1,Xf1) /\ closed(Xs2,Xf2) /\ maps(Xh,Xs1,Xs2) ==> homomorphism(Xh,Xs1,Xf1,Xs2,Xf2) \/ member(f33(Xh,Xs1,Xf1,Xs2,Xf2),Xs1)) /\
   (!Xh Xs1 Xf1 Xs2 Xf2. closed(Xs1,Xf1) /\ closed(Xs2,Xf2) /\ maps(Xh,Xs1,Xs2) /\ equal(apply(Xh,apply_to_two_arguments(Xf1,f32(Xh,Xs1,Xf1,Xs2,Xf2),f33(Xh,Xs1,Xf1,Xs2,Xf2))),apply_to_two_arguments(Xf2,apply(Xh,f32(Xh,Xs1,Xf1,Xs2,Xf2)),apply(Xh,f33(Xh,Xs1,Xf1,Xs2,Xf2)))) ==> homomorphism(Xh,Xs1,Xf1,Xs2,Xf2)) /\
   (!A B C. equal(A,B) ==> equal(f1(A,C),f1(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(f1(F',D),f1(F',E))) /\
   (!A2 B2. equal(A2,B2) ==> equal(f2(A2),f2(B2))) /\
   (!G4 H4. equal(G4,H4) ==> equal(f3(G4),f3(H4))) /\
   (!O7 P7 Q7. equal(O7,P7) ==> equal(f4(O7,Q7),f4(P7,Q7))) /\
   (!R7 T7 S7. equal(R7,S7) ==> equal(f4(T7,R7),f4(T7,S7))) /\
   (!U7 V7 W7. equal(U7,V7) ==> equal(f5(U7,W7),f5(V7,W7))) /\
   (!X7 Z7 Y7. equal(X7,Y7) ==> equal(f5(Z7,X7),f5(Z7,Y7))) /\
   (!A8 B8 C8. equal(A8,B8) ==> equal(f6(A8,C8),f6(B8,C8))) /\
   (!D8 F8 E8. equal(D8,E8) ==> equal(f6(F8,D8),f6(F8,E8))) /\
   (!G8 H8 I8. equal(G8,H8) ==> equal(f7(G8,I8),f7(H8,I8))) /\
   (!J8 L8 K8. equal(J8,K8) ==> equal(f7(L8,J8),f7(L8,K8))) /\
   (!M8 N8 O8. equal(M8,N8) ==> equal(f8(M8,O8),f8(N8,O8))) /\
   (!P8 R8 Q8. equal(P8,Q8) ==> equal(f8(R8,P8),f8(R8,Q8))) /\
   (!S8 T8 U8. equal(S8,T8) ==> equal(f9(S8,U8),f9(T8,U8))) /\
   (!V8 X8 W8. equal(V8,W8) ==> equal(f9(X8,V8),f9(X8,W8))) /\
   (!G H I'. equal(G,H) ==> equal(f10(G,I'),f10(H,I'))) /\
   (!J L K'. equal(J,K') ==> equal(f10(L,J),f10(L,K'))) /\
   (!M N O. equal(M,N) ==> equal(f11(M,O),f11(N,O))) /\
   (!P R Q. equal(P,Q) ==> equal(f11(R,P),f11(R,Q))) /\
   (!S' T' U. equal(S',T') ==> equal(f12(S',U),f12(T',U))) /\
   (!V X W. equal(V,W) ==> equal(f12(X,V),f12(X,W))) /\
   (!Y Z A1. equal(Y,Z) ==> equal(f13(Y,A1),f13(Z,A1))) /\
   (!B1 D1 C1. equal(B1,C1) ==> equal(f13(D1,B1),f13(D1,C1))) /\
   (!E1 F1 G1. equal(E1,F1) ==> equal(f14(E1,G1),f14(F1,G1))) /\
   (!H1 J1 I1. equal(H1,I1) ==> equal(f14(J1,H1),f14(J1,I1))) /\
   (!K1 L1 M1. equal(K1,L1) ==> equal(f16(K1,M1),f16(L1,M1))) /\
   (!N1 P1 O1. equal(N1,O1) ==> equal(f16(P1,N1),f16(P1,O1))) /\
   (!Q1 R1 S1. equal(Q1,R1) ==> equal(f17(Q1,S1),f17(R1,S1))) /\
   (!T1 V1 U1. equal(T1,U1) ==> equal(f17(V1,T1),f17(V1,U1))) /\
   (!W1 X1. equal(W1,X1) ==> equal(f18(W1),f18(X1))) /\
   (!Y1 Z1. equal(Y1,Z1) ==> equal(f19(Y1),f19(Z1))) /\
   (!C2 D2. equal(C2,D2) ==> equal(f20(C2),f20(D2))) /\
   (!E2 F2. equal(E2,F2) ==> equal(f21(E2),f21(F2))) /\
   (!G2 H2 I2 J2. equal(G2,H2) ==> equal(f22(G2,I2,J2),f22(H2,I2,J2))) /\
   (!K2 M2 L2 N2. equal(K2,L2) ==> equal(f22(M2,K2,N2),f22(M2,L2,N2))) /\
   (!O2 Q2 R2 P2. equal(O2,P2) ==> equal(f22(Q2,R2,O2),f22(Q2,R2,P2))) /\
   (!S2 T2 U2. equal(S2,T2) ==> equal(f23(S2,U2),f23(T2,U2))) /\
   (!V2 X2 W2. equal(V2,W2) ==> equal(f23(X2,V2),f23(X2,W2))) /\
   (!Y2 Z2. equal(Y2,Z2) ==> equal(f24(Y2),f24(Z2))) /\
   (!A3 B3. equal(A3,B3) ==> equal(f26(A3),f26(B3))) /\
   (!C3 D3 E3. equal(C3,D3) ==> equal(f27(C3,E3),f27(D3,E3))) /\
   (!F3 H3 G3. equal(F3,G3) ==> equal(f27(H3,F3),f27(H3,G3))) /\
   (!I3 J3 K3 L3. equal(I3,J3) ==> equal(f28(I3,K3,L3),f28(J3,K3,L3))) /\
   (!M3 O3 N3 P3. equal(M3,N3) ==> equal(f28(O3,M3,P3),f28(O3,N3,P3))) /\
   (!Q3 S3 T3 R3. equal(Q3,R3) ==> equal(f28(S3,T3,Q3),f28(S3,T3,R3))) /\
   (!U3 V3 W3 X3. equal(U3,V3) ==> equal(f29(U3,W3,X3),f29(V3,W3,X3))) /\
   (!Y3 A4 Z3 B4. equal(Y3,Z3) ==> equal(f29(A4,Y3,B4),f29(A4,Z3,B4))) /\
   (!C4 E4 F4 D4. equal(C4,D4) ==> equal(f29(E4,F4,C4),f29(E4,F4,D4))) /\
   (!I4 J4 K4 L4. equal(I4,J4) ==> equal(f30(I4,K4,L4),f30(J4,K4,L4))) /\
   (!M4 O4 N4 P4. equal(M4,N4) ==> equal(f30(O4,M4,P4),f30(O4,N4,P4))) /\
   (!Q4 S4 T4 R4. equal(Q4,R4) ==> equal(f30(S4,T4,Q4),f30(S4,T4,R4))) /\
   (!U4 V4 W4 X4. equal(U4,V4) ==> equal(f31(U4,W4,X4),f31(V4,W4,X4))) /\
   (!Y4 A5 Z4 B5. equal(Y4,Z4) ==> equal(f31(A5,Y4,B5),f31(A5,Z4,B5))) /\
   (!C5 E5 F5 D5. equal(C5,D5) ==> equal(f31(E5,F5,C5),f31(E5,F5,D5))) /\
   (!G5 H5 I5 J5 K5 L5. equal(G5,H5) ==> equal(f32(G5,I5,J5,K5,L5),f32(H5,I5,J5,K5,L5))) /\
   (!M5 O5 N5 P5 Q5 R5. equal(M5,N5) ==> equal(f32(O5,M5,P5,Q5,R5),f32(O5,N5,P5,Q5,R5))) /\
   (!S5 U5 V5 T5 W5 X5. equal(S5,T5) ==> equal(f32(U5,V5,S5,W5,X5),f32(U5,V5,T5,W5,X5))) /\
   (!Y5 A6 B6 C6 Z5 D6. equal(Y5,Z5) ==> equal(f32(A6,B6,C6,Y5,D6),f32(A6,B6,C6,Z5,D6))) /\
   (!E6 G6 H6 I6 J6 F6. equal(E6,F6) ==> equal(f32(G6,H6,I6,J6,E6),f32(G6,H6,I6,J6,F6))) /\
   (!K6 L6 M6 N6 O6 P6. equal(K6,L6) ==> equal(f33(K6,M6,N6,O6,P6),f33(L6,M6,N6,O6,P6))) /\
   (!Q6 S6 R6 T6 U6 V6. equal(Q6,R6) ==> equal(f33(S6,Q6,T6,U6,V6),f33(S6,R6,T6,U6,V6))) /\
   (!W6 Y6 Z6 X6 A7 B7. equal(W6,X6) ==> equal(f33(Y6,Z6,W6,A7,B7),f33(Y6,Z6,X6,A7,B7))) /\
   (!C7 E7 F7 G7 D7 H7. equal(C7,D7) ==> equal(f33(E7,F7,G7,C7,H7),f33(E7,F7,G7,D7,H7))) /\
   (!I7 K7 L7 M7 N7 J7. equal(I7,J7) ==> equal(f33(K7,L7,M7,N7,I7),f33(K7,L7,M7,N7,J7))) /\
   (!A B C. equal(A,B) ==> equal(apply(A,C),apply(B,C))) /\
   (!D F' E. equal(D,E) ==> equal(apply(F',D),apply(F',E))) /\
   (!G H I' J. equal(G,H) ==> equal(apply_to_two_arguments(G,I',J),apply_to_two_arguments(H,I',J))) /\
   (!K' M L N. equal(K',L) ==> equal(apply_to_two_arguments(M,K',N),apply_to_two_arguments(M,L,N))) /\
   (!O Q R P. equal(O,P) ==> equal(apply_to_two_arguments(Q,R,O),apply_to_two_arguments(Q,R,P))) /\
   (!S' T'. equal(S',T') ==> equal(complement(S'),complement(T'))) /\
   (!U V W. equal(U,V) ==> equal(composition(U,W),composition(V,W))) /\
   (!X Z Y. equal(X,Y) ==> equal(composition(Z,X),composition(Z,Y))) /\
   (!A1 B1. equal(A1,B1) ==> equal(converse(A1),converse(B1))) /\
   (!C1 D1 E1. equal(C1,D1) ==> equal(cross_product(C1,E1),cross_product(D1,E1))) /\
   (!F1 H1 G1. equal(F1,G1) ==> equal(cross_product(H1,F1),cross_product(H1,G1))) /\
   (!I1 J1. equal(I1,J1) ==> equal(domain_of(I1),domain_of(J1))) /\
   (!I10 J10. equal(I10,J10) ==> equal(first(I10),first(J10))) /\
   (!Q10 R10. equal(Q10,R10) ==> equal(flip_range_of(Q10),flip_range_of(R10))) /\
   (!S10 T10 U10. equal(S10,T10) ==> equal(image(S10,U10),image(T10,U10))) /\
   (!V10 X10 W10. equal(V10,W10) ==> equal(image(X10,V10),image(X10,W10))) /\
   (!Y10 Z10 A11. equal(Y10,Z10) ==> equal(intersection(Y10,A11),intersection(Z10,A11))) /\
   (!B11 D11 C11. equal(B11,C11) ==> equal(intersection(D11,B11),intersection(D11,C11))) /\
   (!E11 F11 G11. equal(E11,F11) ==> equal(non_ordered_pair(E11,G11),non_ordered_pair(F11,G11))) /\
   (!H11 J11 I11. equal(H11,I11) ==> equal(non_ordered_pair(J11,H11),non_ordered_pair(J11,I11))) /\
   (!K11 L11 M11. equal(K11,L11) ==> equal(ordered_pair(K11,M11),ordered_pair(L11,M11))) /\
   (!N11 P11 O11. equal(N11,O11) ==> equal(ordered_pair(P11,N11),ordered_pair(P11,O11))) /\
   (!Q11 R11. equal(Q11,R11) ==> equal(powerset(Q11),powerset(R11))) /\
   (!S11 T11. equal(S11,T11) ==> equal(range_of(S11),range_of(T11))) /\
   (!U11 V11 W11. equal(U11,V11) ==> equal(restrict(U11,W11),restrict(V11,W11))) /\
   (!X11 Z11 Y11. equal(X11,Y11) ==> equal(restrict(Z11,X11),restrict(Z11,Y11))) /\
   (!A12 B12. equal(A12,B12) ==> equal(rotate_right(A12),rotate_right(B12))) /\
   (!C12 D12. equal(C12,D12) ==> equal(second(C12),second(D12))) /\
   (!K12 L12. equal(K12,L12) ==> equal(sigma(K12),sigma(L12))) /\
   (!M12 N12. equal(M12,N12) ==> equal(singleton_set(M12),singleton_set(N12))) /\
   (!O12 P12. equal(O12,P12) ==> equal(successor(O12),successor(P12))) /\
   (!Q12 R12 S12. equal(Q12,R12) ==> equal(union(Q12,S12),union(R12,S12))) /\
   (!T12 V12 U12. equal(T12,U12) ==> equal(union(V12,T12),union(V12,U12))) /\
   (!W12 X12 Y12. equal(W12,X12) /\ closed(W12,Y12) ==> closed(X12,Y12)) /\
   (!Z12 B13 A13. equal(Z12,A13) /\ closed(B13,Z12) ==> closed(B13,A13)) /\
   (!C13 D13 E13. equal(C13,D13) /\ disjoint(C13,E13) ==> disjoint(D13,E13)) /\
   (!F13 H13 G13. equal(F13,G13) /\ disjoint(H13,F13) ==> disjoint(H13,G13)) /\
   (!I13 J13. equal(I13,J13) /\ function(I13) ==> function(J13)) /\
   (!K13 L13 M13 N13 O13 P13. equal(K13,L13) /\ homomorphism(K13,M13,N13,O13,P13) ==> homomorphism(L13,M13,N13,O13,P13)) /\
   (!Q13 S13 R13 T13 U13 V13. equal(Q13,R13) /\ homomorphism(S13,Q13,T13,U13,V13) ==> homomorphism(S13,R13,T13,U13,V13)) /\
   (!W13 Y13 Z13 X13 A14 B14. equal(W13,X13) /\ homomorphism(Y13,Z13,W13,A14,B14) ==> homomorphism(Y13,Z13,X13,A14,B14)) /\
   (!C14 E14 F14 G14 D14 H14. equal(C14,D14) /\ homomorphism(E14,F14,G14,C14,H14) ==> homomorphism(E14,F14,G14,D14,H14)) /\
   (!I14 K14 L14 M14 N14 J14. equal(I14,J14) /\ homomorphism(K14,L14,M14,N14,I14) ==> homomorphism(K14,L14,M14,N14,J14)) /\
   (!O14 P14. equal(O14,P14) /\ little_set(O14) ==> little_set(P14)) /\
   (!Q14 R14 S14 T14. equal(Q14,R14) /\ maps(Q14,S14,T14) ==> maps(R14,S14,T14)) /\
   (!U14 W14 V14 X14. equal(U14,V14) /\ maps(W14,U14,X14) ==> maps(W14,V14,X14)) /\
   (!Y14 A15 B15 Z14. equal(Y14,Z14) /\ maps(A15,B15,Y14) ==> maps(A15,B15,Z14)) /\
   (!C15 D15 E15. equal(C15,D15) /\ member(C15,E15) ==> member(D15,E15)) /\
   (!F15 H15 G15. equal(F15,G15) /\ member(H15,F15) ==> member(H15,G15)) /\
   (!I15 J15. equal(I15,J15) /\ one_to_one_function(I15) ==> one_to_one_function(J15)) /\
   (!K15 L15. equal(K15,L15) /\ ordered_pair_predicate(K15) ==> ordered_pair_predicate(L15)) /\
   (!M15 N15 O15. equal(M15,N15) /\ proper_subset(M15,O15) ==> proper_subset(N15,O15)) /\
   (!P15 R15 Q15. equal(P15,Q15) /\ proper_subset(R15,P15) ==> proper_subset(R15,Q15)) /\
   (!S15 T15. equal(S15,T15) /\ relation(S15) ==> relation(T15)) /\
   (!U15 V15. equal(U15,V15) /\ single_valued_set(U15) ==> single_valued_set(V15)) /\
   (!W15 X15 Y15. equal(W15,X15) /\ subset(W15,Y15) ==> subset(X15,Y15)) /\
   (!Z15 B16 A16. equal(Z15,A16) /\ subset(B16,Z15) ==> subset(B16,A16)) /\
   (~little_set(ordered_pair(a,b))) ==> F`--);
  

val SET046_5 = 
 Term
`(!Y X. ~(element(X,a) /\ element(X,Y) /\ element(Y,X))) /\
   (!X:'a. element(X,f(X)) \/ element(X,a)) /\
   (!X. element(f(X),X) \/ element(X,a)) ==> F`;
  

val SET047_5 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!X Z Y. set_equal(X,Y) /\ element(Z,X) ==> element(Z,Y)) /\
   (!Y Z X. set_equal(X,Y) /\ element(Z,Y) ==> element(Z,X)) /\
   (!X Y. element(f(X,Y),X) \/ element(f(X,Y),Y) \/ set_equal(X,Y)) /\
   (!X Y. element(f(X,Y),Y) /\ element(f(X,Y),X) ==> set_equal(X,Y)) /\
   (set_equal(a,b) \/ set_equal(b,a)) /\
   (~(set_equal(b,a) /\ set_equal(a,b))) ==> F`;
  

val SYN034_1 = 
 (--`(!A:'a. p(A,a) \/ p(A,f(A))) /\
   (!A. p(A,a) \/ p(f(A),A)) /\
   (!A B. ~(p(A,B) /\ p(B,A) /\ p(B,a))) ==> F`--);
  

val SYN071_1 = 
 (--`(!X:'a. equal(X,X)) /\
   (!Y X. equal(X,Y) ==> equal(Y,X)) /\
   (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
   (equal(a,b) \/ equal(c,d)) /\
   (equal(a,c) \/ equal(b,d)) /\
   (~equal(a,d)) /\
   (~equal(b,c)) ==> F`--);
  

val SYN349_1 = 
 (--`(!X Y. f(w(X),g(X,Y)) ==> f(X,g(X,Y))) /\
   (!X Y:'a. f(X,g(X,Y)) ==> f(w(X),g(X,Y))) /\
   (!Y X. f(X,g(X,Y)) /\ f(Y,g(X,Y)) ==> f(g(X,Y),Y) \/ f(g(X,Y),w(X))) /\
   (!Y X. f(g(X,Y),Y) /\ f(Y,g(X,Y)) ==> f(X,g(X,Y)) \/ f(g(X,Y),w(X))) /\
   (!Y X. f(X,g(X,Y)) \/ f(g(X,Y),Y) \/ f(Y,g(X,Y)) \/ f(g(X,Y),w(X))) /\
   (!Y X. f(X,g(X,Y)) /\ f(g(X,Y),Y) ==> f(Y,g(X,Y)) \/ f(g(X,Y),w(X))) /\
   (!Y X. f(X,g(X,Y)) /\ f(g(X,Y),w(X)) ==> f(g(X,Y),Y) \/ f(Y,g(X,Y))) /\
   (!Y X. f(g(X,Y),Y) /\ f(g(X,Y),w(X)) ==> f(X,g(X,Y)) \/ f(Y,g(X,Y))) /\
   (!Y X. f(Y,g(X,Y)) /\ f(g(X,Y),w(X)) ==> f(X,g(X,Y)) \/ f(g(X,Y),Y)) /\
   (!Y X. ~(f(X,g(X,Y)) /\ f(g(X,Y),Y) /\ f(Y,g(X,Y)) /\ f(g(X,Y),w(X)))) ==> F`--);
  

val SYN352_1 = 
 (--`(f(a,b)) /\
   (!X Y:'a. f(X,Y) ==> f(b,z(X,Y)) \/ f(Y,z(X,Y))) /\
   (!X Y. f(X,Y) \/ f(z(X,Y),z(X,Y))) /\
   (!X Y. f(b,z(X,Y)) \/ f(X,z(X,Y)) \/ f(z(X,Y),z(X,Y))) /\
   (!X Y. f(b,z(X,Y)) /\ f(X,z(X,Y)) ==> f(z(X,Y),z(X,Y))) /\
   (!X Y. ~(f(X,Y) /\ f(X,z(X,Y)) /\ f(Y,z(X,Y)))) /\
   (!X Y. f(X,Y) ==> f(X,z(X,Y)) \/ f(Y,z(X,Y))) ==> F`--);
  

val TOP001_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Vf U. element_of_set(U,union_of_members(Vf)) ==> element_of_set(U,f1(Vf,U))) /\
   (!U Vf. element_of_set(U,union_of_members(Vf)) ==> element_of_collection(f1(Vf,U),Vf)) /\
   (!U Uu1 Vf. element_of_set(U,Uu1) /\ element_of_collection(Uu1,Vf) ==> element_of_set(U,union_of_members(Vf))) /\
   (!Vf X. basis(X,Vf) ==> equal_sets(union_of_members(Vf),X)) /\
   (!Vf U X. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_set(X,f10(Vf,U,X))) /\
   (!U X Vf. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_collection(f10(Vf,U,X),Vf)) /\
   (!X. subset_sets(X,X)) /\
   (!X U Y. subset_sets(X,Y) /\ element_of_set(U,X) ==> element_of_set(U,Y)) /\
   (!X Y. equal_sets(X,Y) ==> subset_sets(X,Y)) /\
   (!Y X. subset_sets(X,Y) \/ element_of_set(in_1st_set(X,Y),X)) /\
   (!X Y. element_of_set(in_1st_set(X,Y),Y) ==> subset_sets(X,Y)) /\
   (basis(cx,f)) /\
   (~subset_sets(union_of_members(top_of_basis(f)),cx)) ==> F`;
  

val TOP002_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Vf U. element_of_collection(U,top_of_basis(Vf)) \/ element_of_set(f11(Vf,U),U)) /\
   (!X. ~element_of_set(X,empty_set)) /\
   (~element_of_collection(empty_set,top_of_basis(f))) ==> F`;


val TOP004_1 = 
 Term
`(!(Vf:'a) (U:'b). element_of_set(U,union_of_members(Vf)) ==> element_of_set(U,f1(Vf,U))) /\
   (!U Vf. element_of_set(U,union_of_members(Vf)) ==> element_of_collection(f1(Vf,U),Vf)) /\
   (!U (Uu1:'c) Vf. element_of_set(U,Uu1) /\ element_of_collection(Uu1,Vf) ==> element_of_set(U,union_of_members(Vf))) /\
   (!Vf U Va. element_of_set(U,intersection_of_members(Vf)) /\ element_of_collection(Va,Vf) ==> element_of_set(U,Va)) /\
   (!U Vf. element_of_set(U,intersection_of_members(Vf)) \/ element_of_collection(f2(Vf,U),Vf)) /\
   (!Vf U. element_of_set(U,f2(Vf,U)) ==> element_of_set(U,intersection_of_members(Vf))) /\
   (!Vt X. topological_space(X,Vt) ==> equal_sets(union_of_members(Vt),X)) /\
   (!X Vt. topological_space(X,Vt) ==> element_of_collection(empty_set,Vt)) /\
   (!X Vt. topological_space(X,Vt) ==> element_of_collection(X,Vt)) /\
   (!X Y Z Vt. topological_space(X,Vt) /\ element_of_collection(Y,Vt) /\ element_of_collection(Z,Vt) ==> element_of_collection(intersection_of_sets(Y,Z),Vt)) /\
   (!X Vf Vt. topological_space(X,Vt) /\ subset_collections(Vf,Vt) ==> element_of_collection(union_of_members(Vf),Vt)) /\
   (!X Vt. equal_sets(union_of_members(Vt),X) /\ element_of_collection(empty_set,Vt) /\ element_of_collection(X,Vt) ==> topological_space(X,Vt) \/ element_of_collection(f3(X,Vt),Vt) \/ subset_collections(f5(X,Vt),Vt)) /\
   (!X Vt. equal_sets(union_of_members(Vt),X) /\ element_of_collection(empty_set,Vt) /\ element_of_collection(X,Vt) /\ element_of_collection(union_of_members(f5(X,Vt)),Vt) ==> topological_space(X,Vt) \/ element_of_collection(f3(X,Vt),Vt)) /\
   (!X Vt. equal_sets(union_of_members(Vt),X) /\ element_of_collection(empty_set,Vt) /\ element_of_collection(X,Vt) ==> topological_space(X,Vt) \/ element_of_collection(f4(X,Vt),Vt) \/ subset_collections(f5(X,Vt),Vt)) /\
   (!X Vt. equal_sets(union_of_members(Vt),X) /\ element_of_collection(empty_set,Vt) /\ element_of_collection(X,Vt) /\ element_of_collection(union_of_members(f5(X,Vt)),Vt) ==> topological_space(X,Vt) \/ element_of_collection(f4(X,Vt),Vt)) /\
   (!X Vt. equal_sets(union_of_members(Vt),X) /\ element_of_collection(empty_set,Vt) /\ element_of_collection(X,Vt) /\ element_of_collection(intersection_of_sets(f3(X,Vt),f4(X,Vt)),Vt) ==> topological_space(X,Vt) \/ subset_collections(f5(X,Vt),Vt)) /\
   (!X Vt. equal_sets(union_of_members(Vt),X) /\ element_of_collection(empty_set,Vt) /\ element_of_collection(X,Vt) /\ element_of_collection(intersection_of_sets(f3(X,Vt),f4(X,Vt)),Vt) /\ element_of_collection(union_of_members(f5(X,Vt)),Vt) ==> topological_space(X,Vt)) /\
   (!U X Vt. open(U,X,Vt) ==> topological_space(X,Vt)) /\
   (!X U Vt. open(U,X,Vt) ==> element_of_collection(U,Vt)) /\
   (!X U Vt. topological_space(X,Vt) /\ element_of_collection(U,Vt) ==> open(U,X,Vt)) /\
   (!U X Vt. closed(U,X,Vt) ==> topological_space(X,Vt)) /\
   (!U X Vt. closed(U,X,Vt) ==> open(relative_complement_sets(U,X),X,Vt)) /\
   (!U X Vt. topological_space(X,Vt) /\ open(relative_complement_sets(U,X),X,Vt) ==> closed(U,X,Vt)) /\
   (!Vs X Vt. finer(Vt,Vs,X) ==> topological_space(X,Vt)) /\
   (!Vt X Vs. finer(Vt,Vs,X) ==> topological_space(X,Vs)) /\
   (!X Vs Vt. finer(Vt,Vs,X) ==> subset_collections(Vs,Vt)) /\
   (!X Vs Vt. topological_space(X,Vt) /\ topological_space(X,Vs) /\ subset_collections(Vs,Vt) ==> finer(Vt,Vs,X)) /\
   (!Vf X. basis(X,Vf) ==> equal_sets(union_of_members(Vf),X)) /\
   (!X Vf Y Vb1 Vb2. basis(X,Vf) /\ element_of_set(Y,X) /\ element_of_collection(Vb1,Vf) /\ element_of_collection(Vb2,Vf) /\ element_of_set(Y,intersection_of_sets(Vb1,Vb2)) ==> element_of_set(Y,f6(X,Vf,Y,Vb1,Vb2))) /\
   (!X Y Vb1 Vb2 Vf. basis(X,Vf) /\ element_of_set(Y,X) /\ element_of_collection(Vb1,Vf) /\ element_of_collection(Vb2,Vf) /\ element_of_set(Y,intersection_of_sets(Vb1,Vb2)) ==> element_of_collection(f6(X,Vf,Y,Vb1,Vb2),Vf)) /\
   (!X Vf Y Vb1 Vb2. basis(X,Vf) /\ element_of_set(Y,X) /\ element_of_collection(Vb1,Vf) /\ element_of_collection(Vb2,Vf) /\ element_of_set(Y,intersection_of_sets(Vb1,Vb2)) ==> subset_sets(f6(X,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1,Vb2))) /\
   (!Vf X. equal_sets(union_of_members(Vf),X) ==> basis(X,Vf) \/ element_of_set(f7(X,Vf),X)) /\
   (!X Vf. equal_sets(union_of_members(Vf),X) ==> basis(X,Vf) \/ element_of_collection(f8(X,Vf),Vf)) /\
   (!X Vf. equal_sets(union_of_members(Vf),X) ==> basis(X,Vf) \/ element_of_collection(f9(X,Vf),Vf)) /\
   (!X Vf. equal_sets(union_of_members(Vf),X) ==> basis(X,Vf) \/ element_of_set(f7(X,Vf),intersection_of_sets(f8(X,Vf),f9(X,Vf)))) /\
   (!Uu9 X Vf. equal_sets(union_of_members(Vf),X) /\ element_of_set(f7(X,Vf),Uu9) /\ element_of_collection(Uu9,Vf) /\ subset_sets(Uu9,intersection_of_sets(f8(X,Vf),f9(X,Vf))) ==> basis(X,Vf)) /\
   (!Vf U X. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_set(X,f10(Vf,U,X))) /\
   (!U X Vf. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_collection(f10(Vf,U,X),Vf)) /\
   (!Vf X U. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> subset_sets(f10(Vf,U,X),U)) /\
   (!Vf U. element_of_collection(U,top_of_basis(Vf)) \/ element_of_set(f11(Vf,U),U)) /\
   (!Vf Uu11 U. element_of_set(f11(Vf,U),Uu11) /\ element_of_collection(Uu11,Vf) /\ subset_sets(Uu11,U) ==> element_of_collection(U,top_of_basis(Vf))) /\
   (!U Y X Vt. element_of_collection(U,subspace_topology(X,Vt,Y)) ==> topological_space(X,Vt)) /\
   (!U Vt Y X. element_of_collection(U,subspace_topology(X,Vt,Y)) ==> subset_sets(Y,X)) /\
   (!X Y U Vt. element_of_collection(U,subspace_topology(X,Vt,Y)) ==> element_of_collection(f12(X,Vt,Y,U),Vt)) /\
   (!X Vt Y U. element_of_collection(U,subspace_topology(X,Vt,Y)) ==> equal_sets(U,intersection_of_sets(Y,f12(X,Vt,Y,U)))) /\
   (!X Vt U Y Uu12. topological_space(X,Vt) /\ subset_sets(Y,X) /\ element_of_collection(Uu12,Vt) /\ equal_sets(U,intersection_of_sets(Y,Uu12)) ==> element_of_collection(U,subspace_topology(X,Vt,Y))) /\
   (!U Y X Vt. element_of_set(U,interior(Y,X,Vt)) ==> topological_space(X,Vt)) /\
   (!U Vt Y X. element_of_set(U,interior(Y,X,Vt)) ==> subset_sets(Y,X)) /\
   (!Y X Vt U. element_of_set(U,interior(Y,X,Vt)) ==> element_of_set(U,f13(Y,X,Vt,U))) /\
   (!X Vt U Y. element_of_set(U,interior(Y,X,Vt)) ==> subset_sets(f13(Y,X,Vt,U),Y)) /\
   (!Y U X Vt. element_of_set(U,interior(Y,X,Vt)) ==> open(f13(Y,X,Vt,U),X,Vt)) /\
   (!U Y Uu13 X Vt. topological_space(X,Vt) /\ subset_sets(Y,X) /\ element_of_set(U,Uu13) /\ subset_sets(Uu13,Y) /\ open(Uu13,X,Vt) ==> element_of_set(U,interior(Y,X,Vt))) /\
   (!U Y X Vt. element_of_set(U,closure(Y,X,Vt)) ==> topological_space(X,Vt)) /\
   (!U Vt Y X. element_of_set(U,closure(Y,X,Vt)) ==> subset_sets(Y,X)) /\
   (!Y X Vt U V. element_of_set(U,closure(Y,X,Vt)) /\ subset_sets(Y,V) /\ closed(V,X,Vt) ==> element_of_set(U,V)) /\
   (!Y X Vt U. topological_space(X,Vt) /\ subset_sets(Y,X) ==> element_of_set(U,closure(Y,X,Vt)) \/ subset_sets(Y,f14(Y,X,Vt,U))) /\
   (!Y U X Vt. topological_space(X,Vt) /\ subset_sets(Y,X) ==> element_of_set(U,closure(Y,X,Vt)) \/ closed(f14(Y,X,Vt,U),X,Vt)) /\
   (!Y X Vt U. topological_space(X,Vt) /\ subset_sets(Y,X) /\ element_of_set(U,f14(Y,X,Vt,U)) ==> element_of_set(U,closure(Y,X,Vt))) /\
   (!U Y X Vt. neighborhood(U,Y,X,Vt) ==> topological_space(X,Vt)) /\
   (!Y U X Vt. neighborhood(U,Y,X,Vt) ==> open(U,X,Vt)) /\
   (!X Vt Y U. neighborhood(U,Y,X,Vt) ==> element_of_set(Y,U)) /\
   (!X Vt Y U. topological_space(X,Vt) /\ open(U,X,Vt) /\ element_of_set(Y,U) ==> neighborhood(U,Y,X,Vt)) /\
   (!Z Y X Vt. limit_point(Z,Y,X,Vt) ==> topological_space(X,Vt)) /\
   (!Z Vt Y X. limit_point(Z,Y,X,Vt) ==> subset_sets(Y,X)) /\
   (!Z X Vt U Y. limit_point(Z,Y,X,Vt) /\ neighborhood(U,Z,X,Vt) ==> element_of_set(f15(Z,Y,X,Vt,U),intersection_of_sets(U,Y))) /\
   (!Y X Vt U Z. ~(limit_point(Z,Y,X,Vt) /\ neighborhood(U,Z,X,Vt) /\ eq_p(f15(Z,Y,X,Vt,U),Z))) /\
   (!Y Z X Vt. topological_space(X,Vt) /\ subset_sets(Y,X) ==> limit_point(Z,Y,X,Vt) \/ neighborhood(f16(Z,Y,X,Vt),Z,X,Vt)) /\
   (!X Vt Y Uu16 Z. topological_space(X,Vt) /\ subset_sets(Y,X) /\ element_of_set(Uu16,intersection_of_sets(f16(Z,Y,X,Vt),Y)) ==> limit_point(Z,Y,X,Vt) \/ eq_p(Uu16,Z)) /\
   (!U Y X Vt. element_of_set(U,boundary(Y,X,Vt)) ==> topological_space(X,Vt)) /\
   (!U Y X Vt. element_of_set(U,boundary(Y,X,Vt)) ==> element_of_set(U,closure(Y,X,Vt))) /\
   (!U Y X Vt. element_of_set(U,boundary(Y,X,Vt)) ==> element_of_set(U,closure(relative_complement_sets(Y,X),X,Vt))) /\
   (!U Y X Vt. topological_space(X,Vt) /\ element_of_set(U,closure(Y,X,Vt)) /\ element_of_set(U,closure(relative_complement_sets(Y,X),X,Vt)) ==> element_of_set(U,boundary(Y,X,Vt))) /\
   (!X Vt. hausdorff(X,Vt) ==> topological_space(X,Vt)) /\
   (!X_2 X_1 X Vt. hausdorff(X,Vt) /\ element_of_set(X_1,X) /\ element_of_set(X_2,X) ==> eq_p(X_1,X_2) \/ neighborhood(f17(X,Vt,X_1,X_2),X_1,X,Vt)) /\
   (!X_1 X_2 X Vt. hausdorff(X,Vt) /\ element_of_set(X_1,X) /\ element_of_set(X_2,X) ==> eq_p(X_1,X_2) \/ neighborhood(f18(X,Vt,X_1,X_2),X_2,X,Vt)) /\
   (!X Vt X_1 X_2. hausdorff(X,Vt) /\ element_of_set(X_1,X) /\ element_of_set(X_2,X) ==> eq_p(X_1,X_2) \/ disjoint_s(f17(X,Vt,X_1,X_2),f18(X,Vt,X_1,X_2))) /\
   (!Vt X. topological_space(X,Vt) ==> hausdorff(X,Vt) \/ element_of_set(f19(X,Vt),X)) /\
   (!Vt X. topological_space(X,Vt) ==> hausdorff(X,Vt) \/ element_of_set(f20(X,Vt),X)) /\
   (!X Vt. topological_space(X,Vt) /\ eq_p(f19(X,Vt),f20(X,Vt)) ==> hausdorff(X,Vt)) /\
   (!X Vt Uu19 Uu20. topological_space(X,Vt) /\ neighborhood(Uu19,f19(X,Vt),X,Vt) /\ neighborhood(Uu20,f20(X,Vt),X,Vt) /\ disjoint_s(Uu19,Uu20) ==> hausdorff(X,Vt)) /\
   (!Va1 Va2 X Vt. separation(Va1,Va2,X,Vt) ==> topological_space(X,Vt)) /\
   (!Va2 X Vt Va1. ~(separation(Va1,Va2,X,Vt) /\ equal_sets(Va1,empty_set))) /\
   (!Va1 X Vt Va2. ~(separation(Va1,Va2,X,Vt) /\ equal_sets(Va2,empty_set))) /\
   (!Va2 X Va1 Vt. separation(Va1,Va2,X,Vt) ==> element_of_collection(Va1,Vt)) /\
   (!Va1 X Va2 Vt. separation(Va1,Va2,X,Vt) ==> element_of_collection(Va2,Vt)) /\
   (!Vt Va1 Va2 X. separation(Va1,Va2,X,Vt) ==> equal_sets(union_of_sets(Va1,Va2),X)) /\
   (!X Vt Va1 Va2. separation(Va1,Va2,X,Vt) ==> disjoint_s(Va1,Va2)) /\
   (!Vt X Va1 Va2. topological_space(X,Vt) /\ element_of_collection(Va1,Vt) /\ element_of_collection(Va2,Vt) /\ equal_sets(union_of_sets(Va1,Va2),X) /\ disjoint_s(Va1,Va2) ==> separation(Va1,Va2,X,Vt) \/ equal_sets(Va1,empty_set) \/ equal_sets(Va2,empty_set)) /\
   (!X Vt. connected_space(X,Vt) ==> topological_space(X,Vt)) /\
   (!Va1 Va2 X Vt. ~(connected_space(X,Vt) /\ separation(Va1,Va2,X,Vt))) /\
   (!X Vt. topological_space(X,Vt) ==> connected_space(X,Vt) \/ separation(f21(X,Vt),f22(X,Vt),X,Vt)) /\
   (!Va X Vt. connected_set(Va,X,Vt) ==> topological_space(X,Vt)) /\
   (!Vt Va X. connected_set(Va,X,Vt) ==> subset_sets(Va,X)) /\
   (!X Vt Va. connected_set(Va,X,Vt) ==> connected_space(Va,subspace_topology(X,Vt,Va))) /\
   (!X Vt Va. topological_space(X,Vt) /\ subset_sets(Va,X) /\ connected_space(Va,subspace_topology(X,Vt,Va)) ==> connected_set(Va,X,Vt)) /\
   (!Vf X Vt. open_covering(Vf,X,Vt) ==> topological_space(X,Vt)) /\
   (!X Vf Vt. open_covering(Vf,X,Vt) ==> subset_collections(Vf,Vt)) /\
   (!Vt Vf X. open_covering(Vf,X,Vt) ==> equal_sets(union_of_members(Vf),X)) /\
   (!Vt Vf X. topological_space(X,Vt) /\ subset_collections(Vf,Vt) /\ equal_sets(union_of_members(Vf),X) ==> open_covering(Vf,X,Vt)) /\
   (!X Vt. compact_space(X,Vt) ==> topological_space(X,Vt)) /\
   (!X Vt Vf1. compact_space(X,Vt) /\ open_covering(Vf1,X,Vt) ==> finite(f23(X,Vt,Vf1))) /\
   (!X Vt Vf1. compact_space(X,Vt) /\ open_covering(Vf1,X,Vt) ==> subset_collections(f23(X,Vt,Vf1),Vf1)) /\
   (!Vf1 X Vt. compact_space(X,Vt) /\ open_covering(Vf1,X,Vt) ==> open_covering(f23(X,Vt,Vf1),X,Vt)) /\
   (!X Vt. topological_space(X,Vt) ==> compact_space(X,Vt) \/ open_covering(f24(X,Vt),X,Vt)) /\
   (!Uu24 X Vt. topological_space(X,Vt) /\ finite(Uu24) /\ subset_collections(Uu24,f24(X,Vt)) /\ open_covering(Uu24,X,Vt) ==> compact_space(X,Vt)) /\
   (!Va X Vt. compact_set(Va,X,Vt) ==> topological_space(X,Vt)) /\
   (!Vt Va X. compact_set(Va,X,Vt) ==> subset_sets(Va,X)) /\
   (!X Vt Va. compact_set(Va,X,Vt) ==> compact_space(Va,subspace_topology(X,Vt,Va))) /\
   (!X Vt Va. topological_space(X,Vt) /\ subset_sets(Va,X) /\ compact_space(Va,subspace_topology(X,Vt,Va)) ==> compact_set(Va,X,Vt)) /\
   (basis(cx,f)) /\
   (!U. element_of_collection(U,top_of_basis(f))) /\
   (!V. element_of_collection(V,top_of_basis(f))) /\
   (!U V. ~element_of_collection(intersection_of_sets(U,V),top_of_basis(f))) 
   ==> F`;
  

val TOP004_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!U Uu1 Vf. element_of_set(U,Uu1) /\ element_of_collection(Uu1,Vf) ==> element_of_set(U,union_of_members(Vf))) /\
   (!Vf X. basis(X,Vf) ==> equal_sets(union_of_members(Vf),X)) /\
   (!X Vf Y Vb1 Vb2. basis(X,Vf) /\ element_of_set(Y,X) /\ element_of_collection(Vb1,Vf) /\ element_of_collection(Vb2,Vf) /\ element_of_set(Y,intersection_of_sets(Vb1,Vb2)) ==> element_of_set(Y,f6(X,Vf,Y,Vb1,Vb2))) /\
   (!X Y Vb1 Vb2 Vf. basis(X,Vf) /\ element_of_set(Y,X) /\ element_of_collection(Vb1,Vf) /\ element_of_collection(Vb2,Vf) /\ element_of_set(Y,intersection_of_sets(Vb1,Vb2)) ==> element_of_collection(f6(X,Vf,Y,Vb1,Vb2),Vf)) /\
   (!X Vf Y Vb1 Vb2. basis(X,Vf) /\ element_of_set(Y,X) /\ element_of_collection(Vb1,Vf) /\ element_of_collection(Vb2,Vf) /\ element_of_set(Y,intersection_of_sets(Vb1,Vb2)) ==> subset_sets(f6(X,Vf,Y,Vb1,Vb2),intersection_of_sets(Vb1,Vb2))) /\
   (!Vf U X. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_set(X,f10(Vf,U,X))) /\
   (!U X Vf. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_collection(f10(Vf,U,X),Vf)) /\
   (!Vf X U. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> subset_sets(f10(Vf,U,X),U)) /\
   (!Vf U. element_of_collection(U,top_of_basis(Vf)) \/ element_of_set(f11(Vf,U),U)) /\
   (!Vf Uu11 U. element_of_set(f11(Vf,U),Uu11) /\ element_of_collection(Uu11,Vf) /\ subset_sets(Uu11,U) ==> element_of_collection(U,top_of_basis(Vf))) /\
   (!Y X Z. subset_sets(X,Y) /\ subset_sets(Y,Z) ==> subset_sets(X,Z)) /\
   (!Y Z X. element_of_set(Z,intersection_of_sets(X,Y)) ==> element_of_set(Z,X)) /\
   (!X Z Y. element_of_set(Z,intersection_of_sets(X,Y)) ==> element_of_set(Z,Y)) /\
   (!X Z Y. element_of_set(Z,X) /\ element_of_set(Z,Y) ==> element_of_set(Z,intersection_of_sets(X,Y))) /\
   (!X U Y V. subset_sets(X,Y) /\ subset_sets(U,V) ==> subset_sets(intersection_of_sets(X,U),intersection_of_sets(Y,V))) /\
   (!X Z Y. equal_sets(X,Y) /\ element_of_set(Z,X) ==> element_of_set(Z,Y)) /\
   (!Y X. equal_sets(intersection_of_sets(X,Y),intersection_of_sets(Y,X))) /\
   (basis(cx,f)) /\
   (!U. element_of_collection(U,top_of_basis(f))) /\
   (!V. element_of_collection(V,top_of_basis(f))) /\
   (!U V. ~element_of_collection(intersection_of_sets(U,V),top_of_basis(f)))
   ==> F`;
  

val TOP005_2 = 
Lib.with_flag(Globals.guessing_tyvars,true)
 Term
`(!Vf U. element_of_set(U,union_of_members(Vf)) ==> element_of_set(U,f1(Vf,U))) /\
   (!U Vf. element_of_set(U,union_of_members(Vf)) ==> element_of_collection(f1(Vf,U),Vf)) /\
   (!Vf U X. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_set(X,f10(Vf,U,X))) /\
   (!U X Vf. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> element_of_collection(f10(Vf,U,X),Vf)) /\
   (!Vf X U. element_of_collection(U,top_of_basis(Vf)) /\ element_of_set(X,U) ==> subset_sets(f10(Vf,U,X),U)) /\
   (!Vf U. element_of_collection(U,top_of_basis(Vf)) \/ element_of_set(f11(Vf,U),U)) /\
   (!Vf Uu11 U. element_of_set(f11(Vf,U),Uu11) /\ element_of_collection(Uu11,Vf) /\ subset_sets(Uu11,U) ==> element_of_collection(U,top_of_basis(Vf))) /\
   (!X U Y. element_of_set(U,X) ==> subset_sets(X,Y) \/ element_of_set(U,Y)) /\
   (!Y X Z. subset_sets(X,Y) /\ element_of_collection(Y,Z) ==> subset_sets(X,union_of_members(Z))) /\
   (!X U Y. subset_collections(X,Y) /\ element_of_collection(U,X) ==> element_of_collection(U,Y)) /\
   (subset_collections(g,top_of_basis(f))) /\
   (~element_of_collection(union_of_members(g),top_of_basis(f))) ==> F`;
  

