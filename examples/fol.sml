(*---------------------------------------------------------------------------*
 * Some first order logic examples, using John Harrison's implementation     *
 * of MESON. There are many more such examples in src/meson/test.sml.        *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Invokes MESON and supplies some statistics as well.                       *
 *---------------------------------------------------------------------------*)

fun Prove tm =
  Lib.with_flag(mesonLib.chatting, 1)
    (Count.apply Tactical.prove)
       (tm,mesonLib.MESON_TAC[]);


val LOS = Term
  `(!x y z. P x y /\ P y z ==> P x z) /\
   (!x y z. Q x y /\ Q y z ==> Q x z) /\
   (!x y. P x y ==> P y x) /\
   (!x y. P x y \/ Q x y)
   ==> (!x y. P x y) \/ (!x y. Q x y)`;

Prove LOS;;


val CAT001_3 = Term
`(!X. equal(X,X)) /\
 (!Y X. equal(X,Y) ==> equal(Y,X)) /\
 (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
 (!Y X. equivalent(X,Y) ==> there_exists(X)) /\
 (!X Y. equivalent(X,Y) ==> equal(X,Y)) /\
 (!X Y. there_exists(X) /\ equal(X,Y) ==> equivalent(X,Y)) /\
 (!X. there_exists(domain(X)) ==> there_exists(X)) /\
 (!X. there_exists(codomain(X)) ==> there_exists(X)) /\
 (!Y X. there_exists(compose(X,Y)) ==> there_exists(domain(X))) /\
 (!X Y. there_exists(compose(X,Y)) ==> equal(domain(X),codomain(Y))) /\
 (!X Y. there_exists(domain(X)) /\ equal(domain(X),codomain(Y)) ==>
        there_exists(compose(X,Y))) /\
 (!X Y Z. equal(compose(X,compose(Y,Z)),compose(compose(X,Y),Z))) /\
 (!X. equal(compose(X,domain(X)),X)) /\
 (!X. equal(compose(codomain(X),X),X)) /\
 (!X Y. equivalent(X,Y) ==> there_exists(Y)) /\
 (!X Y. there_exists X /\ there_exists Y /\ equal(X,Y) ==> equivalent(X,Y)) /\
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
 (!Y X Z. equal(compose(compose(a,b),X),Y) /\
          equal(compose(compose(a,b),Z),Y) ==> equal(X,Z)) /\
 (there_exists(compose(b,h))) /\
 (equal(compose(b,h),compose(b,g))) /\
 (~equal(h,g))
  ==>
     F`;

Prove CAT001_3;


val CAT005_1 = Term
`(!X. equal(X,X)) /\
 (!Y X. equal(X,Y) ==> equal(Y,X)) /\
 (!Y X Z. equal(X,Y) /\ equal(Y,Z) ==> equal(X,Z)) /\
 (!X Y. defined(X,Y) ==> product(X,Y,compose(X,Y))) /\
 (!Z X Y. product(X,Y,Z) ==> defined(X,Y)) /\
 (!X Xy Y Z. product(X,Y,Xy) /\ defined(Xy,Z) ==> defined(Y,Z)) /\
 (!Y Xy Z X Yz. product(X,Y,Xy) /\ product(Y,Z,Yz) /\
                defined(Xy,Z) ==> defined(X,Yz)) /\
 (!Xy Y Z X Yz Xyz. product(X,Y,Xy) /\ product(Xy,Z,Xyz) /\
                    product(Y,Z,Yz) ==> product(X,Yz,Xyz)) /\
 (!Z Yz X Y. product(Y,Z,Yz) /\ defined(X,Yz) ==> defined(X,Y)) /\
 (!Y X Yz Xy Z. product(Y,Z,Yz) /\ product(X,Y,Xy) /\
                defined(X,Yz) ==> defined(Xy,Z)) /\
 (!Yz X Y Xy Z Xyz. product(Y,Z,Yz) /\ product(X,Yz,Xyz) /\
                    product(X,Y,Xy) ==> product(Xy,Z,Xyz)) /\
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
 (~equal(domain(a),d))
  ==>
     F`;


Prove CAT005_1; (* Takes a while *)
