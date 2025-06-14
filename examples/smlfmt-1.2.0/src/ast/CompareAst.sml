(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure CompareAst:
sig
  val equal: {tabWidth: int} -> Ast.t * Ast.t -> bool
end =
struct

  (* =======================================================================
   * combinators for functions of type 'a * 'a -> bool (equality checkers)
   *
   * makes it a bit easier to write equality checks over records with this
   * idiom:
   *
   *   val checker =
   *     at #field1 eq1 <&>
   *     at #field2 eq2 <&>
   *     ...            <&>
   *     at #fieldN eqN
   *
   *   val result = checker (x, y)
   *)

  type 'a eq = 'a * 'a -> bool

  fun at (select: 'b -> 'a) (eq: 'a eq) : 'b eq =
    fn (x: 'b, y: 'b) => eq (select x, select y)

  fun <&> (eq1: 'a eq, eq2: 'a eq) : 'a eq =
    fn (x, y) => eq1 (x, y) andalso eq2 (x, y)

  infix 2 <&>

  (* ======================================================================= *)

  fun equal_op eq (op1, op2) =
    case (op1, op2) of
      (SOME x, SOME y) => eq (x, y)
    | (NONE, NONE) => true
    | _ => false

  (* ======================================================================= *)

  open Ast


  fun equal {tabWidth: int} (Ast tops1, Ast tops2) =
    let

      fun equal_tok (t1, t2) =
        Token.sameExceptForMultilineIndentation {tabWidth = tabWidth} (t1, t2)


      fun equal_syntaxseq eq (s1, s2) =
        case (s1, s2) of
          (SyntaxSeq.Empty, SyntaxSeq.Empty) => true
        | (SyntaxSeq.One x, SyntaxSeq.One y) => eq (x, y)
        | (SyntaxSeq.Many x, SyntaxSeq.Many y) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal eq)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (x, y)
            end
        | _ => false


      fun equal_ty (t1, t2) =
        case (t1, t2) of
          (Ty.Var v1, Ty.Var v2) => equal_tok (v1, v2)

        | (Ty.Record r1, Ty.Record r2) =>
            let
              val checker =
                at #left equal_tok <&> at #right equal_tok
                <&> at #delims (Seq.equal equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #lab equal_tok <&> at #colon equal_tok <&> at #ty equal_ty))
            in
              checker (r1, r2)
            end

        | (Ty.Tuple t1, Ty.Tuple t2) =>
            let
              val checker =
                at #elems (Seq.equal equal_ty)
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (t1, t2)
            end

        | (Ty.Con c1, Ty.Con c2) =>
            let
              val checker =
                at #args (equal_syntaxseq equal_ty)
                <&> at #id (at MaybeLongToken.getToken equal_tok)
            in
              checker (c1, c2)
            end

        | (Ty.Arrow a1, Ty.Arrow a2) =>
            let
              val checker =
                at #from equal_ty <&> at #arrow equal_tok <&> at #to equal_ty
            in
              checker (a1, a2)
            end

        | (Ty.Parens p1, Ty.Parens p2) =>
            let
              val checker =
                at #left equal_tok <&> at #ty equal_ty <&> at #right equal_tok
            in
              checker (p1, p2)
            end

        | _ => false


      fun equal_patrow (r1, r2) =
        case (r1, r2) of
          (Pat.DotDotDot d1, Pat.DotDotDot d2) => equal_tok (d1, d2)

        | (Pat.LabEqPat lep1, Pat.LabEqPat lep2) =>
            let
              val checker =
                at #lab equal_tok <&> at #eq equal_tok <&> at #pat equal_pat
            in
              checker (lep1, lep2)
            end

        | (Pat.LabAsPat lap1, Pat.LabAsPat lap2) =>
            let
              val checker =
                at #id equal_tok
                <&> at #ty (equal_op (at #colon equal_tok <&> at #ty equal_ty))
                <&>
                at #aspat (equal_op (at #ass equal_tok <&> at #pat equal_pat))
            in
              checker (lap1, lap2)
            end

        | _ => false


      and equal_pat (p1, p2) =
        case (p1, p2) of
          (Pat.Wild w1, Pat.Wild w2) => equal_tok (w1, w2)

        | (Pat.Const c1, Pat.Const c2) => equal_tok (c1, c2)

        | (Pat.Unit u1, Pat.Unit u2) =>
            (at #left equal_tok <&> at #right equal_tok) (u1, u2)

        | (Pat.Ident i1, Pat.Ident i2) =>
            let
              val checker =
                at #opp (equal_op equal_tok)
                <&> at #id (at MaybeLongToken.getToken equal_tok)
            in
              checker (i1, i2)
            end

        | (Pat.List l1, Pat.List l2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_pat)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (l1, l2)
            end

        | (Pat.Tuple t1, Pat.Tuple t2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_pat)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (t1, t2)
            end

        | (Pat.Record r1, Pat.Record r2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_patrow)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (r1, r2)
            end

        | (Pat.Parens p1, Pat.Parens p2) =>
            let
              val checker =
                at #left equal_tok <&> at #pat equal_pat <&> at #right equal_tok
            in
              checker (p1, p2)
            end

        | (Pat.Con c1, Pat.Con c2) =>
            let
              val checker =
                at #opp (equal_op equal_tok)
                <&> at #id (at MaybeLongToken.getToken equal_tok)
                <&> at #atpat equal_pat
            in
              checker (c1, c2)
            end

        | (Pat.Infix i1, Pat.Infix i2) =>
            let
              val checker =
                at #left equal_pat <&> at #id equal_tok <&> at #right equal_pat
            in
              checker (i1, i2)
            end

        | (Pat.Typed t1, Pat.Typed t2) =>
            let
              val checker =
                at #pat equal_pat <&> at #colon equal_tok <&> at #ty equal_ty
            in
              checker (t1, t2)
            end

        | (Pat.Layered l1, Pat.Layered l2) =>
            let
              val checker =
                at #opp (equal_op equal_tok) <&> at #id equal_tok
                <&> at #ty (equal_op (at #colon equal_tok <&> at #ty equal_ty))
                <&> at #ass equal_tok <&> at #pat equal_pat
            in
              checker (l1, l2)
            end

        | (Pat.Or o1, Pat.Or o2) =>
            let
              val checker =
                at #elems (Seq.equal equal_pat)
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (o1, o2)
            end

        | _ => false


      fun equal_rowexp (re1, re2) =
        case (re1, re2) of
          (Exp.RecordRow r1, Exp.RecordRow r2) =>
            let
              val checker =
                at #lab equal_tok <&> at #eq equal_tok <&> at #exp equal_exp
            in
              checker (r1, r2)
            end

        | (Exp.RecordPun p1, Exp.RecordPun p2) => at #id equal_tok (p1, p2)

        | _ => false


      and equal_exp (e1, e2) =
        case (e1, e2) of
          (Exp.Const c1, Exp.Const c2) => equal_tok (c1, c2)

        | (Exp.Ident i1, Exp.Ident i2) =>
            let
              val checker =
                at #opp (equal_op equal_tok)
                <&> at #id (at MaybeLongToken.getToken equal_tok)
            in
              checker (i1, i2)
            end

        | (Exp.Record r1, Exp.Record r2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_rowexp)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (r1, r2)
            end

        | (Exp.Select s1, Exp.Select s2) =>
            (at #hash equal_tok <&> at #label equal_tok) (s1, s2)

        | (Exp.Unit u1, Exp.Unit u2) =>
            (at #left equal_tok <&> at #right equal_tok) (u1, u2)

        | (Exp.Tuple t1, Exp.Tuple t2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_exp)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (t1, t2)
            end

        | (Exp.List l1, Exp.List l2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_exp)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (l1, l2)
            end

        | (Exp.Sequence s1, Exp.Sequence s2) =>
            let
              val checker =
                at #left equal_tok <&> at #elems (Seq.equal equal_exp)
                <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok
            in
              checker (s1, s2)
            end

        | (Exp.LetInEnd lie1, Exp.LetInEnd lie2) =>
            let
              val checker =
                at #lett equal_tok <&> at #dec equal_dec <&> at #inn equal_tok
                <&> at #exps (Seq.equal equal_exp)
                <&> at #delims (Seq.equal equal_tok) <&> at #endd equal_tok
            in
              checker (lie1, lie2)
            end

        | (Exp.Parens p1, Exp.Parens p2) =>
            (at #left equal_tok <&> at #exp equal_exp <&> at #right equal_tok)
              (p1, p2)

        | (Exp.App a1, Exp.App a2) =>
            (at #left equal_exp <&> at #right equal_exp) (a1, a2)

        | (Exp.Infix i1, Exp.Infix i2) =>
            let
              val checker =
                at #left equal_exp <&> at #id equal_tok <&> at #right equal_exp
            in
              checker (i1, i2)
            end

        | (Exp.Typed t1, Exp.Typed t2) =>
            let
              val checker =
                at #exp equal_exp <&> at #colon equal_tok <&> at #ty equal_ty
            in
              checker (t1, t2)
            end

        | (Exp.Andalso a1, Exp.Andalso a2) =>
            let
              val checker =
                at #left equal_exp <&> at #andalsoo equal_tok
                <&> at #right equal_exp
            in
              checker (a1, a2)
            end

        | (Exp.Orelse o1, Exp.Orelse o2) =>
            let
              val checker =
                at #left equal_exp <&> at #orelsee equal_tok
                <&> at #right equal_exp
            in
              checker (o1, o2)
            end

        | (Exp.Handle h1, Exp.Handle h2) =>
            let
              val checker =
                at #exp equal_exp <&> at #handlee equal_tok
                <&>
                at #elems (Seq.equal
                  (at #pat equal_pat <&> at #arrow equal_tok
                   <&> at #exp equal_exp)) <&> at #delims (Seq.equal equal_tok)
                <&> at #optbar (equal_op equal_tok)
            in
              checker (h1, h2)
            end

        | (Exp.Raise r1, Exp.Raise r2) =>
            (at #raisee equal_tok <&> at #exp equal_exp) (r1, r2)

        | (Exp.IfThenElse ite1, Exp.IfThenElse ite2) =>
            let
              val checker =
                at #iff equal_tok <&> at #exp1 equal_exp <&> at #thenn equal_tok
                <&> at #exp2 equal_exp <&> at #elsee equal_tok
                <&> at #exp3 equal_exp
            in
              checker (ite1, ite2)
            end

        | (Exp.While w1, Exp.While w2) =>
            let
              val checker =
                at #whilee equal_tok <&> at #exp1 equal_exp
                <&> at #doo equal_tok <&> at #exp2 equal_exp
            in
              checker (w1, w2)
            end

        | (Exp.Case c1, Exp.Case c2) =>
            let
              val checker =
                at #casee equal_tok <&> at #exp equal_exp <&> at #off equal_tok
                <&>
                at #elems (Seq.equal
                  (at #pat equal_pat <&> at #arrow equal_tok
                   <&> at #exp equal_exp)) <&> at #delims (Seq.equal equal_tok)
                <&> at #optbar (equal_op equal_tok)
            in
              checker (c1, c2)
            end

        | (Exp.Fn f1, Exp.Fn f2) =>
            let
              val checker =
                at #fnn equal_tok
                <&>
                at #elems (Seq.equal
                  (at #pat equal_pat <&> at #arrow equal_tok
                   <&> at #exp equal_exp)) <&> at #delims (Seq.equal equal_tok)
                <&> at #optbar (equal_op equal_tok)
            in
              checker (f1, f2)
            end

        | (Exp.MLtonSpecific m1, Exp.MLtonSpecific m2) =>
            let
              val checker =
                at #underscore equal_tok <&> at #directive equal_tok
                <&> at #contents (Seq.equal equal_tok)
                <&> at #semicolon equal_tok
            in
              checker (m1, m2)
            end

        | _ => false


      and equal_fnameargs (fna1, fna2) =
        case (fna1, fna2) of
          (Exp.PrefixedFun pf1, Exp.PrefixedFun pf2) =>
            let
              val checker =
                at #opp (equal_op equal_tok) <&> at #id equal_tok
                <&> at #args (Seq.equal equal_pat)
            in
              checker (pf1, pf2)
            end

        | (Exp.InfixedFun if1, Exp.InfixedFun if2) =>
            let
              val checker =
                at #larg equal_pat <&> at #id equal_tok <&> at #rarg equal_pat
            in
              checker (if1, if2)
            end

        | (Exp.CurriedInfixedFun cif1, Exp.CurriedInfixedFun cif2) =>
            let
              val checker =
                at #lparen equal_tok <&> at #larg equal_pat <&> at #id equal_tok
                <&> at #rarg equal_pat <&> at #rparen equal_tok
                <&> at #args (Seq.equal equal_pat)
            in
              checker (cif1, cif2)
            end

        | _ => false


      and equal_fvalbind (fv1, fv2) =
        let
          val checker =
            at #delims (Seq.equal equal_tok)
            <&>
            at #elems (Seq.equal
              (at #delims (Seq.equal equal_tok)
               <&> at #optbar (equal_op equal_tok)
               <&>
               at #elems (Seq.equal
                 (at #fname_args equal_fnameargs
                  <&>
                  at #ty (equal_op (at #colon equal_tok <&> at #ty equal_ty))
                  <&> at #eq equal_tok <&> at #exp equal_exp))))
        in
          checker (fv1, fv2)
        end


      and equal_typbind (tb1, tb2) =
        let
          val checker =
            at #elems (Seq.equal
              (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
               <&> at #eq equal_tok <&> at #ty equal_ty))
            <&> at #delims (Seq.equal equal_tok)
        in
          checker (tb1, tb2)
        end


      and equal_datbind (db1, db2) =
        let
          val checker =
            at #delims (Seq.equal equal_tok)
            <&>
            at #elems (Seq.equal
              (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
               <&> at #eq equal_tok <&> at #optbar (equal_op equal_tok)
               <&> at #delims (Seq.equal equal_tok)
               <&>
               at #elems (Seq.equal
                 (at #opp (equal_op equal_tok) <&> at #id equal_tok
                  <&> at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty))))))
        in
          checker (db1, db2)
        end


      and equal_dec (d1, d2) =
        case (d1, d2) of
          (Exp.DecEmpty, Exp.DecEmpty) => true

        | (Exp.DecVal v1, Exp.DecVal v2) =>
            let
              val checker =
                at #vall equal_tok <&> at #tyvars (equal_syntaxseq equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #recc (equal_op equal_tok) <&> at #pat equal_pat
                   <&> at #eq equal_tok <&> at #exp equal_exp))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (v1, v2)
            end

        | (Exp.DecFun f1, Exp.DecFun f2) =>
            let
              val checker =
                at #funn equal_tok <&> at #tyvars (equal_syntaxseq equal_tok)
                <&> at #fvalbind equal_fvalbind
            in
              checker (f1, f2)
            end

        | (Exp.DecType t1, Exp.DecType t2) =>
            let val checker = at #typee equal_tok <&> at #typbind equal_typbind
            in checker (t1, t2)
            end

        | (Exp.DecDatatype d1, Exp.DecDatatype d2) =>
            let
              val checker =
                at #datatypee equal_tok <&> at #datbind equal_datbind
                <&>
                at #withtypee (equal_op
                  (at #withtypee equal_tok <&> at #typbind equal_typbind))
            in
              checker (d1, d2)
            end

        | (Exp.DecReplicateDatatype rd1, Exp.DecReplicateDatatype rd2) =>
            let
              val checker =
                at #left_datatypee equal_tok <&> at #left_id equal_tok
                <&> at #eq equal_tok <&> at #right_datatypee equal_tok
                <&> at #right_id (at MaybeLongToken.getToken equal_tok)
            in
              checker (rd1, rd2)
            end

        | (Exp.DecAbstype a1, Exp.DecAbstype a2) =>
            let
              val checker =
                at #abstypee equal_tok <&> at #datbind equal_datbind
                <&>
                at #withtypee (equal_op
                  (at #withtypee equal_tok <&> at #typbind equal_typbind))
                <&> at #withh equal_tok <&> at #dec equal_dec
                <&> at #endd equal_tok
            in
              checker (a1, a2)
            end

        | (Exp.DecException e1, Exp.DecException e2) =>
            let
              val checker =
                at #exceptionn equal_tok <&> at #elems (Seq.equal equal_exbind)
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (e1, e2)
            end

        | (Exp.DecLocal l1, Exp.DecLocal l2) =>
            let
              val checker =
                at #locall equal_tok <&> at #left_dec equal_dec
                <&> at #inn equal_tok <&> at #right_dec equal_dec
                <&> at #endd equal_tok
            in
              checker (l1, l2)
            end

        | (Exp.DecOpen o1, Exp.DecOpen o2) =>
            let
              val checker =
                at #openn equal_tok
                <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
            in
              checker (o1, o2)
            end

        | (Exp.DecMultiple m1, Exp.DecMultiple m2) =>
            let
              val checker =
                at #elems (Seq.equal equal_dec)
                <&> at #delims (Seq.equal (equal_op equal_tok))
            in
              checker (m1, m2)
            end

        | (Exp.DecInfix i1, Exp.DecInfix i2) =>
            let
              val checker =
                at #infixx equal_tok <&> at #precedence (equal_op equal_tok)
                <&> at #elems (Seq.equal equal_tok)
            in
              checker (i1, i2)
            end

        | (Exp.DecInfixr i1, Exp.DecInfixr i2) =>
            let
              val checker =
                at #infixrr equal_tok <&> at #precedence (equal_op equal_tok)
                <&> at #elems (Seq.equal equal_tok)
            in
              checker (i1, i2)
            end

        | (Exp.DecNonfix n1, Exp.DecNonfix n2) =>
            let
              val checker =
                at #nonfixx equal_tok <&> at #elems (Seq.equal equal_tok)
            in
              checker (n1, n2)
            end

        | _ => false


      and equal_exbind (b1, b2) =
        case (b1, b2) of
          (Exp.ExnNew n1, Exp.ExnNew n2) =>
            let
              val checker =
                at #opp (equal_op equal_tok) <&> at #id equal_tok
                <&> at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty))
            in
              checker (n1, n2)
            end

        | (Exp.ExnReplicate r1, Exp.ExnReplicate r2) =>
            let
              val checker =
                at #opp (equal_op equal_tok) <&> at #left_id equal_tok
                <&> at #eq equal_tok
                <&> at #right_id (at MaybeLongToken.getToken equal_tok)
            in
              checker (r1, r2)
            end

        | _ => false


      fun equal_sigdec (Sig.Signature s1, Sig.Signature s2) =
        let
          val checker =
            at #signaturee equal_tok <&> at #delims (Seq.equal equal_tok)
            <&>
            at #elems (Seq.equal
              (at #ident equal_tok <&> at #eq equal_tok
               <&> at #sigexp equal_sigexp))
        in
          checker (s1, s2)
        end


      and equal_sigexp (se1, se2) =
        case (se1, se2) of
          (Sig.Ident i1, Sig.Ident i2) => equal_tok (i1, i2)

        | (Sig.Spec s1, Sig.Spec s2) =>
            let
              val checker =
                at #sigg equal_tok <&> at #spec equal_spec
                <&> at #endd equal_tok
            in
              checker (s1, s2)
            end

        | (Sig.WhereType w1, Sig.WhereType w2) =>
            let
              val checker =
                at #sigexp equal_sigexp
                <&>
                at #elems (Seq.equal
                  (at #wheree equal_tok <&> at #typee equal_tok
                   <&> at #tyvars (equal_syntaxseq equal_tok)
                   <&> at #tycon (at MaybeLongToken.getToken equal_tok)
                   <&> at #eq equal_tok <&> at #ty equal_ty))
            in
              checker (w1, w2)
            end

        | _ => false


      and equal_spec (s1, s2) =
        case (s1, s2) of
          (Sig.EmptySpec, Sig.EmptySpec) => true

        | (Sig.Val v1, Sig.Val v2) =>
            let
              val checker =
                at #vall equal_tok
                <&>
                at #elems (Seq.equal
                  (at #vid equal_tok <&> at #colon equal_tok <&> at #ty equal_ty))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (v1, v2)
            end

        | (Sig.Type t1, Sig.Type t2) =>
            let
              val checker =
                at #typee equal_tok
                <&>
                at #elems (Seq.equal
                  (at #tyvars (equal_syntaxseq equal_tok)
                   <&> at #tycon equal_tok))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (t1, t2)
            end

        | (Sig.TypeAbbreviation a1, Sig.TypeAbbreviation a2) =>
            let val checker = at #typee equal_tok <&> at #typbind equal_typbind
            in checker (a1, a2)
            end

        | (Sig.Eqtype e1, Sig.Eqtype e2) =>
            let
              val checker =
                at #eqtypee equal_tok
                <&>
                at #elems (Seq.equal
                  (at #tyvars (equal_syntaxseq equal_tok)
                   <&> at #tycon equal_tok))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (e1, e2)
            end

        | (Sig.Datatype d1, Sig.Datatype d2) =>
            let
              val checker =
                at #datatypee equal_tok <&> at #delims (Seq.equal equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #tyvars (equal_syntaxseq equal_tok)
                   <&> at #tycon equal_tok <&> at #eq equal_tok
                   <&> at #optbar (equal_op equal_tok)
                   <&> at #delims (Seq.equal equal_tok)
                   <&>
                   at #elems (Seq.equal
                     (at #vid equal_tok
                      <&>
                      at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty))))))
            in
              checker (d1, d2)
            end

        | (Sig.ReplicateDatatype r1, Sig.ReplicateDatatype r2) =>
            let
              val checker =
                at #left_datatypee equal_tok <&> at #left_id equal_tok
                <&> at #eq equal_tok <&> at #right_datatypee equal_tok
                <&> at #right_id (at MaybeLongToken.getToken equal_tok)
            in
              checker (r1, r2)
            end

        | (Sig.Exception e1, Sig.Exception e2) =>
            let
              val checker =
                at #exceptionn equal_tok <&> at #delims (Seq.equal equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #vid equal_tok
                   <&>
                   at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty))))
            in
              checker (e1, e2)
            end

        | (Sig.Structure s1, Sig.Structure s2) =>
            let
              val checker =
                at #structuree equal_tok <&> at #delims (Seq.equal equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #id equal_tok <&> at #colon equal_tok
                   <&> at #sigexp equal_sigexp))
            in
              checker (s1, s2)
            end

        | (Sig.Include i1, Sig.Include i2) =>
            let val checker = at #includee equal_tok <&> at #sigexp equal_sigexp
            in checker (i1, i2)
            end

        | (Sig.IncludeIds i1, Sig.IncludeIds i2) =>
            let
              val checker =
                at #includee equal_tok <&> at #sigids (Seq.equal equal_tok)
            in
              checker (i1, i2)
            end

        | (Sig.SharingType s1, Sig.SharingType s2) =>
            let
              val checker =
                at #spec equal_spec <&> at #sharingg equal_tok
                <&> at #typee equal_tok
                <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (s1, s2)
            end

        | (Sig.Sharing s1, Sig.Sharing s2) =>
            let
              val checker =
                at #spec equal_spec <&> at #sharingg equal_tok
                <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (s1, s2)
            end

        | (Sig.Multiple m1, Sig.Multiple m2) =>
            let
              val checker =
                at #elems (Seq.equal equal_spec)
                <&> at #delims (Seq.equal (equal_op equal_tok))
            in
              checker (m1, m2)
            end

        | _ => false


      fun equal_strdec (sd1, sd2) =
        case (sd1, sd2) of
          (Str.DecEmpty, Str.DecEmpty) => true

        | (Str.DecCore d1, Str.DecCore d2) => equal_dec (d1, d2)

        | (Str.DecStructure s1, Str.DecStructure s2) =>
            let
              val checker =
                at #structuree equal_tok <&> at #delims (Seq.equal equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #strid equal_tok
                   <&>
                   at #constraint (equal_op
                     (at #colon equal_tok <&> at #sigexp equal_sigexp))
                   <&> at #eq equal_tok <&> at #strexp equal_strexp))
            in
              checker (s1, s2)
            end

        | (Str.DecMultiple m1, Str.DecMultiple m2) =>
            let
              val checker =
                at #elems (Seq.equal equal_strdec)
                <&> at #delims (Seq.equal (equal_op equal_tok))
            in
              checker (m1, m2)
            end

        | (Str.DecLocalInEnd lie1, Str.DecLocalInEnd lie2) =>
            let
              val checker =
                at #locall equal_tok <&> at #strdec1 equal_strdec
                <&> at #inn equal_tok <&> at #strdec2 equal_strdec
                <&> at #endd equal_tok
            in
              checker (lie1, lie2)
            end

        | (Str.MLtonOverload o1, Str.MLtonOverload o2) =>
            let
              val checker =
                at #underscore equal_tok <&> at #overload equal_tok
                <&> at #prec equal_tok <&> at #name equal_tok
                <&> at #colon equal_tok <&> at #colon equal_tok
                <&> at #ty equal_ty <&> at #ass equal_tok
                <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
                <&> at #delims (Seq.equal equal_tok)
            in
              checker (o1, o2)
            end

        | _ => false


      and equal_strexp (se1, se2) =
        case (se1, se2) of
          (Str.Ident i1, Str.Ident i2) =>
            at MaybeLongToken.getToken equal_tok (i1, i2)

        | (Str.Struct s1, Str.Struct s2) =>
            let
              val checker =
                at #structt equal_tok <&> at #strdec equal_strdec
                <&> at #endd equal_tok
            in
              checker (s1, s2)
            end

        | (Str.Constraint c1, Str.Constraint c2) =>
            let
              val checker =
                at #strexp equal_strexp <&> at #colon equal_tok
                <&> at #sigexp equal_sigexp
            in
              checker (c1, c2)
            end

        | (Str.FunAppExp e1, Str.FunAppExp e2) =>
            let
              val checker =
                at #funid equal_tok <&> at #lparen equal_tok
                <&> at #strexp equal_strexp <&> at #rparen equal_tok
            in
              checker (e1, e2)
            end

        | (Str.FunAppDec d1, Str.FunAppDec d2) =>
            let
              val checker =
                at #funid equal_tok <&> at #lparen equal_tok
                <&> at #strdec equal_strdec <&> at #rparen equal_tok
            in
              checker (d1, d2)
            end

        | (Str.LetInEnd lie1, Str.LetInEnd lie2) =>
            let
              val checker =
                at #lett equal_tok <&> at #strdec equal_strdec
                <&> at #inn equal_tok <&> at #strexp equal_strexp
                <&> at #endd equal_tok
            in
              checker (lie1, lie2)
            end

        | _ => false


      fun equal_fundec (Fun.DecFunctor x, Fun.DecFunctor y) =
        let
          fun equal_funarg (fa1, fa2) =
            case (fa1, fa2) of
              (Fun.ArgSpec s1, Fun.ArgSpec s2) => equal_spec (s1, s2)

            | (Fun.ArgIdent i1, Fun.ArgIdent i2) =>
                let
                  val checker =
                    at #strid equal_tok <&> at #colon equal_tok
                    <&> at #sigexp equal_sigexp
                in
                  checker (i1, i2)
                end

            | _ => false

          val checker =
            at #functorr equal_tok <&> at #delims (Seq.equal equal_tok)
            <&>
            at #elems (Seq.equal
              (at #funid equal_tok <&> at #lparen equal_tok
               <&> at #funarg equal_funarg <&> at #rparen equal_tok
               <&>
               at #constraint (equal_op
                 (at #colon equal_tok <&> at #sigexp equal_sigexp))
               <&> at #eq equal_tok <&> at #strexp equal_strexp))
        in
          checker (x, y)
        end


      fun equal_topdec (td1, td2) =
        case (td1, td2) of
          (SigDec sd1, SigDec sd2) => equal_sigdec (sd1, sd2)
        | (StrDec sd1, StrDec sd2) => equal_strdec (sd1, sd2)
        | (FunDec fd1, FunDec fd2) => equal_fundec (fd1, fd2)
        | (TopExp te1, TopExp te2) =>
            let val checker = at #exp equal_exp <&> at #semicolon equal_tok
            in checker (te1, te2)
            end
        | _ => false

    in
      Seq.equal (at #topdec equal_topdec <&> at #semicolon (equal_op equal_tok))
        (tops1, tops2)
    end

end
