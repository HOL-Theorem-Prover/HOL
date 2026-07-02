/**
 * @file HOLScript grammar for tree-sitter
 * @author Daniel Nezamabadi
 * @license MIT
 */

// Adapted tree-sitter-sml by Matthew Fluet, released under the MIT license.

/* eslint-disable require-jsdoc */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// ******************************************************** //
// Extensions
// ******************************************************** //

const EXTENSIONS = true;

function ifExtElse(ext, resExt, resStd) {
    if (Array.isArray(EXTENSIONS) ?
        (Array.isArray(ext) ?
         ext.some((ext) => EXTENSIONS.includes(ext)) :
         EXTENSIONS.includes(ext)) :
        EXTENSIONS) {
        return resExt;
    } else {
        return resStd;
    }
}

function ifExtAlt(ext, resExt) {
    return ifExtElse(ext, resExt, choice());
}
function ifExtOpt(ext, resExt) {
    return ifExtElse(ext, optional(resExt), blank());
}

const optBar = ifExtOpt('optBar', '|');

// ******************************************************** //
// Regular Expressions for Constants
// ******************************************************** //

const decDigitRE = '[0-9]';
const decNumRE = ifExtElse(
    'extendedNumConst',
    `${decDigitRE}(?:_*${decDigitRE})*`,
    `${decDigitRE}+`,
);
const hexDigitRE = '[A-Fa-f0-9]';
const hexNumRE = ifExtElse(
    'extendedNumConst',
    `${hexDigitRE}(?:_*${hexDigitRE})*`,
    `${hexDigitRE}+`,
);
const binDigitRE = '[01]';
const binNumRE = ifExtElse(
    'extendedNumConst',
    `${binDigitRE}(?:_*${binDigitRE})*`,
    `${binDigitRE}+`,
);
const integerConstRE = ifExtElse(
    'extendedNumConst',
    `~?${decNumRE}|~?0x${hexNumRE}|~?0b${binNumRE}`,
    `~?${decNumRE}|~?0x${hexNumRE}`,
);
const wordConstRE = ifExtElse(
    'extendedNumConst',
    `0w${decNumRE}|0wx${hexNumRE}|0wb${binNumRE}`,
    `0w${decNumRE}|0wx${hexNumRE}`,
);
const fracRE = `[.]${decNumRE}`;
const expRE = `[eE]~?${decNumRE}`;
const realConstRE = `~?${decNumRE}${fracRE}(?:${expRE})?|~?${decNumRE}(?:${fracRE})?${expRE}`;

const stringConstRE = '"(?:[^"\\\\]|\\\\[^\\s]|\\\\\\s*\\\\)*"';
const charConstRE = '#"(?:[^"\\\\]|\\\\[^\\s]|\\\\\\s*\\\\)*"';

// ******************************************************** //
// Regular Expressions Identifiers
// ******************************************************** //

// Plain ASCII per the SML spec — `_alphaAlphaNumeric_ident' feeds
// SML's `vid' / `longvid' / `strid' and the HOL declaration names
// (theorem / definition / clause / dot-field / Quote / attribute),
// all of which are reflected as SML identifiers.  HOL-term
// identifiers that admit Unicode subscripts live in
// `_hol_alphanumeric'.
const alphaNumericIdentSuffixRE = /[A-Za-z0-9_']*/.source;
const alphaAlphaNumericIdentRE = `[A-Za-z]${alphaNumericIdentSuffixRE}`;
const primeAlphaNumericIdentRE = `'${alphaNumericIdentSuffixRE}`;
// Backtick is in SML's symbolic-vid class per the Definition, but
// HOL4 reserves it as a term-quote delimiter — never as part of an
// SML symbolic identifier — so excluding it lets the lexer pick
// `` ` '' as the quote opener rather than greedily merging `` `~ '',
// `` `[ '', etc. with the following char.
const symbolicIdentRE = /[!%&$#+\-/:<=>?@\\~^|*]+/.source;

// HOL-term identifier character classes (used in `_hol_alphanumeric').
//
// LETTERLIKE — Unicode "letterlike symbols" block plus curated math
// operators (∅ ∞ ∑ ∏ ∫ ∂ ⊤ ⊥ ⊢ ⊨) HOL treats as identifier starters.
// SUP — superscript-letter set (postfix variants like `nl³', `=⁺').
// SUB — subscript set (₀-₉, ₐ-ₜ).  GREEK — Greek capital + small letters.
//
// The qualified-name suffix `$<name>' allows the same starter set as
// a plain (non-variable, non-constructor) identifier — i.e. `a-zA-Z'
// plus Greek and letterlike — so it's factored out as one constant.
const HOL_LETTERLIKE = '℀-⅏∅∞∑∏∫∂⊤⊥⊢⊨';
const HOL_SUP_LETTERS = 'ʰ-ʸⁱⁿᵃ-ᵪ';
const HOL_SUB = '₀-₉ₐ-ₜ';
const HOL_GREEK = 'Ͱ-κμ-Ͽ';
const HOL_IDENT_STARTER = `a-zA-Z${HOL_GREEK}${HOL_LETTERLIKE}`;
const HOL_IDENT_CONT =
    `a-zA-Z${HOL_GREEK}0-9'_${HOL_SUB}${HOL_LETTERLIKE}${HOL_SUP_LETTERS}`;
const HOL_IDENT_DOLLAR_TAIL =
    `(\\$[${HOL_IDENT_STARTER}][${HOL_IDENT_CONT}]*)?`;

// ******************************************************** //
// "Separated By"
// ******************************************************** //

const commaSep = {name: 'Comma', token: ','};
const semicolonSep = {name: 'Semicolon', token: ';'};

function mkSepByAux(cnt, pre, sep, elt, pst) {
    if (cnt > 0) {
        return seq(
            pre ? sep : blank(),
            elt,
            mkSepByAux(cnt - 1, true, sep, elt, pst),
        );
    } else {
        if (pre) {
            if (pst) {
                return seq(repeat(seq(sep, elt)), pst(true));
            } else {
                return repeat(seq(sep, elt));
            }
        } else {
            if (pst) {
                return choice(pst(false), seq(elt, repeat(seq(sep, elt)), pst(true)));
            } else {
                return optional(seq(elt, repeat(seq(sep, elt))));
            }
        }
    }
}

function mkSepByCntFstLst(sep, elt, cnt, fst, lst) {
    let optSep = false; let empSep = false;
    let preSep; let pstSep;
    if (typeof sep === 'string') {
        preSep = blank();
        pstSep = blank();
    } else {
        if (ifExtElse('emp'.concat(sep.name), true, false)) {
            empSep = true;
            optSep = true;
        } else if (ifExtElse('opt'.concat(sep.name), true, false)) {
            optSep = true;
        }
        sep = sep.token;
        if (empSep) {
            sep = repeat1(sep);
        }
        if (optSep) {
            preSep = optional(sep);
            pstSep = optional(sep);
        } else {
            preSep = blank();
            pstSep = blank();
        }
    }

    let pst;
    if (lst) {
        pst = (pre) => {
            if (lst.rqd) {
                if (pre) {
                    return seq(sep, lst.elt, pstSep);
                } else {
                    return seq(lst.elt, pstSep);
                }
            } else {
                if (pre) {
                    return seq(optional(seq(sep, lst.elt)), pstSep);
                } else {
                    return optional(seq(lst.elt, pstSep));
                }
            }
        };
    } else if (optSep) {
        pst = (pre) => {
            if (pre) {
                return pstSep;
            } else {
                return blank();
            }
        };
    } else {
        pst = false;
    };

    if (fst) {
        if (fst.rqd) {
            return seq(preSep, fst.elt, mkSepByAux(cnt, true, sep, elt, pst));
        } else {
            return choice(
                seq(preSep, fst.elt, mkSepByAux(cnt, true, sep, elt, pst)),
                seq(preSep, mkSepByAux(cnt, false, sep, elt, pst)),
            );
        }
    } else {
        return seq(preSep, mkSepByAux(cnt, false, sep, elt, pst));
    };
}

// function mkSepByCnt(sep, elt, cnt) {
//   return mkSepByCntFstLst(sep, elt, cnt, false, false);
// }

function mkSepBy(sep, elt, cnt) {
    return mkSepByCntFstLst(sep, elt, 0, false, false);
}

function mkSepBy1(sep, elt, cnt) {
    return mkSepByCntFstLst(sep, elt, 1, false, false);
}

function mkSepBy2(sep, elt, cnt) {
    return mkSepByCntFstLst(sep, elt, 2, false, false);
}

// `t <opn> k1 ↦ v1; k2 ↦ v2; … <cls>' — shared body of the three
// bracketed update forms (list-update `l❲…❳', fmap-update `fm⟨…⟩',
// function-update `f⦇…⦈').  Optional trailing `;' is HOL's uniform
// relaxation for enclosed list forms.
function holBracketUpdate($, opn, cls) {
    return seq(
        $._hol_tight, opn,
        mkSepBy1(';', seq($._hol_term, '↦', $._hol_term)),
        optional(';'),
        cls,
    );
}

function mkBrakSepByCntFstLst(opn, sep, elt, cnt, fst, lst, cls) {
    return seq(opn, mkSepByCntFstLst(sep, elt, cnt, fst, lst), cls);
}

function mkBrakSepBy(opn, sep, elt, cls) {
    return seq(opn, mkSepBy(sep, elt), cls);
}

function mkBrakSepBy1(opn, sep, elt, cls) {
    return seq(opn, mkSepBy1(sep, elt), cls);
}

function mkSeqAux(clsSing, clsSep) {
    return choice(clsSing, mkBrakSepBy1('(', ',', clsSep, ')'));
}

function mkSeq(cls) {
    return mkSeqAux(cls, cls);
}

// ******************************************************** //
// Grammar
// ******************************************************** //

module.exports = grammar({
    name: 'holscript',

    extras: $ => [
        /\s+/,
        $.block_comment,
        ...ifExtElse('lineComment', [$.line_comment], []),
    ],

    externals: $ => [
        $.block_comment,
        $.line_comment,
    ],

    supertypes: $ => [
        $._scon,
        $._exp,
        $._dec,
        $._pat,
        $._ty,
        $._strexp,
        $._strdec,
        $._sigexp,
        $._sigdec,
        $._spec,
        $._fctdec,
        $._topdec,
    ],

    inline: $ => [
    ],

    conflicts: $ => [
        [
            // Two tokens of lookahead required.
            $.wheretype_sigexp,
        ],
        // HOL
        // `nl³' could stand alone as a _hol_term or sit as the lhs of
        // an application (`nl³ x').  Both readings are valid; we want
        // the GLR parser to keep both alive and pick lhs when followed
        // by another atom.  Same shape for universe and field-select.
        [$._hol_application_lhs, $._hol_term],
        // Same shape between _hol_application_lhs and _hol_tight:
        // an identifier (or other shared shape) is ambiguous between
        // standing on the lhs of an application and being the tight
        // rhs of the enclosing application.  GLR resolves left-assoc
        // via the prec.left on hol_application.
        [$._hol_application_lhs, $._hol_tight],
        // Same shapes appear in both `_hol_term' (the general term
        // type, used everywhere) and `_hol_tight' (the
        // tighter-than-application subset).  GLR picks the right one
        // by context.
        [$._hol_term, $._hol_tight],
        [$._hol_term, $._hol_application_lhs, $._hol_tight],
    ],

    // HACK Causes problem when we add HOL things
    // word: $ => $._alphaAlphaNumeric_ident,

    rules: {
        source_file: $ => optional($._program),

        comment: $ => choice(
            $.block_comment,
            ifExtAlt('lineComment', $.line_comment),
        ),

        // ******************************************************** //
        // Special Constants
        // ******************************************************** //

        _scon: $ => choice(
            $.integer_scon,
            $.word_scon,
            $.real_scon,
            $.string_scon,
            $.char_scon,
        ),

        integer_scon: $ => new RegExp(integerConstRE),
        word_scon: $ => new RegExp(wordConstRE),
        real_scon: $ => new RegExp(realConstRE),
        string_scon: $ => new RegExp(stringConstRE),
        char_scon: $ => new RegExp(charConstRE),

        // ******************************************************** //
        // Identifier Classes (Core)
        // ******************************************************** //

        _alphaAlphaNumeric_ident: $ => new RegExp(alphaAlphaNumericIdentRE),
        _primeAlphaNumeric_ident: $ => new RegExp(primeAlphaNumericIdentRE),
        _symbolic_ident: $ => new RegExp(symbolicIdentRE),

        tyvar: $ => choice($._primeAlphaNumeric_ident),
        tyvarseq: $ => mkSeq($.tyvar),
        vid: $ => choice($._alphaAlphaNumeric_ident, $._symbolic_ident),
        longvid: $ => seq(repeat(seq($.strid, '.')), $.vid),
        tycon: $ => choice($._alphaAlphaNumeric_ident, $._symbolic_ident),
        longtycon: $ => seq(repeat(seq($.strid, '.')), $.tycon),
        lab: $ => choice($._alphaAlphaNumeric_ident, $._symbolic_ident, /[1-9][0-9]*/),

        // ******************************************************** //
        // Expressions and Matches (Core)
        // ******************************************************** //

        _atexp: $ => choice(
            $.scon_exp,
            $.vid_exp,
            $.record_exp,
            $.recordsel_exp,
            $.unit_exp,
            $.tuple_exp,
            $.list_exp,
            ifExtAlt('vectorExp', $.vec_exp),
            $.sequence_exp,
            $.let_exp,
            $.paren_exp,
            // HOL
            $.quoted_term,
            $.quoted_type,
            $.backquote
        ),

        scon_exp: $ => $._scon,
        vid_exp: $ => seq(optional('op'), $.longvid),
        record_exp: $ => mkBrakSepByCntFstLst(
            '{',
            commaSep,
            $._exprow, 0,
            false,
            ifExtElse('recordExt', {elt: $.ellipsis_exprow, rqd: false}, false),
            '}',
        ),
        _exprow: $ => choice(
            $.exprow,
            ifExtAlt('recordExpPun', $.labvar_exprow),
        ),
        exprow: $ => seq($.lab, '=', $._exp),
        labvar_exprow: $ => seq($.vid, optional(seq(':', $._ty))),
        ellipsis_exprow: $ => seq('...', '=', $._exp),
        recordsel_exp: $ => seq('#', $.lab),
        unit_exp: $ => prec(1, seq('(', ')')),
        tuple_exp: $ => mkBrakSepBy('(', commaSep, $._exp, ')'),
        list_exp: $ => mkBrakSepByCntFstLst(
            '[',
            commaSep,
            $._exp, 0,
            false,
            ifExtElse('listEllipsis', {elt: $.ellipsis_listexp, rqd: false}, false),
            ']',
        ),
        ellipsis_listexp: $ => seq('...', '=', $._exp),
        vec_exp: $ => mkBrakSepBy('#[', commaSep, $._exp, ']'),
        sequence_exp: $ => mkBrakSepBy('(', semicolonSep, $._exp, ')'),
        let_exp: $ => seq(
            'let',
            repeat(choice(';', field('dec', $._dec))),
            'in',
            mkSepBy1(semicolonSep, field('body', $._exp)),
            'end',
        ),
        paren_exp: $ => prec(1, seq('(', $._exp, ')')),

        // The Definition orders by decreasing precedence
        _exp: $ => choice(
            $._atexp,
            $.app_exp,
            $.typed_exp,
            $.conj_exp,
            $.disj_exp,
            $.handle_exp,
            $.raise_exp,
            $.cond_exp,
            $.iter_exp,
            $.case_exp,
            $.fn_exp,
        ),

        app_exp: $ => prec(10, seq($._atexp, repeat1($._atexp))),
        typed_exp: $ => prec(9, seq($._exp, ':', $._ty)),
        conj_exp: $ => prec.left(8, seq($._exp, 'andalso', $._exp)),
        disj_exp: $ => prec.left(7, seq($._exp, 'orelse', $._exp)),
        handle_exp: $ => prec(6, seq($._exp, 'handle', $._match)),
        raise_exp: $ => prec(5, seq('raise', $._exp)),
        cond_exp: $ => prec.right(4, seq(
            'if', field('if_exp', $._exp),
            'then', field('then_exp', $._exp),
            ifExtElse('optElse',
                      optional(seq('else', field('else_exp', $._exp))),
                      seq('else', field('else_exp', $._exp))),
        )),
        iter_exp: $ => prec(3, seq('while', field('while_exp', $._exp), 'do', field('do_exp', $._exp))),
        case_exp: $ => prec(2, seq('case', $._exp, 'of', $._match)),
        fn_exp: $ => prec(1, seq('fn', $._match)),

        _match: $ => prec.right(seq(optBar, mkSepBy1('|', $.mrule))),
        mrule: $ => seq($._pat, '=>', $._exp),

        // ******************************************************** //
        // Declarations and Bindings (Core)
        // ******************************************************** //

        _dec: $ => choice(
            $._dec_no_local,
            $.local_dec,
        ),
        _dec_no_local: $ => choice(
            ifExtAlt('doDec', $.do_dec),
            $.val_dec,
            $.fun_dec,
            $.type_dec,
            $.datatype_dec,
            $.datarepl_dec,
            $.abstype_dec,
            $.exception_dec,
            // $.local_dec,
            $.open_dec,
            $.infix_dec,
            $.infixr_dec,
            $.nonfix_dec,
        ),

        do_dec: $ => seq('do', $._exp),

        val_dec: $ => seq(
            'val',
            optional('rec'),
            optional($.tyvarseq),
            $._valbind,
        ),
        _valbind: $ => mkSepBy1('and', $.valbind),
        valbind: $ => seq(field('pat', $._pat), '=', field('def', $._exp)),

        fun_dec: $ => seq(
            'fun',
            optional($.tyvarseq),
            $._fvalbind,
        ),
        _fvalbind: $ => mkSepBy1('and', $.fvalbind),
        fvalbind: $ => $._fmatch,
        _fmatch: $ => seq(optBar, mkSepBy1('|', $.fmrule)),
        fmrule: $ => seq(
            choice(
                prec(2, seq(optional('op'), field('name', $.vid), repeat1(field('arg', $._atpat)))),
                prec(2, seq('(', field('argl', $._atpat), field('name', $.vid), field('argr', $._atpat), ')', repeat(field('arg', $._atpat)))),
                prec(0, seq(field('argl', $._atpat), field('name', $.vid), field('argr', $._atpat))),
            ),
            optional(seq(':', field('ty', $._ty))),
            '=',
            field('def', $._exp),
        ),

        type_dec: $ => seq('type', $._typbind),
        _typbind: $ => mkSepBy1('and', $.typbind),
        typbind: $ => seq(
            optional($.tyvarseq),
            field('name', $.tycon),
            '=',
            field('def', $._ty),
        ),

        datatype_dec: $ => seq(
            'datatype',
            $._datbind,
            optional(seq('withtype', field('withtype', $._typbind))),
        ),
        _datbind: $ => mkSepBy1('and', $.datbind),
        datbind: $ => seq(
            optional($.tyvarseq),
            field('name', $.tycon),
            '=',
            field('def', $._conbind),
        ),
        _conbind: $ => seq(optBar, mkSepBy1('|', $.conbind)),
        conbind: $ => seq(
            seq(optional('op'), field('name', $.vid)),
            optional(seq('of', field('ty', $._ty))),
        ),

        datarepl_dec: $ => seq(
            'datatype',
            field('name', $.tycon),
            '=',
            'datatype',
            field('def', $.longtycon),
        ),

        abstype_dec: $ => seq(
            'abstype',
            $._datbind,
            optional(seq('withtype', field('withtype', $._typbind))),
            'with',
            repeat(choice(';', field('dec', $._dec))),
            'end',
        ),

        exception_dec: $ => seq('exception', $._exbind),
        _exbind: $ => mkSepBy1('and', $.exbind),
        exbind: $ => choice(
            seq(
                seq(optional('op'), field('name', $.vid)),
                optional(seq('of', field('ty', $._ty))),
            ),
            seq(
                seq(optional('op'), field('name', $.vid)),
                '=',
                seq(optional('op'), field('def', $.longvid)),
            ),
        ),

        // `local <dec> in <body> end' — SML's local-declaration
        // shell.  The <body> region admits HOL declarations
        // (`Theorem'/`Definition'/`Datatype'/…) too, since real HOL
        // code uses `local val op >> = op THEN … in Theorem …
        // QED … end' to scope SML helpers used inside proofs.
        local_dec: $ => seq(
            'local',
            repeat(choice(';', field('dec', $._dec))),
            'in',
            repeat(choice(';', field('body', $._dec), field('body', $._topdec_hol))),
            'end',
        ),

        // The HOL-only subset of `_topdec' — used inside `local …
        // in …' bodies so HOL declarations aren't restricted to
        // top level.
        _topdec_hol: $ => choice(
            $.hol_definition,
            $.hol_definition_with_proof,
            $.hol_datatype,
            $.hol_theorem_with_proof,
            $.hol_theorem_alias,
            $.hol_inductive,
            $.hol_type_alias,
            $.hol_overload,
            $.hol_quote_block,
            $.hol_resume_proof,
            $.hol_finalise,
        ),

        open_dec: $ => seq('open', repeat1($.longstrid)),

        infix_dec: $ => seq('infix', optional(/[0-9]/), repeat1($.vid)),
        infixr_dec: $ => seq('infixr', optional(/[0-9]/), repeat1($.vid)),
        nonfix_dec: $ => seq('nonfix', repeat1($.vid)),

        // ******************************************************** //
        // Patterns (Core)
        // ******************************************************** //

        _atpat: $ => choice(
            $.wildcard_pat,
            $.scon_pat,
            $.vid_pat,
            $.record_pat,
            $.unit_pat,
            $.tuple_pat,
            $.list_pat,
            ifExtAlt('vectorPat', $.vec_pat),
            $.paren_pat,
        ),

        wildcard_pat: $ => '_',
        scon_pat: $ => $._scon,
        vid_pat: $ => seq(optional('op'), $.longvid),
        record_pat: $ => mkBrakSepByCntFstLst(
            '{',
            commaSep,
            $._patrow, 0,
            false,
            {elt: $.ellipsis_patrow, rqd: false},
            '}',
        ),
        _patrow: $ => choice($.patrow, $.labvar_patrow),
        patrow: $ => seq($.lab, '=', $._pat),
        labvar_patrow: $ => seq(
            $.vid,
            optional(seq(':', $._ty)),
            optional(seq('as', $._pat)),
        ),
        ellipsis_patrow: $ => seq('...', ifExtOpt('recordExt', seq('=', $._pat))),
        unit_pat: $ => prec(1, seq('(', ')')),
        tuple_pat: $ => mkBrakSepBy('(', commaSep, $._pat, ')'),
        list_pat: $ => mkBrakSepByCntFstLst(
            '[',
            commaSep,
            $._pat, 0,
            false,
            ifExtElse('listEllipsis', {elt: $.ellipsis_listpat, rqd: false}, false),
            ']'),
        ellipsis_listpat: $ => seq('...', '=', $._pat),
        vec_pat: $ => mkBrakSepBy('#[', commaSep, $._pat, ')'),
        paren_pat: $ => prec(1, seq('(', $._pat, ')')),

        // The Definition orders by decreasing precedence
        _pat: $ => choice(
            $._atpat,
            $.app_pat,
            $.typed_pat,
            ifExtElse('conjPat', $.conj_pat, $.as_pat),
            ifExtAlt(['orPat', 'disjPat'], $.disj_pat),
        ),

        app_pat: $ => prec(4, seq($._atpat, repeat1($._atpat))),
        typed_pat: $ => prec(3, seq($._pat, ':', $._ty)),
        as_pat: $ => prec.right(2, seq(optional('op'), $.vid, optional(seq(':', $._ty)), 'as', $._pat)),
        conj_pat: $ => prec.right(2, seq($._pat, 'as', $._pat)),
        disj_pat: $ => prec.left(1, seq($._pat, '|', $._pat)),

        // ******************************************************** //
        // Type expressions (Core)
        // ******************************************************** //

        _ty: $ => $._fn_ty,
        tyseq: $ => mkSeqAux($._atty, $._ty),

        _fn_ty: $ => choice($.fn_ty, $._tuple_ty),
        fn_ty: $ => seq($._tuple_ty, '->', $._fn_ty),

        _tuple_ty: $ => choice($.tuple_ty, $._paren_ty),
        tuple_ty: $ => mkSepBy2('*', $._paren_ty),

        _paren_ty: $ => choice($.paren_ty, $._atty),
        paren_ty: $ => seq('(', $._ty, ')'),

        _atty: $ => choice(
            $.tyvar_ty,
            $.record_ty,
            $.tycon_ty,
        ),

        tyvar_ty: $ => $.tyvar,
        record_ty: $ => mkBrakSepByCntFstLst(
            '{',
            commaSep,
            $.tyrow, 0,
            false,
            ifExtElse('recordExt', {elt: $.ellipsis_tyrow, rqd: false}, false),
            '}',
        ),
        tyrow: $ => seq($.lab, ':', $._ty),
        ellipsis_tyrow: $ => seq('...', ':', $._ty),
        tycon_ty: $ => seq(
            optional($.tyseq),
            $.longtycon,
        ),

        // ******************************************************** //
        // Identifier Classes (Modules)
        // ******************************************************** //

        strid: $ => choice($._alphaAlphaNumeric_ident),
        longstrid: $ => seq(repeat(seq($.strid, '.')), $.strid),
        sigid: $ => choice($._alphaAlphaNumeric_ident),
        fctid: $ => choice($._alphaAlphaNumeric_ident),

        // ******************************************************** //
        // Structure Expressions (Modules)
        // ******************************************************** //

        _strexp: $ => choice(
            $.struct_strexp,
            $.strid_strexp,
            $.constr_strexp,
            $.fctapp_strexp,
            $.let_strexp,
        ),

        struct_strexp: $ => seq(
            'struct',
            repeat(choice(';', field('strdec', $._strdec))),
            'end',
        ),
        strid_strexp: $ => $.longstrid,
        constr_strexp: $ => seq($._strexp, choice(':', ':>'), $._sigexp),
        fctapp_strexp: $ => seq(
            field('name', $.fctid),
            '(',
            field('arg',
                  choice(
                      $._strexp,
                      repeat(choice(';', $._strdec)),
                  ),
                 ),
            ')',
        ),
        let_strexp: $ => seq(
            'let',
            repeat(choice(';', field('dec', $._strdec))),
            'in',
            field('body', $._strexp),
            'end',
        ),

        _strdec: $ => choice(
            $._dec_no_local,
            $.structure_strdec,
            $.local_strdec,
        ),

        structure_strdec: $ => seq('structure', $._strbind),
        _strbind: $ => mkSepBy1('and', $.strbind),
        strbind: $ => seq(
            field('name', $.strid),
            optional(seq(choice(':', ':>'), field('sig', $._sigexp))),
            '=',
            field('def', $._strexp),
        ),

        local_strdec: $ => seq(
            'local',
            repeat(choice(';', field('dec', $._strdec))),
            'in',
            repeat(choice(';', field('body', $._strdec), field('body', $._topdec_hol))),
            'end',
        ),

        // ******************************************************** //
        // Signature Expressions (Modules)
        // ******************************************************** //

        _sigexp: $ => choice(
            $.sig_sigexp,
            $.sigid_sigexp,
            $.wheretype_sigexp,
        ),

        sig_sigexp: $ => seq(
            'sig',
            repeat(choice(';', field('spec', $._spec))),
            'end',
        ),
        sigid_sigexp: $ => $.sigid,
        wheretype_sigexp: $ => seq(
            $._sigexp,
            'where',
            mkSepBy1('and', seq(
                'type',
                optional($.tyvarseq),
                $.longtycon,
                '=',
                $._ty,
            )),
        ),

        _sigdec: $ => choice(
            $.signature_sigdec,
        ),
        signature_sigdec: $ => seq('signature', $._sigbind),
        _sigbind: $ => mkSepBy1('and', $.sigbind),
        sigbind: $ => seq(
            field('name', $.sigid),
            '=',
            field('def', $._sigexp),
        ),

        // ******************************************************** //
        // Specifications (Modules)
        // ******************************************************** //

        _spec: $ => choice(
            $.val_spec,
            $.type_spec,
            $.eqtype_spec,
            $.datatype_spec,
            $.datarepl_spec,
            $.exception_spec,
            $.structure_spec,
            $.include_spec,
            $.sharingtype_spec,
            $.sharing_spec,
        ),

        val_spec: $ => seq('val', $._valdesc),
        _valdesc: $ => mkSepBy1('and', $.valdesc),
        valdesc: $ => seq(field('name', $.vid), ':', field('ty', $._ty)),

        type_spec: $ => seq('type', choice($._typedesc, $._typbind)),
        _typedesc: $ => mkSepBy1('and', $.typedesc),
        typedesc: $ => seq(
            optional($.tyvarseq),
            field('name', $.tycon),
        ),

        eqtype_spec: $ => seq('eqtype', $._typedesc),

        datatype_spec: $ => seq(
            'datatype',
            $._datdesc,
            ifExtOpt('sigWithtype', seq('withtype', field('withtype', $._typbind))),
        ),
        _datdesc: $ => mkSepBy1('and', $.datdesc),
        datdesc: $ => seq(
            optional($.tyvarseq),
            field('name', $.tycon),
            '=',
            field('def', $._condesc),
        ),
        _condesc: $ => seq(optBar, mkSepBy1('|', $.condesc)),
        condesc: $ => seq(
            field('name', $.vid),
            optional(seq('of', field('ty', $._ty))),
        ),

        datarepl_spec: $ => seq(
            'datatype',
            field('name', $.tycon),
            '=',
            'datatype',
            field('def', $.longtycon),
        ),

        exception_spec: $ => seq('exception', $._exdesc),
        _exdesc: $ => mkSepBy1('and', $.exdesc),
        exdesc: $ => seq(
            field('name', $.vid),
            optional(seq('of', field('ty', $._ty))),
        ),

        structure_spec: $ => seq('structure', $._strdesc),
        _strdesc: $ => mkSepBy1('and', $.strdesc),
        strdesc: $ => seq(field('name', $.strid), ':', field('sig', $._sigexp)),

        include_spec: $ => seq('include', choice($._sigexp, seq($.sigid, repeat1($.sigid)))),

        sharingtype_spec: $ => seq('sharing', 'type', mkSepBy2('=', $.longtycon)),

        sharing_spec: $ => seq('sharing', mkSepBy2('=', $.longstrid)),

        // ******************************************************** //
        // Functors (Modules)
        // ******************************************************** //

        _fctdec: $ => choice(
            $.functor_fctdec,
        ),
        functor_fctdec: $ => seq('functor', $._fctbind),
        _fctbind: $ => mkSepBy1('and', $.fctbind),
        fctbind: $ => seq(
            field('name', $.fctid),
            '(',
            field('arg',
                  choice(
                      seq($.strid, ':', $._sigexp),
                      repeat(choice(';', $._spec)),
                  ),
                 ),
            ')',
            optional(seq(choice(':', ':>'), field('sig', $._sigexp))),
            '=',
            field('def', $._strexp),
        ),

        // ******************************************************** //
        // Topdecs
        // ******************************************************** //

        _topdec: $ => choice(
            $._strdec,
            $._sigdec,
            $._fctdec,
            // HOL
            $.hol_definition,
            $.hol_definition_with_proof,
            $.hol_datatype,
            $.hol_theorem_with_proof,
            $.hol_theorem_alias,
            $.hol_inductive,
            $.hol_type_alias,
            $.hol_theory_dec,
            $.hol_ancestors_dec,
            $.hol_libs_dec,
            $.hol_overload,
            $.hol_quote_block,
            $.hol_resume_proof,
            $.hol_finalise,
        ),

        // ******************************************************** //
        // Programs
        // ******************************************************** //

        _program: $ => seq(
            choice(repeat1($._topdec), $._exp),
            optional(seq(';', optional($._program))),
        ),


        // ******************************************************** //
        // HOL
        // ******************************************************** //
        antiquoted: $ => choice(
            seq('^', '(', $._exp, ')'),
            seq('^', alias($._alphaAlphaNumeric_ident, $.sml_variable))
        ),

        // `“term”' (Unicode smart quotes) or `` ``term`` '' (traditional
        // double-backtick ASCII form, still the dominant style in many
        // older HOL libraries).
        quoted_term: $ => choice(
            seq('“', $._hol_term, '”'),
            seq($._double_backtick, $._hol_term, $._double_backtick),
        ),

        // `“:τ”' or `` ``:τ`` '' — the leading colon after the open
        // delimiter is what marks the quotation as a type rather than
        // a term.
        quoted_type: $ => choice(
            seq('“', ':', $._hol_type, '”'),
            seq($._double_backtick, ':', $._hol_type, $._double_backtick),
        ),

        // The `` `` '' delimiter is two backticks, lexed as a single
        // token.  Without explicit priority the lexer is free to
        // choose either this 2-char form or a 2-char SML symbolic
        // identifier `` `` '' (since `` ` '' is in SML's symbolic-vid
        // character class); `prec(5, …)' biases the tie toward the
        // delimiter token so traditional `` ``term`` '' / `` ``:τ`` ''
        // quotations parse.
        _double_backtick: $ => token(prec(5, '``')),

        // Inside `‘…’' / `` `…` '' quotes:
        //   • any char that isn't `^', a backtick, or a smart quote;
        //   • a caret followed by *any* non-letter, non-`(', non-quote
        //     character — covers HOL's `^^' / `^`' escapes plus the
        //     common postfix-in-quoted-term shapes like `g^+', `R^*',
        //     `g^=', which HOL parses as the postfix forms `g²' / `R꙳'
        //     / `g^=' inside the backquote and *isn't* trying to
        //     antiquote.
        // Caret followed by a letter or `(' enters `antiquoted'.
        _quote_content: $ => choice(
            alias(/([^\^`‘’]|\^[^A-Za-z(‘’`])+/, $.quoted),
            $.antiquoted
        ),

        backquote: $ => choice(
            seq('‘', repeat($._quote_content), '’'),
            seq('`', repeat($._quote_content), '`'),
        ),

        hol_attributes: $ => seq(
            '[',
            mkSepBy1(',', alias($._alphaAlphaNumeric_ident, $.attribute)),
            ']'
        ),

        hol_definition: $ => seq(
            'Definition',
            alias($._alphaAlphaNumeric_ident, $.hol_defname),
            optional($.hol_attributes),
            ':',
            $.hol_fn_spec,
            'End'
        ),

        hol_definition_with_proof: $ => seq(
            'Definition',
            alias($._alphaAlphaNumeric_ident, $.hol_defname),
            optional($.hol_attributes),
            ':',
            $.hol_fn_spec,
            'Termination',
            $.tactic,
            'End'
        ),

        hol_datatype: $ => seq(
            'Datatype',
            ':',
            $.hol_binding,
            'End'
        ),

        hol_theorem_with_proof: $ => seq(
            choice('Theorem', 'Triviality'),
            alias($._alphaAlphaNumeric_ident, $.hol_thmname),
            optional($.hol_attributes),
            ':',
            alias($._hol_term, $.hol_thmstmt),
            'Proof',
            $.tactic,
            'QED'
        ),

        // `Resume <thm>[<label>]:' / `Resume <thm>:' opens the body of
        // a suspended proof.  The label form picks up a particular
        // suspendlabel; without one we resume whatever's still open.
        hol_resume_proof: $ => seq(
            'Resume',
            alias($._alphaAlphaNumeric_ident, $.hol_thmname),
            optional($.hol_attributes),
            ':',
            $.tactic,
            'QED'
        ),

        // `Finalise <thm>' closes out any remaining suspended proofs
        // for the named theorem.  Single-token declaration.
        hol_finalise: $ => seq(
            'Finalise',
            alias($._alphaAlphaNumeric_ident, $.hol_thmname),
        ),

        // Theorem foo = thm_expr [|> rule1 |> rule2 …]
        hol_theorem_alias: $ => seq(
            choice('Theorem', 'Triviality'),
            alias($._alphaAlphaNumeric_ident, $.hol_thmname),
            optional($.hol_attributes),
            '=',
            $._exp
        ),

        // Type x = ":type" — alias declaration for a HOL type.
        hol_type_alias: $ => seq(
            'Type',
            alias($._alphaAlphaNumeric_ident, $.hol_typename),
            optional($.hol_attributes),
            '=',
            $._exp
        ),

        // Inductive / CoInductive foo: <body> End
        // The body is one or more HOL terms.  `∧'/`/\\' joins clauses
        // within a single big conjunction (the indentScript style),
        // but adjacent clauses without any joining `∧' are also
        // accepted (the sampleScript CoInductive style — HOL treats
        // them as implicitly conjoined).  Clause labels
        // `[~name?[attrs]?:]' appear as a prefix annotation on a term
        // via `hol_labelled_term'.
        hol_inductive: $ => seq(
            choice('Inductive', 'CoInductive'),
            alias($._alphaAlphaNumeric_ident, $.hol_defname),
            optional($.hol_attributes),
            ':',
            alias(repeat1($._hol_term), $.hol_inductive_body),
            'End'
        ),

        // [~name:] / [name:] / [name[attr,…]:] / [~name[attr,…]:]
        //
        // A single lexical token, not a parse rule with sub-nodes.
        // The full bracketed form `[~name(\[attr,…\])?:]' can never be
        // any other valid HOL term, so tokenising it atomically beats
        // the parser-level alternative — which had it competing with
        // `hol_list' / `hol_list_index' and losing in clause-boundary
        // disambiguation.  The token text is `[~?name(\[attr,…\])?:]';
        // downstream tooling that wants the name or attributes parses
        // it back out of the token text.
        hol_clause_label: $ => token(new RegExp(
            '\\[' +
            '~?' +
            alphaAlphaNumericIdentRE +
            '(' +
                '\\[' +
                alphaAlphaNumericIdentRE +
                '(,' + alphaAlphaNumericIdentRE + ')*' +
            '\\])?' +
            ':\\]'
        )),

        // Theory name
        hol_theory_dec: $ => seq(
            'Theory',
            alias($._alphaAlphaNumeric_ident, $.hol_theoryname),
            optional($.hol_attributes)
        ),

        // Ancestors [attrs?] name name … (whitespace-separated)
        // `Ancestors [attrs?] name[name_attrs?] name[name_attrs?] …'
        // Each ancestor name can carry its own attribute block (e.g.
        // `term[qualified]' restricts to qualified-only references).
        hol_ancestors_dec: $ => seq(
            'Ancestors',
            optional($.hol_attributes),
            repeat1(seq(
                alias($._alphaAlphaNumeric_ident, $.hol_ancestor_name),
                optional($.hol_attributes),
            )),
        ),

        // `Libs' [attrs?] name[attrs]? name[attrs]? …
        // Each lib name can carry its own attribute block (`Q[qualified]',
        // `BasicProvers[qualified]', ...) — same shape as Ancestors.
        hol_libs_dec: $ => seq(
            'Libs',
            optional($.hol_attributes),
            repeat1(seq(
                alias($._alphaAlphaNumeric_ident, $.hol_lib_name),
                optional($.hol_attributes),
            )),
        ),

        // `Quote name [attrs]? : <opaque body> End' as a single lexical
        // token, using the standard regular-language construction for
        // "anything up to terminator T with no internal T".  Each body
        // alternative consumes a fixed number of characters; the DFA
        // is finite without lazy quantification or assertions.
        // `prec(10, …)' wins the length tie against the `vid' regex.
        hol_quote_block: $ => token(prec(10, new RegExp(
            `Quote[ \\t]+${alphaAlphaNumericIdentRE}` + // Quote keyword + name
            '([ \\t]*\\[[^\\]]*\\])?[ \\t]*:' +          // optional [attrs] then :
            '(' +                                        // body —
                '[^\\n]'                          + '|' +
                '\\n[^E]'                         + '|' +
                '\\nE[^n]'                        + '|' +
                '\\nEn[^d]'                       + '|' +
                '\\nEnd[A-Za-z0-9_\']' +
            ')*' +
            '\\nEnd[^A-Za-z0-9_\']'                     // \nEnd<non-ident>
        ))),

        // Overload name = expr  OR  Overload "symbol" = expr
        hol_overload: $ => seq(
            'Overload',
            choice(
                alias($._alphaAlphaNumeric_ident, $.hol_overloadname),
                alias($.string_scon, $.hol_overloadname)
            ),
            optional($.hol_attributes),
            '=',
            $._exp
        ),

        _atomic_tactic: $ => choice(
            $._exp,
            seq('(', $.THEN, ')')
        ),

        tactic: $ => choice(
            $._atomic_tactic,
            $.THEN
        ),

        // Tactic chain separators.  Symbolic ones: `\\' (original
        // ASCII THEN), `>>' (then), `>-' (then for first subgoal),
        // `>~ [‘pat’]' (select subgoal by pattern), `>|' (THEN_LT
        // — split into subgoals with a list tactic).  Word infixes:
        // `THEN' / `THENL' (ASCII); `by' (discharge a subgoal with
        // a tactic — `‘subgoal’ by tac' is the prevalent core-HOL
        // form) and `suffices_by' (the sufficient-to-show variant).
        // Right-hand side of each separator is an SML expression.
        THEN: $ => prec.left(seq(
            $._atomic_tactic,
            repeat1(seq(
                choice('\\\\', '>>', '>-', '>~', '>|',
                       'THEN', 'THENL', 'THEN_LT', 'THEN1',
                       'by', 'suffices_by'),
                $._atomic_tactic
            ))
        )),

        hol_binding: $ => seq(
            $.hol_identifier,
            '=',
            choice($.hol_constructor, $.hol_datatype_record)
        ),

        hol_constructor: $ => mkSepBy1('|', $.hol_clause),

        // Record-type body for a Datatype: <| field : type; … |>.
        // Same bracket / separator shape as a value-level record literal;
        // here each entry is `name : type' rather than `name := value'.
        hol_datatype_record: $ => seq(
            '<|',
            mkSepBy1(';', $.hol_datatype_record_field),
            '|>'
        ),
        hol_datatype_record_field: $ => seq(
            alias($._alphaAlphaNumeric_ident, $.hol_record_field_name),
            ':',
            $._hol_type
        ),

        hol_clause: $ => seq(
            $.hol_identifier,
            repeat($._hol_ty_spec)
        ),

        _hol_ty_spec: $ => choice(
            $.hol_atomic_type,
            seq('(', $._hol_type ,')')
        ),

        // A Definition body is just a HOL term.  Multi-clause
        // definitions are conjunctions (`∧'/`/\\'), individual
        // equations use `=' or `⇔' as binary operators — HOL's own
        // parser doesn't syntactically separate them from other
        // term-forming operators.  Downstream consumers can identify
        // eqn boundaries by looking for top-level `=' / `⇔' inside
        // the fn_spec's term.
        hol_fn_spec: $ => alias($._hol_term, $.hol_term),

        hol_identifier: $ => choice(
            $._hol_alphanumeric,
            $._hol_symbolic,
            $._hol_dollared,
            $._hol_op_with_sup,
            $._hol_unicode_op,
            $._hol_bracket_ident,
        ),

        // Bracket-like tokens registered as user-defined mixfix
        // delimiters in various HOL libraries — `<[', `]>' (ordinal
        // notation, quotient-lambda substitution).  These are
        // lexed as bare identifiers and don't attempt to pair;
        // libraries use them both as bracket delimiters and as
        // fixity infixes in different theories, and the ambiguity
        // is inherent (surface syntax alone can't tell them apart).
        // Application-chain-parse is close enough to survive.
        _hol_bracket_ident: $ => token(choice('<[', ']>')),

        // A binary-operator-like Unicode character carrying a
        // trailing superscript-letter modifier — `⇒ⁱ', `∧ⁱ', `⊢ⁱ',
        // `⊨ᶜ', etc.  HOL libraries register these as their own
        // mixfix operators via `set_mapped_fixity'; tree-sitter
        // can't follow that, but lexing them as one token here means
        // the surrounding term falls through to the application-chain
        // reading rather than ERROR-ing.
        //
        // Greedy lexing keeps `⇒' (no super) → 1-char binary literal
        // and `⇒ⁱ' (with super) → 2-char identifier-like token.
        _hol_op_with_sup: $ => token(new RegExp(
            `[×←-⋿⤀-⧿⨀-⫿][${HOL_SUP_LETTERS}]+`
        )),

        // Fallback for bare Unicode math-operator characters we
        // don't recognise as binary infixes — treats a lone
        // `⨾' / `⨟' / `⩾' / etc. as an identifier so the surrounding
        // term parses (as an application chain) instead of ERROR-
        // recovering into the middle of the file.  Ranges cover
        // Mathematical Operators (U+2200–U+22FF), Miscellaneous
        // Mathematical Symbols-A/B (U+2900–U+29FF), and Supplemental
        // Mathematical Operators (U+2A00–U+2AFF), minus the specific
        // characters that appear as literals in `hol_binary_term',
        // `hol_binder', `hol_annotated', etc.  Token priority is
        // -1 so that explicit literals like `∧', `∨', `⇒', `∈',
        // `∀' etc. still win when they're at the same position.
        _hol_unicode_op: $ => token(prec(-1, /[⨀-⫿⤀-⧿⌀-⏿]/)),

        // Bare `_' — wildcard pattern.  Token priority is -1 so
        // `_ident' / `_1' / `_N' consistently lex as `_hol_alpha-
        // numeric' (which has an explicit `_[cont]+' alternative
        // in its regex) rather than being greedily split into
        // wildcard-then-rest.  A lone `_' (no following identifier
        // char) still wins as wildcard.
        hol_wildcard: $ => token(prec(-1, '_')),

        // Identifier alphabets allowed:
        //   ASCII letters / digits / `_' / `''
        //   Greek (U+0370\u2013U+03FF, minus the slot that lives in \u03BB)
        //   Subscript digits (U+2080\u2013U+2089) and Latin subscript letters
        //     (U+2090\u2013U+209C) \u2014 `float\u209C', `n\u2080' lex as one name.
        //   Letterlike symbols (U+2100\u2013U+214F) \u2014 `\u2115', `\u211D', `\u2102', etc.
        //   A hand-picked set of Math-Operators-block characters that
        //     HOL uses as constants rather than operators: `\u2205', `\u221E',
        //     `\u2211', `\u220F', `\u222B', `\u2202', `\u22A4', `\u22A5', `\u22A2', `\u22A8'.  We don't open
        //     the whole U+2200\u2013U+22FF range because too much of it is
        //     already used as our own operator/binder keywords (`\u2227',
        //     `\u2228', `\u21D2', `\u2208', `\u2286', `\u2200', `\u2203', \u2026) and admitting the
        //     range in *continuation* position would silently glue
        //     `x\u2227y' into a single 3-char identifier.
        //   Latin superscript letters in identifier *continuation*
        //     only \u2014 `\u2071' (U+2071), `\u207F' (U+207F), the lowercase
        //     Modifier-Letter range `\u1D43-\u1D6A' (U+1D43\u2013U+1D6A), and the
        //     Spacing-Modifier-Letter Latin subset `\u02B0-\u02B8'
        //     (U+02B0\u2013U+02B8).  Lets HOL constants like `\u22A2\u2071' / `\u0393\u1D47'
        //     lex as a single name.
        // Superscript *digits* and uppercase Latin superscripts are
        // *not* part of the identifier: `n\u00B2' and `R\u1D40' are postfix
        // forms (see hol_postfix_term).
        //
        // A trailing `$<ident>' suffix is admitted to handle HOL's
        // qualified-name syntax: `theory$constant'.
        //
        // The `_[cont]+' alternative handles HOL's freshly-generated
        // variables (`_1', `_2', `_x', ...) — used in record
        // eliminators, case-of desugaring, and any other place the
        // pretty-printer emits a `_'-prefixed name.  Bare `_' stays
        // as `hol_wildcard'.  Combined regex so `_hol_alphanumeric'
        // remains a single token — keeps parser tables compatible
        // with keyword literals like `Theorem' / `End' / `QED'.
        _hol_alphanumeric: $ => new RegExp(
            `([${HOL_IDENT_STARTER}][${HOL_IDENT_CONT}]*|_[${HOL_IDENT_CONT}]+)${HOL_IDENT_DOLLAR_TAIL}`
        ),

        // ASCII symbolic identifier with an optional subscript /
        // superscript-letter suffix.  HOL libraries often decorate a
        // standard infix with a subscript or superscript letter to
        // mark a parallel variant — `-->ₐ', `&ₐ', `<->ₐ', `=⁺',
        // etc.  Greedy lexing keeps `-->' (no suffix → binary
        // literal) and `-->ₐ' (with subscript → 4-char identifier
        // token) distinct, just as for the Unicode-operator + super
        // case in `_hol_op_with_sup'.
        //
        // Optional leading `$' handles the HOL `$op' form that refers
        // to a fixity-registered operator as an ordinary function
        // (`$=', `$/\\', `$!' etc.), and a bare `$' is a valid token
        // on its own (HOL's function-application-at-460 operator).
        _hol_symbolic: $ => token(
            choice(
                seq(
                    // TODO Add support for ^ and `
                    repeat1(choice('#', '?', '+', '*', '/', '\\', '=', '<', '>',
                                   '&', '%', '@', '!', ':', '|', '-', '~')),
                    // Trailing modifiers: subscripts, superscript letters,
                    // `_' (parallel-variant marker: `**_', `+_').
                    repeat(new RegExp(`[${HOL_SUB}${HOL_SUP_LETTERS}_]`)),
                ),
                // Bare `$' (HOL's function-application infix at 460)
                // or `$$', `$$$', … (dollar-only names).
                repeat1('$'),
            )
        ),

        // `$'-prefixed identifier: `$' followed by *any* sequence of
        // identifier characters (symbolic, alphanumeric, comma,
        // trailing modifiers).  HOL uses this to refer to a
        // fixity-registered function by name — `$=', `$SUBSET',
        // `$/\\', `$,', `$*,', `$!', all mean "the underlying
        // function of the operator/name" as an ordinary value.
        // Since the interior can freely mix symbolic and
        // alphanumeric chars (`$*,' has both), one regex covers
        // the family.
        _hol_dollared: $ => token(new RegExp(
            `\\$[${HOL_IDENT_CONT},#?+*/\\\\=<>&%@!:|\\-~]+`
        )),

        _hol_term: $ => choice(
            $._hol_literal,
            $.hol_wildcard,
            $.hol_tuple,
            $.hol_list,
            $.hol_set,
            $._hol_application_lhs,
            $.hol_list_index,
            $.hol_list_update,
            $.hol_fmap_app,
            $.hol_fmap_update,
            $.hol_func_update,
            $.hol_record_literal,
            $.hol_record_update,
            $.hol_field_select,
            $.hol_postfix_term,
            $.hol_universe,
            $.hol_type_quotation,
            $.hol_denotation_bracket,
            $.hol_paren_op,
            $.hol_signed_inf,
            $.hol_labelled_term,
            $.hol_cond,
            $.hol_case,
            $.hol_let,
            $.hol_do,
            $.hol_binder,
            $.hol_left_unary_term,
            $.hol_binary_term,
            $.hol_annotated,
            prec(2500, seq('(', $._hol_term, ')'))
        ),

        // Type quotation `(:τ)' — a term-level literal for a type.
        // Distinguished from `(term)' (parens) and `(term : ty)'
        // (annotation) by the colon appearing immediately after `('.
        hol_type_quotation: $ => seq('(', ':', $._hol_type, ')'),

        // `(op)' — parenthesised bare unary-prefix operator.  Only
        // needed for `~' / `¬' / `-' / `&' because those chars lex
        // as literal tokens used by `hol_left_unary_term' rather
        // than as `_hol_symbolic'; without this rule the parser
        // starts a unary term needing an operand and then fails
        // at `)'.  Other operator-in-parens forms (`(+)', `(<)',
        // `(=)', `(::)', `(foo)') already parse through the
        // generic paren-around-term path with the operator as an
        // identifier atom inside.
        hol_paren_op: $ => prec(2600, seq(
            '(',
            alias(choice('~', '¬', '-', '&'), $.hol_identifier),
            ')'
        )),

        // `⟦τ⟧' — Unicode mathematical white square brackets.  HOL
        // libraries use these as a bracket-atom form (turing machine
        // encoding: `⟦UPDATE_ACT_S_TM s …⟧'; data-refinement
        // interpretation brackets; various denotational libraries).
        // Matched-bracket form: mismatches produce a local ERROR
        // rather than cascading.
        hol_denotation_bracket: $ => seq('⟦', $._hol_term, '⟧'),

        // `+∞' / `−∞' — single tokens (lexer longest-match wins over
        // `+'/`−' binary ops + identifier `∞').  HOL writers very
        // often spell `PosInf' / `NegInf' this way and our grammar
        // would otherwise want a left operand for the `+'/`−'.
        hol_signed_inf: $ => token(choice('+∞', '−∞')),

        // A HOL term prefixed with an Inductive-clause label.  Used
        // inside Inductive bodies; binds tightly to its term so
        // `[~r:] A ∧ B' parses as `([~r:] A) ∧ B'.  The high dynamic
        // precedence biases the GLR parser toward (a) the
        // close-at-A interpretation when both ∧-spans are possible
        // and (b) the clause-label-not-a-list interpretation when
        // `[name:]' appears mid-clause without an `∧' before it
        // (i.e. when a new clause is starting in a body that omits
        // the conjunction).
        hol_labelled_term: $ => prec.dynamic(10, seq(
            $.hol_clause_label,
            $._hol_term
        )),

        // Things that can stand on the left of a function application.
        // Plain identifiers, nested applications, and any tighter-binding
        // form — postfix / universe / field-select and the bracketed
        // access/update forms — all bind tighter than application (2000)
        // and so `nl³ x' is `(nl³) x', `r.fld x' is `(r.fld) x', and
        // `fm⟨k⟩ x' is `(fm⟨k⟩) x'.  A parenthesised term is also a
        // valid lhs (`(f) x', `(f x) y' for the contents of `(…)' that
        // happens to evaluate to a function), so it's included here
        // too — otherwise `(y) foo z' would mis-recover as a binary
        // operator parse on `foo'.
        _hol_application_lhs: $ => choice(
            $.hol_application,
            $.hol_identifier,
            $.antiquoted,
            $.hol_postfix_term,
            $.hol_universe,
            $.hol_field_select,
            $.hol_list_index,
            $.hol_list_update,
            $.hol_fmap_app,
            $.hol_fmap_update,
            $.hol_func_update,
            // HOL's term-level substitution notation `[t/x] M' parses
            // as application of the syntactic substitution `[t/x]'
            // (which our grammar tokenises as `hol_list' with one
            // element `t/x') to `M'.  Allowing lists on the lhs lets
            // that work; it also harmlessly admits the unusual
            // `[a;b;c] f' as application.
            $.hol_list,
            // Sets / tuples / literals on the lhs of an unknown infix
            // (`{x} division_of y', `(a, b) f') need to be valid
            // application-chain lhs too — otherwise the user-level
            // infix has no left operand and the parser ERROR-recovers
            // by dropping it.
            $.hol_set,
            $.hol_tuple,
            $._hol_literal,
            prec(2500, seq('(', $._hol_term, ')')),
        ),

        // Things that bind tighter than function application (2000):
        // postfix (2100), universe (2200), field selection (2500),
        // bracketed access/update forms, and ordinary atoms (literals,
        // identifiers, tuples, lists, sets, parens).  This is the
        // type of an application's *right* argument so that `f x²'
        // absorbs the `²' into the rhs as `f (x²)' rather than wrapping
        // the whole application in postfix as `(f x)²'.  Excluding
        // `hol_application' from `_hol_tight' is what makes that work.
        _hol_tight: $ => choice(
            $._hol_literal,
            $.hol_identifier,
            $.hol_wildcard,
            $.antiquoted,
            $.hol_tuple,
            $.hol_list,
            $.hol_set,
            $.hol_list_index,
            $.hol_list_update,
            $.hol_fmap_app,
            $.hol_fmap_update,
            $.hol_func_update,
            $.hol_record_literal,
            $.hol_record_update,
            $.hol_field_select,
            $.hol_postfix_term,
            $.hol_universe,
            $.hol_type_quotation,
            $.hol_denotation_bracket,
            $.hol_paren_op,
            $.hol_signed_inf,
            prec(2500, seq('(', $._hol_term, ')')),
        ),

        // Function application at HOL precedence 2000, left-associative.
        // Right operand is `_hol_tight' (no hol_application) so the
        // left-associative nesting is forced through the lhs:
        // `f g x' = `app(app(f, g), x)'.
        hol_application: $ => prec.left(
            2000,
            seq(
                $._hol_application_lhs,
                $._hol_tight,
            )
        ),

        // Bracketed application/update forms.  Each takes a term on the
        // left, opens one of three bracket pairs, and contains either a
        // single key term (access) or one-or-more `key ↦ value' pairs
        // separated by `;' (update).  HOL puts these at precedence 2100
        // alongside the other postfix forms (²/³/ᵀ/^=/^*/⁺), so they
        // bind tighter than function application (2000) and `f l❲i❳'
        // parses as `f (l❲i❳)' rather than `(f l)❲i❳'.
        //
        //   l❲i❳            list/array access
        //   l❲k ↦ v❳        list update
        //   l❲k ↦ v; …❳     list multi-update
        //   fm⟨k⟩           finite-map application
        //   fm⟨k ↦ v; …⟩    finite-map update
        //   f⦇k ↦ v; …⦈     function update
        hol_list_index: $ => prec.left(2100, seq(
            $._hol_tight, '❲', $._hol_term, '❳'
        )),
        hol_fmap_app: $ => prec.left(2100, seq(
            $._hol_tight, '⟨', $._hol_term, '⟩'
        )),
        hol_list_update: $ => prec.left(2100, holBracketUpdate($, '❲', '❳')),
        hol_fmap_update: $ => prec.left(2100, holBracketUpdate($, '⟨', '⟩')),
        hol_func_update: $ => prec.left(2100, holBracketUpdate($, '⦇', '⦈')),

        // Record literal: <| f := v; f2 updated_by g; … |>
        // Record update : r with <| … |>
        // Each field uses either `:=' (replace) or `updated_by'
        // (apply a function to the current field value); multiple
        // fields are `;'-separated.
        hol_record_literal: $ => seq(
            '<|',
            mkSepBy1(';', $.hol_record_field),
            optional(';'),
            '|>'
        ),
        hol_record_field: $ => seq(
            alias($._alphaAlphaNumeric_ident, $.hol_record_field_name),
            choice(':=', 'updated_by'),
            $._hol_term
        ),
        // `r with <|fld1 := v1; …|>' or the abbreviated single-field
        // form `r with fld := v' / `r with fld updated_by f' (no
        // `<|…|>' braces).  Both compile to the same shape.
        hol_record_update: $ => prec.left(2000, seq(
            $._hol_application_lhs,
            'with',
            choice($.hol_record_literal, $.hol_record_field),
        )),

        // Postfix operators at HOL precedence 2100 — bind tighter than
        // function application (2000), looser than universe (2200) and
        // field selection (2500).  Stack left-associatively so `x²ᵀ'
        // parses as `(x²)ᵀ'.
        //   ²  ³        — exponentiation
        //   ᵀ           — relinv  (relation inverse)
        //   ^=          — EQC
        //   ^*  ꙳       — RTC (reflexive-transitive closure)
        //   ^+  ⁺       — TC (transitive closure)
        hol_postfix_term: $ => {
            const ops = ['²', '³', 'ᵀ', '^=', '^*', '꙳', '^+', '⁺'];
            return choice(...ops.map(op =>
                prec.left(2100, seq(
                    field('term', $._hol_tight),
                    field('operator', op),
                ))
            ));
        },

        // Universe prefix at HOL precedence 2200.  `𝕌 ty' / `univ ty'
        // is the universe set of a type.  Operand is `_hol_tight'
        // (no hol_application), matching HOL's "operand must bind
        // tighter than 2200" rule.
        hol_universe: $ => prec(2200, seq(
            field('operator', choice('𝕌', 'univ')),
            field('term', $._hol_tight),
        )),

        // Field selection `r.fld' at HOL precedence 2500 (tightest).
        // The `.field' part is one lexical token (token.immediate) so it
        // only matches when the dot and field name are adjacent, with
        // no intervening whitespace.  Binder dots like `∀x. P x' (with
        // a space — or even without, since the following keyword/symbol
        // breaks the immediate token) therefore can't be mistaken for
        // field selection.  Left-associative so `r.a.b' = `(r.a).b'.
        hol_field_select: $ => prec.left(2500, seq(
            field('term', $._hol_tight),
            field('dot_field', $.hol_dot_field),
        )),

        hol_dot_field: $ => token.immediate(
            new RegExp('\\.' + alphaAlphaNumericIdentRE)
        ),

        hol_cond: $ => prec(
            70,
            seq('if', $._hol_term, 'then', $._hol_term, 'else', $._hol_term)
        ),

        // `let v1 = e1; v2 = e2; … in body' — HOL term-level let with
        // multi-binding.  Bindings are separated by either `;' or the
        // keyword `and' (the latter is HOL's parallel-let form:
        // `let X = e1 and Y = e2 in body' evaluates `e1' and `e2'
        // against the same outer scope, whereas `;' cascades bindings
        // left-to-right).  Both spellings compile to the same shape.
        // HOL precedence is 8 (very loose) so the body extends as
        // far as the surrounding context allows (typically to the
        // next outer `;', `End', `QED', `)', etc.).
        //
        // LHS of each binding is a pattern: just an identifier in the
        // common case (`M0 = principal_hnf M'), but HOL also accepts
        // tuple patterns like `(x, y) = pair_expr'.
        hol_let: $ => prec(8, seq(
            'let',
            $.hol_let_binding,
            repeat(seq(choice(';', 'and'), $.hol_let_binding)),
            optional(choice(';', 'and')),
            'in',
            $._hol_term,
        )),

        // A let binding is just `LHS = RHS'.  Like `hol_fn_spec', we
        // don't distinguish this from a general `_hol_term' with a
        // binary `=' inside — the shape is the same, and downstream
        // consumers can identify the `=' boundary in the resulting
        // binary_term.
        hol_let_binding: $ => alias($._hol_term, $.hol_term),

        // HOL's monadic `do … od' notation (from monadLib).  We
        // recognise the keyword shell — `do' / `od' and the `;'-
        // separated statement list — but parse each statement as a
        // plain `_hol_term'.  The lexer prefers the symbolic-vid
        // reading of `<-' / `<<-' over a literal token, so the
        // monadic-bind structure shows up as a curried application
        // `x <- m' = `app(app(x, <-), m)' inside `hol_do_term'.
        // That's structurally wrong but doesn't ERROR, which keeps
        // downstream font-lock / navigation working.
        hol_do: $ => seq(
            'do',
            mkSepBy1(';', alias($._hol_term, $.hol_do_term)),
            optional(';'),
            'od',
        ),

        hol_case: $ => prec.right(
            1,
            seq(
                'case',
                alias($._hol_term, $.hol_term),
                'of',
                optional('|'), mkSepBy1('|', $.hol_match)
            )
        ),

        // Case-of branch: pattern `=>' body.  HOL doesn't distinguish
        // patterns from terms syntactically, so the LHS is `_hol_term'
        // — including bare cons `x::xs', constructor application
        // `SOME x', tuples, lists, wildcards, and everything else.
        hol_match: $ => seq(
            alias($._hol_term, $.hol_term),
            // `=>' is the modern HOL convention; `->' is an older
            // alternative still used by (e.g.) `examples/dev/AES/'.
            choice("=>", "->"),
            alias($._hol_term, $.hol_term),
        ),

        // A binder variable is one of:
        //   • a plain name (optionally annotated / restricted)
        //   • a parenthesised bvar   `(x)', `(x:'a)', `(x::s)'
        //   • a `,'-separated bvar tuple — `λ(x, y). body' is the
        //     standard HOL pair-destructuring shape, semantically
        //     `λp. let (x, y) = p in body'.  Same form nests:
        //     `λ(x, (y, z)). …'.
        //   • a space-separated group of names with a shared type
        //     annotation — `!(r s):'a field. …' means `!r:'a field.
        //     !s:'a field. …'.  The names are all plain
        //     alphanumeric; only the shared annotation is optional.
        hol_bvar: $ => choice(
            $._hol_bvar,
            seq('(', $._hol_bvar, ')'),
            seq('(', $.hol_bvar, ',', mkSepBy1(',', $.hol_bvar), ')'),
            seq(
                '(',
                alias($._hol_alphanumeric, $.hol_alphanumeric),
                repeat1(alias($._hol_alphanumeric, $.hol_alphanumeric)),
                ')',
                optional(seq(':', $._hol_type)),
            ),
        ),

        // A bvar is a name, optionally annotated with a type (`x:'a')
        // or restricted to a set/measure (`x::s' — HOL's restricted-
        // quantification syntax, `!x::s. P x' desugars to
        // `!x. x ∈ s ⇒ P x'; works with any binder — !, ?, AE, etc.).
        _hol_bvar: $ => seq(
            alias($._hol_alphanumeric, $.hol_alphanumeric),
            optional(choice(
                seq(':', $._hol_type),
                seq('::', alias($._hol_term, $.hol_term)),
            ))
        ),

        // Permanently borrowed (and adapted) from tree-sitter/tree-sitter-c,
        // which is released under the MIT license.
        hol_binder: $ => {
            const table = [
                // Core boolean / hilbert / integer binders
                'OLEAST', 'oleast', 'LEAST', 'LEAST_INT', 'some',
                '?!!', '∃!', '?!', '∃', '?', '∀',
                '!', '@', 'λ', '\\',
                // Option — "at most one" quantifier
                'EXISTS_AT_MOST_ONE',
                // n-bit — finite Cartesian product
                'FCP',
                // Measure / probability theory
                'AE',
                // CakeML-style spec binders
                'POSTv', 'SEP_EXISTS',
                // Separation-logic library binders
                'asl_exists', 'asl_forall', 'COND_PROP___EXISTS',
                // miller/prob — probably / possibly (symbolic)
                '!*', '?*',
                // Tree-sitter grammars are static, so this list can't
                // grow at parse time; add a name here when a new
                // library introduces a common one (POSTve / POSTe /
                // POSTvd / etc. are obvious neighbours).
            ];

            return choice(...table.map(
                (binder) => {
                    return seq(
                        binder,
                        repeat1($.hol_bvar),
                        '.',
                        $._hol_term
                    )
            }));
        },

        // Prefix unary operators, level 900 in HOL term_grammar:
        //   & (numeric coercion), - (numeric negation), ¬ / ~ (negation)
        hol_left_unary_term: $ => {
            const table = [
                ['&', 900],
                ['-', 900],
                ['¬', 900],
                ['~', 900],
            ];

            return choice(...table.map(
                ([operator, precedence]) => {
                    return prec(
                        precedence,
                        seq(
                            field('operator', operator),
                            field('term', $._hol_term),
                        )
                    );

            }));
        },

        // Binary infix operators with HOL precedences (from term_grammar()).
        // Numbers match HOL's canonical levels — higher binds tighter.
        // Associativity: 'L' left, 'R' right, 'N' non-associative (modelled
        //   as prec.left for tree-sitter's parser).
        hol_binary_term: $ => {
            const table = [
                // 50 R — pair constructor.  HOL treats `,' as a
                // standard infix at this precedence; `a, b' (with or
                // without parens) is `(,) a b'.
                [',', 50, 'R'],
                // 80 — :-
                [':-', 80, 'N'],
                // 100 — biconditionals / map-arrow
                ['↦', 100, 'N'],
                ['|->', 100, 'N'],
                ['⇎', 100, 'N'],
                ['<=/=>', 100, 'N'],
                ['⇔', 100, 'N'],
                ['<=>', 100, 'N'],
                // Monadic bind / let-bind from HOL's `do … od'.  Just
                // ordinary infixes here — the same shape as `<=' etc.
                // The string literals win over the SML symbolic-vid
                // regex by tree-sitter's longest-match + literal-prec
                // rules, so `x <- m' parses as `hol_binary_term(x, <-, m)'.
                ['<-', 100, 'R'],
                ['<<-', 100, 'R'],
                // 200 R — implication
                ['⇨ᵣ', 200, 'R'],
                ['⇒', 200, 'R'],
                ['==>', 200, 'R'],
                // 300 R — disjunction
                ['∨', 300, 'R'],
                ['\\\/', 300, 'R'],
                // 310 L — pipe-into
                [':>', 310, 'L'],
                // 320 N — UPDATE
                ['=+', 320, 'N'],
                // 400 R — conjunction
                ['⅋ᵣ', 400, 'R'],
                ['∧', 400, 'R'],
                ['\/\\', 400, 'R'],
                // 425 N — set/relation membership
                ['refines', 425, 'N'],
                ['partitions', 425, 'N'],
                ['equiv_on', 425, 'N'],
                ['∉', 425, 'N'],
                ['NOTIN', 425, 'N'],
                ['∈', 425, 'N'],
                ['IN', 425, 'N'],
                // 450 N — ordering / equality / subset family
                ['≼', 450, 'N'],
                ['<<=', 450, 'N'],
                ['PERMUTES', 450, 'N'],
                ['HAS_SIZE', 450, 'N'],
                ['⊂', 450, 'N'],
                ['PSUBSET', 450, 'N'],
                ['⊆', 450, 'N'],
                ['SUBSET', 450, 'N'],
                ['≥', 450, 'N'],
                ['>=', 450, 'N'],
                ['≤', 450, 'N'],
                ['<=', 450, 'N'],
                ['>', 450, 'N'],
                ['<', 450, 'N'],
                ['⊆ᵣ', 450, 'N'],
                ['RSUBSET', 450, 'N'],
                ['≠', 450, 'N'],
                ['<>', 450, 'N'],
                ['=', 450, 'N'],
                // 460 R — $ function-application
                //   `with`, `:=`, `updated_by` also live here in HOL but
                //   are covered by dedicated record syntax forms above.
                ['$', 460, 'R'],
                // 480 L — list-concat
                ['⧺', 480, 'L'],
                ['++', 480, 'L'],
                ['+++', 480, 'L'],
                // 490 R — cons / pair-rel / lex
                ['::', 490, 'R'],
                ['CONS', 490, 'R'],
                ['INSERT', 490, 'R'],
                ['###', 490, 'R'],
                ['PAIR_REL', 490, 'R'],
                ['LEX', 490, 'R'],
                ['##', 490, 'R'],
                ['===>', 490, 'R'],
                // 500 L — additive / set union / diff
                // `..' is the integer-range operator from pred_setLib,
                // used inside `{m..n}' range-set notation.
                ['..', 500, 'L'],
                // 500 L — bracket-flanked comparators from
                // `examples/imperative' — HOL libraries do sometimes
                // put a `[' or `]' at the start / end of a symbolic
                // infix; can't lex them via `_hol_symbolic' because
                // the brackets are already list delimiters, so
                // pin them explicitly.
                ['[=.', 500, 'L'],
                ['[<>.', 500, 'L'],
                ['⊔', 500, 'L'],
                ['<+>', 500, 'L'],
                ['DELETE', 500, 'L'],
                ['DIFF', 500, 'L'],
                ['∪', 500, 'L'],
                ['UNION', 500, 'L'],
                ['<*>', 500, 'L'],
                ['−', 500, 'L'],
                ['-', 500, 'L'],
                ['+', 500, 'L'],
                ['∪ᵣ', 500, 'L'],
                ['RUNION', 500, 'L'],
                // 600 L — multiplicative / set intersection
                ['∩', 600, 'L'],
                ['INTER', 600, 'L'],
                ['\\\\', 600, 'L'],
                ['DIV', 600, 'L'],
                ['MOD', 600, 'L'],
                ['/', 600, 'L'],
                ['*', 600, 'L'],
                ['∩ᵣ', 600, 'L'],
                ['RINTER', 600, 'L'],
                // 601 R — cross / pair product
                ['×', 601, 'R'],
                ['CROSS', 601, 'R'],
                ['⊗', 601, 'R'],
                ['*,', 601, 'R'],
                // 650 L — %%
                ['%%', 650, 'L'],
                // 700 R — exponentiation
                ['**', 700, 'R'],
                ['EXP', 700, 'R'],
                // 750 R — arrow
                ['-->', 750, 'R'],
                // 800 R — function composition
                ['∘ᵣ', 800, 'R'],
                ['O', 800, 'R'],
                ['∘', 800, 'R'],
                ['o', 800, 'R'],
                // 2000 L — FCP bit-select `w ' n' (fcpTheory), same prec
                // as function application.  Whitespace matters at the
                // lexer level: `x'' ' n' is (identifier-with-primes ' n),
                // but a bare `'` between tokens is the infix.
                ["'", 2000, 'L'],
            ];

            return choice(...table.map(
                ([operator, precedence, associativity]) => {
                    const rule = seq(
                        field('left', $._hol_term),
                        field('operator', operator),
                        field('right', $._hol_term),
                    );

                    switch (associativity) {
                    case 'L':
                        return prec.left(precedence, rule);
                    case 'R':
                        return prec.right(precedence, rule);
                    default:
                        // TODO Deal with non-associativity properly
                        return prec.left(precedence, rule);
                    }
            }));
        },

        hol_annotated: $ => prec(
            899,
            seq($._hol_term, ':', $._hol_type)
        ),

        _hol_type: $ => choice(
            $.hol_atomic_type,
            // Antiquotation `^ty' / `^(ty)' is valid in type
            // positions too — used pervasively in `src/quotient/'
            // to splice a computed type into a Theorem body's type
            // annotation (`[] : ^subs').
            $.antiquoted,
            $.hol_list_ty,
            $.hol_tycon_app,
            $.hol_tycon_app_tuple,
            $.hol_bracket_ty,
            $.hol_fun_ty,
            $.hol_prod_ty,
            $.hol_cart_ty,
            $.hol_sum_ty,
            $.hol_finmap_ty,
            seq('(', $._hol_type, ')')
        ),

        // HOL type precedences (from tighter to looser):
        //
        //   200   TY '[' TY ']'          bracketed type parameter, postfix
        //   100   TY tycon               postfix unary tycon app (`'a list',
        //                                `('a, 'b) fmap')
        //    80   TY 'list'              (special-cased for the ubiquitous
        //                                `list' tycon; same prec class as
        //                                any other postfix tycon)
        //    70   TY '#'  TY             product      (R-assoc)
        //    60   TY '**' TY             cartesian    (R-assoc)
        //    60   TY '+'  TY             sum          (R-assoc)
        //    50   TY '|->' TY            finmap       (R-assoc)
        //    50   TY '->' TY             function     (R-assoc)
        //
        // Right-associativity so `'a -> 'b -> 'c' means `'a -> ('b -> 'c)'
        // and `'a # 'b # 'c' means `'a # ('b # 'c)' — matching HOL's
        // conventional reading.

        // `'a['b]' — bracketed type-parameter form (used by n-bit /
        // FCP: `'a['b]' is a Cartesian type-family application).
        // Postfix at prec 200, higher than any binary type operator,
        // so `'a['b] # 'c' parses as `('a['b]) # 'c'.
        hol_bracket_ty: $ => prec.left(200, seq(
            $._hol_type,
            '[',
            $._hol_type,
            ']'
        )),

        hol_list_ty: $ => prec.left(100, seq($._hol_type, 'list')),

        // `'a foo' or `bar foo' — postfix unary tycon application.
        hol_tycon_app: $ => prec.left(100, seq(
            $._hol_type,
            alias($._hol_alphanumeric, $.hol_tycon)
        )),

        // `('a, 'b, …) foo' — multi-argument tycon application.
        hol_tycon_app_tuple: $ => prec.left(100, seq(
            '(',
            mkSepBy2(',', $._hol_type),
            ')',
            alias($._hol_alphanumeric, $.hol_tycon)
        )),

        hol_prod_ty:   $ => prec.right(70, seq($._hol_type, '#',   $._hol_type)),
        hol_cart_ty:   $ => prec.right(60, seq($._hol_type, '**',  $._hol_type)),
        hol_sum_ty:    $ => prec.right(60, seq($._hol_type, '+',   $._hol_type)),
        hol_finmap_ty: $ => prec.right(50, seq($._hol_type, '|->', $._hol_type)),
        hol_fun_ty:    $ => prec.right(50, seq($._hol_type, '->',  $._hol_type)),

        hol_atomic_type: $ => choice(
            'num',
            'string',
            // BUG? Allows 'f'oo as a type variable
            /\'[a-zA-Z\u0370-\u03BA\u03BC-\u03FF0-9\'_]+/,
            // Numeric type literals \u2014 `:0', `:5', `:52', `:1023', etc.
            // HOL uses these as the type-level arguments of fixed-width
            // word and float tycons (`(52,11) float', `:32 word').
            /[0-9]+/,
            $._hol_alphanumeric
        ),

        hol_tuple: $ => seq(
            '(',
            optional(mkSepBy2(',', $._hol_term)),
            ')'
        ),

        // `[e1; e2; …]' — list literal.  Allows a trailing `;'
        // after the last element (HOL's uniform relaxation for
        // enclosed list forms).
        hol_list: $ => seq(
            '[',
            optional(seq(mkSepBy1(';', $._hol_term), optional(';'))),
            ']'
        ),

        // Three set-notation shapes:
        //   `{ e1; e2; … }'        — set literal
        //   `{ e | P }'            — set comprehension (gspec)
        //   `{ e | vs | P }'       — set comprehension with explicit
        //                            variable list (gspec2)
        // The comprehension forms admit a tuple-pattern as the
        // term `e' — `{ a, b | P }' and `{ i, j | i IN s /\ j IN t i }'
        // are standard.  This works because `,' is a standard infix
        // in `hol_binary_term' at HOL prec 50 R.  The literal form
        // allows a trailing `;' on the last element.
        hol_set: $ => choice(
            seq('{',
                optional(seq(mkSepBy1(';', $._hol_term), optional(';'))),
                '}'),
            seq('{', $._hol_term, '|', $._hol_term, '}'),
            seq('{', $._hol_term, '|', $._hol_term, '|', $._hol_term, '}'),
        ),

        _hol_literal: $ => choice(
            $.hol_number,
            $.hol_string,
            $.hol_character,
            $.hol_true,
            $.hol_false
        ),

        hol_true: $ => 'T',

        hol_false: $ => 'F',

        // Decimal / hex / binary numerals with an optional one-letter
        // HOL type suffix.  Common suffixes:
        //   `w' — word (wordsLib)
        //   `i' — int  (integerLib)
        //   `r' — real (realLib)
        //   `q' — rational (ratLib)
        //   `n' — explicit num annotation (used in DECIDE proofs)
        // Hex/binary forms are `0xFF', `0b101' and may also carry a
        // suffix.  Embedded underscores are allowed for grouping
        // (`1_000', `0xFFFF_FFFF').
        hol_number: $ => choice(
            /0x[0-9a-fA-F][0-9a-fA-F_]*[ainqrw]?/,
            /0b[01][01_]*[ainqrw]?/,
            /\d[\d_]*[ainqrw]?/,
        ),

        // https://gist.github.com/cellularmitosis/6fd5fc2a65225364f72d3574abd9d5d5
        // TODO These regexes may be incorrect; alternatives were posted on
        //   Discord
        hol_string: $ => /\"([^\"\\]|\\.)*\"/,

        // HACK Does not make sure the string is of length 1
        hol_character: $ => /#\"([^\"\\]|\\.)*\"/
    },
});
