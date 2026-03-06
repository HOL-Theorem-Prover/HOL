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

const alphaNumericIdentSuffixRE = /[A-Za-z0-9_']*/.source;
const alphaAlphaNumericIdentRE = `[A-Za-z]${alphaNumericIdentSuffixRE}`;
const primeAlphaNumericIdentRE = `'${alphaNumericIdentSuffixRE}`;
const symbolicIdentRE = /[!%&$#+\-/:<=>?@\\~`^|*]+/.source;

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
        [$.hol_pcons, $.hol_ptuple]
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

        local_dec: $ => seq(
            'local',
            repeat(choice(';', field('dec', $._dec))),
            'in',
            repeat(choice(';', field('body', $._dec))),
            'end',
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
            repeat(choice(';', field('body', $._strdec))),
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
            $.hol_theorem_with_proof
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

        quoted_term: $ => seq('“', $._hol_term, '”'),

        quoted_type: $ => seq('“', ':', $._hol_type, '”'),

        _quote_content: $ => choice(
            alias(/([^\^`‘’]|\^\^|\^\`)+/, $.quoted),
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
            'Datatype:',
            $.hol_binding,
            'End'
        ),

        hol_theorem_with_proof: $ => seq(
            'Theorem',
            alias($._alphaAlphaNumeric_ident, $.hol_thmname),
            optional($.hol_attributes),
            ':',
            alias($._hol_term, $.hol_thmstmt),
            'Proof',
            $.tactic,
            'QED'
        ),

        // TODO Unsure about this (in particular THEN)
        _atomic_tactic: $ => choice(
            $._exp,
            seq('(', $.THEN, ')')
        ),

        tactic: $ => choice(
            $._atomic_tactic,
            $.THEN
        ),

        THEN: $ => prec.left(mkSepBy2('\\\\', $._atomic_tactic)),

        hol_binding: $ => seq(
            $.hol_identifier,
            '=',
            $.hol_constructor
        ),

        hol_constructor: $ => mkSepBy1('|', $.hol_clause),

        hol_clause: $ => seq(
            $.hol_identifier,
            repeat($._hol_ty_spec)
        ),

        _hol_ty_spec: $ => choice(
            $.hol_atomic_type,
            seq('(', $._hol_type ,')')
        ),

        hol_fn_spec: $ => choice(
            mkSepBy1('∧', choice($.hol_eqn, seq('(', $.hol_eqn, ')'))),
            mkSepBy1('\/\\', choice($.hol_eqn, seq('(', $.hol_eqn, ')')))
        ),

        // TODO Sort out precedence levels properly
        // NOTE hol_eqn has higher precedence to avoid conjunction being
        //   "consumed" by the term
        hol_eqn: $ => prec(450, seq(
            $.hol_identifier,
            repeat($.hol_pat),
            '=',
            alias($._hol_term, $.hol_term))),

        hol_pat: $ => choice(
            $._hol_pat,
            seq('(',
                $._hol_pat,
                ':',
                alias($._hol_ty_spec, $.hol_pannotation),
                ')'
               )
        ),

        _hol_pat: $ => choice(
            $.hol_variable,
            $.hol_wildcard,
            $._hol_literal,
            $.hol_cname_alphanumeric,
            $.hol_pcons,
            $.hol_ptuple,
            $.hol_plist,
            seq('(', $.hol_cname_alphanumeric, repeat1($.hol_pat), ')')
        ),

        hol_pcons: $ => seq('(', mkSepBy1('::', $.hol_pat), ')'),

        hol_ptuple: $ => seq('(', mkSepBy1(',', $.hol_pat), ')'),

        hol_plist: $ => seq(
            '[',
            mkSepBy(';', $.hol_pat),
            ']'
        ),

        hol_identifier: $ => choice(
            $._hol_alphanumeric,
            $._hol_symbolic
        ),

        hol_wildcard: $ => '_',

        // TODO Missing unicode subscript and superscript
        // TODO Make this more readable?
        _hol_alphanumeric: $ => /[a-zA-Z\u0370-\u03BA\u03BC-\u03FF][a-zA-Z\u0370-\u03BA\u03BC-\u03FF0-9\'_]*/,

        _hol_symbolic: $ => token(
            choice(
                // TODO Add support for ^ and `
                repeat1(choice('#', '?', '+', '*', '/', '\\', '=', '<', '>',
                               '&', '%', '@', '!', ':', '|', '-')),
                repeat1('$')
            )
        ),

        // HACK trying to disambiguate variables and constructors
        // start with uppercase letter
        // TODO Maybe just get rid of this and hol_variable
        hol_cname_alphanumeric: $ => /[A-Z][a-zA-Z\u0370-\u03BA\u03BC-\u03FF0-9\'_]*/,

        // start with lowercase letter
        hol_variable: $ => /[a-z][a-zA-Z\u0370-\u03BA\u03BC-\u03FF0-9\'_]*/,

        _hol_term: $ => choice(
            $._hol_literal,
            $.hol_tuple,
            $.hol_list,
            $.hol_set,
            $._hol_application_lhs,
            $.hol_cond,
            $.hol_case,
            $.hol_binder,
            $.hol_left_unary_term,
            $.hol_binary_term,
            $.hol_annotated,
            prec(2500, seq('(', $._hol_term, ')'))
        ),

        // TODO Look into applying this pattern
        //   https://github.com/tree-sitter/tree-sitter-c/blob/6c7f459ddc0bcf78b615d3a3f4e8fed87b8b3b1b/grammar.js#L1034
        //   term_grammar: binders, binary expressions, ...

        _hol_application_lhs: $ => choice(
            $.hol_application,
            $.hol_identifier,
        ),

        // TODO Define this using repeat1 somehow
        hol_application: $ => prec.left(
            2000,
            seq(
                $._hol_application_lhs,
                choice($._hol_application_lhs, $._hol_term)
            )
        ),

        hol_cond: $ => prec(
            70,
            seq('if', $._hol_term, 'then', $._hol_term, 'else', $._hol_term)
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

        // TODO Feels hacky
        _hol_pcon_nopare: $ => seq($.hol_cname_alphanumeric, repeat1($.hol_pat)),

        hol_match: $ => seq(
            alias(
                choice(
                    $._hol_pat,
                    $._hol_pcon_nopare
                ),
                $.hol_pat
            ),
            "=>",
            alias($._hol_term, $.hol_term),
        ),

        // TODO find better names for (_)hol_bvar
        hol_bvar: $ => choice(
            seq('(', $._hol_bvar, ')'),
            $._hol_bvar,
        ),

        _hol_bvar: $ => seq(
            alias($._hol_alphanumeric, $.hol_alphanumeric),
            optional(seq(':', $._hol_type))
        ),

        // Permanently borrowed (and adapted) from tree-sitter/tree-sitter-c,
        // which is released under the MIT license.
        hol_binder: $ => {
            const table = [
                'OLEAST', 'LEAST', 'some', '?!!', '∃!', '?!', '∃', '?', '∀',
                '!', '@', 'λ', '\\'
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

        hol_left_unary_term: $ => {
            const table = [
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

        hol_binary_term: $ => {
            const table = [
                ['⇎', 100, 'N'],
                ['<=/=>', 100, 'N'],
                ['<=>', 100, 'N'],
                ['⇔', 100, 'N'],
                ['==>', 200, 'L'],
                ['⇒', 200, 'L'],
                ['\\\/', 300, 'R'],
                ['∨', 300, 'R'],
                ['\/\\', 400, 'R'],
                ['∧', 400, 'R'],
                ['∉', 400, 'N'],
                ['NOTIN', 400, 'N'],
                ['∈', 400, 'N'],
                ['IN', 400, 'N'],
                ['≼', 450, 'N'],
                ['<<=', 450, 'N'],
                ['PERMUTES', 450, 'N'],
                ['HAS_SIZE', 450, 'N'],
                ['⊂', 450, 'N'],
                ['PSUBSET', 450, 'N'],
                ['⊆', 450, 'N'],
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
                ['$', 460, 'R'],
                ['::', 490, 'R'],
                ['INSERT', 490, 'R'],
                ['+', 500, 'L'],
                ['o', 800, 'R']
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
            $.hol_list_ty,
            $.hol_fun_ty,
            seq('(', $._hol_type, ')')
        ),

        hol_list_ty: $ => seq($._hol_type, 'list'),

        hol_fun_ty: $ => prec.right(
            50,
            seq($._hol_type, '->', $._hol_type)
        ),

        hol_atomic_type: $ => choice(
            'num',
            'string',
            // BUG? Allows 'f'oo as a type variable
            /\'[a-zA-Z\u0370-\u03BA\u03BC-\u03FF0-9\'_]+/,
            $._hol_alphanumeric
        ),

        hol_tuple: $ => seq(
            '(',
            optional(mkSepBy2(',', $._hol_term)),
            ')'
        ),

        hol_list: $ => seq(
            '[',
            mkSepBy(';', $._hol_term),
            ']'
        ),

        hol_set: $ => seq(
            '{',
            mkSepBy(';', $._hol_term),
            '}'
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

        hol_number: $ => /\d[\d_]*/,

        // https://gist.github.com/cellularmitosis/6fd5fc2a65225364f72d3574abd9d5d5
        // TODO These regexes may be incorrect; alternatives were posted on
        //   Discord
        hol_string: $ => /\"([^\"\\]|\\.)*\"/,

        // HACK Does not make sure the string is of length 1
        hol_character: $ => /#\"([^\"\\]|\\.)*\"/
    },
});
