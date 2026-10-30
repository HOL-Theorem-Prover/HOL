// Adapted tree-sitter-sml by Matthew Fluet, released under the MIT license.
#include <wctype.h>
#include <string.h>
#include <tree_sitter/parser.h>

enum TokenType {
  BLOCK_COMMENT,
  LINE_COMMENT,
  BOL_PROOF,
  BOL_QED,
};

// BOL-anchored HOL block keywords.  When one of these tokens is
// listed as valid in the current parser state, we consume the word
// at the current position only if (a) we're at column 0 (no leading
// whitespace on the line) and (b) the word matches the keyword text
// exactly.  This anchors block delimiters at BOL so a greedy term or
// tactic parse can't silently absorb them as identifiers.
//
// Note the limit of that guarantee: tree-sitter only consults the
// external scanner for tokens valid in the *current* parse state.
// While a declaration body is mid-construct -- a binder still waiting
// for its `.', an unterminated `let' -- no block delimiter is valid
// lookahead, `valid_symbols' has none of these set, and the term goes
// on to swallow a column-0 `End' / `Theorem' / `Proof' / `QED' as an
// ordinary name.  Error recovery then blames the whole region, so one
// truncated declaration can cost its well-formed neighbours their
// node types (and with them their font-lock and `forward-sexp').
//
// Closing that hole means the scanner has to own `_hol_alphanumeric'
// outright, since an external token that declines falls back to its
// internal rule.  That was tried and abandoned: an external token
// outranks every internal one, so owning identifiers means declining
// every keyword, and HOL code genuinely uses `op', `as', `rec', `fn',
// `type', `raise', `val' and `T' as term variables -- re-admitting
// them at parser level conflicts with the very constructs they open.
// tree-sitter's `reserved' words (CLI 0.24+) are the clean fix; the
// generated parser here is from 0.20.8, which ignores the key.
static const struct { const char* text; int len; enum TokenType tok; } BOL_KEYWORDS[] = {
  {"Proof", 5, BOL_PROOF},
  {"QED",   3, BOL_QED},
};
static const int BOL_KEYWORD_COUNT = 2;

static bool is_ident_cont(int32_t c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
         (c >= '0' && c <= '9') || c == '_' || c == '\'';
}

static bool scan_bol_keyword(TSLexer *lexer, const bool *valid_symbols) {
  bool any_wanted = false;
  for (int i = 0; i < BOL_KEYWORD_COUNT; i++) {
    if (valid_symbols[BOL_KEYWORDS[i].tok]) { any_wanted = true; break; }
  }
  if (!any_wanted) return false;
  if (lexer->get_column(lexer) != 0) return false;

  char buf[32];
  int len = 0;
  while (len < 30 && !lexer->eof(lexer) && is_ident_cont(lexer->lookahead)) {
    buf[len++] = (char)lexer->lookahead;
    lexer->advance(lexer, false);
  }
  buf[len] = 0;

  for (int i = 0; i < BOL_KEYWORD_COUNT; i++) {
    if (valid_symbols[BOL_KEYWORDS[i].tok] &&
        len == BOL_KEYWORDS[i].len &&
        strcmp(buf, BOL_KEYWORDS[i].text) == 0) {
      lexer->result_symbol = BOL_KEYWORDS[i].tok;
      return true;
    }
  }
  return false;
}

void * tree_sitter_holscript_external_scanner_create() {
  return NULL;
}

void tree_sitter_holscript_external_scanner_destroy(__attribute__ ((unused)) void *payload) {
  return;
}

unsigned tree_sitter_holscript_external_scanner_serialize(__attribute__ ((unused)) void *payload, __attribute__ ((unused)) char *buffer) {
  return 0;
}

void tree_sitter_holscript_external_scanner_deserialize(__attribute__ ((unused)) void *payload, __attribute__ ((unused)) const char *buffer, __attribute__ ((unused)) unsigned length) {
  return;
}

bool tree_sitter_holscript_external_scanner_finish_line_comment(TSLexer *lexer) {
  while (true) {
    if (lexer->eof(lexer)) return false;
    switch (lexer->lookahead) {
    case '\n':
      lexer->advance(lexer, false);
      return true;
    case '\r':
      lexer->advance(lexer, false);
      if (!lexer->eof(lexer) && lexer->lookahead == '\n') {
        lexer->advance(lexer, false);
      }
      return true;
    default:
      lexer->advance(lexer, false);
      continue;
    }
  }
}

bool tree_sitter_holscript_external_scanner_finish_block_comment(TSLexer *lexer, bool line_comment) {
  unsigned depth = 1;
  while (true) {
    if (lexer->eof(lexer)) return false;
    switch (lexer->lookahead) {
    case '(':
      lexer->advance(lexer, false);
      if (lexer->eof(lexer)) return false;
      if (lexer->lookahead == '*') {
        lexer->advance(lexer, false);
        if (lexer->eof(lexer)) return false;
        if (line_comment && lexer->lookahead == ')') {
          lexer->advance(lexer, false);
          if (tree_sitter_holscript_external_scanner_finish_line_comment(lexer)) {
            continue;
          } else {
            return false;
          }
        } else {
          depth += 1;
          continue;
        }
      } else {
        continue;
      };
    case '*':
      lexer->advance(lexer, false);
      if (lexer->eof(lexer)) return false;
      if (lexer->lookahead == ')') {
        lexer->advance(lexer, false);
        depth -= 1;
        if (depth == 0) {
          return true;
        } else {
          continue;
        }
      } else {
        continue;
      };
    default:
      lexer->advance(lexer, false);
      continue;
    }
  }
}

// Sets *consumed once the leading `(' has been eaten.  The lexer
// cannot be rewound, so after that point a failure must abort the
// whole external scan: any sub-scanner that ran next would have its
// token silently extended backwards over the stray `('.  Harmless
// while comments are the only thing scanned here, but it is a trap
// for anything added later.
bool tree_sitter_holscript_external_scanner_scan_comment(TSLexer *lexer, bool block_comment, bool line_comment, bool *consumed) {
  while (!lexer->eof(lexer) && iswspace(lexer->lookahead)) {
    lexer->advance(lexer, true);
  }
  if (lexer->eof(lexer)) return false;
  if (lexer->lookahead == '(') {
    lexer->advance(lexer, false);
    *consumed = true;
    if (lexer->eof(lexer)) return false;
    if (lexer->lookahead == '*') {
      lexer->advance(lexer, false);
      if (lexer->eof(lexer)) return false;
      if (line_comment && lexer->lookahead == ')') {
        lexer->advance(lexer, false);
        if (tree_sitter_holscript_external_scanner_finish_line_comment(lexer)) {
          lexer->result_symbol = LINE_COMMENT;
          return true;
        } else {
          return false;
        }
      } else if (block_comment) {
        if (tree_sitter_holscript_external_scanner_finish_block_comment(lexer, line_comment)) {
          lexer->result_symbol = BLOCK_COMMENT;
          return true;
        } else {
          return false;
        }
      } else {
        return false;
      }
    } else {
      return false;
    }
  } else {
    return false;
  }
}

bool tree_sitter_holscript_external_scanner_scan(__attribute__ ((unused)) void *payload, TSLexer *lexer, const bool *valid_symbols) {
  bool consumed = false;
  if (valid_symbols[BLOCK_COMMENT] || valid_symbols[LINE_COMMENT]) {
    if (tree_sitter_holscript_external_scanner_scan_comment(
            lexer, valid_symbols[BLOCK_COMMENT], valid_symbols[LINE_COMMENT],
            &consumed)) {
      return true;
    }
    // An unrewindable `(' that turned out not to open a comment: give
    // up here so tree-sitter re-lexes it internally.
    if (consumed) return false;
  }
  return scan_bol_keyword(lexer, valid_symbols);
}
