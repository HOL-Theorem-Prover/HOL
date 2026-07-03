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
  while (len < 30 && is_ident_cont(lexer->lookahead)) {
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

bool tree_sitter_holscript_external_scanner_scan_comment(TSLexer *lexer, bool block_comment, bool line_comment) {
  while (!lexer->eof(lexer) && iswspace(lexer->lookahead)) {
    lexer->advance(lexer, true);
  }
  if (lexer->eof(lexer)) return false;
  if (lexer->lookahead == '(') {
    lexer->advance(lexer, false);
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
  if (valid_symbols[BLOCK_COMMENT] || valid_symbols[LINE_COMMENT]) {
    if (tree_sitter_holscript_external_scanner_scan_comment(lexer, valid_symbols[BLOCK_COMMENT], valid_symbols[LINE_COMMENT])) {
      return true;
    }
  }
  return scan_bol_keyword(lexer, valid_symbols);
}
