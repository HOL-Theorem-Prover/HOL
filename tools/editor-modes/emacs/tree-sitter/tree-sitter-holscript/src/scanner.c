// Adapted tree-sitter-sml by Matthew Fluet, released under the MIT license.
#include <wctype.h>
#include <tree_sitter/parser.h>

enum TokenType {
  BLOCK_COMMENT,
  LINE_COMMENT,
};

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
    return tree_sitter_holscript_external_scanner_scan_comment(lexer, valid_symbols[BLOCK_COMMENT], valid_symbols[LINE_COMMENT]);
  } else {
    return false;
  }
}
