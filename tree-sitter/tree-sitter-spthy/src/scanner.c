#include <wctype.h>
#include <stdbool.h>

#include <tree_sitter/parser.h>

enum TokenType {
    MULTI_COMMENT,
    SINGLE_COMMENT
};

// Code inspired by:
// https://github.com/ulrikstrid/ligo/commit/c7e54645a2ab8402e3995283ecd624af772908d7#diff-d2dc96fb2151553ebe461cabf8cc8ef105113a8478c3c86abd91fc2c589861eb

void * tree_sitter_spthy_external_scanner_create() {return NULL;}
void tree_sitter_spthy_external_scanner_destroy(void *payload) {}
unsigned tree_sitter_spthy_external_scanner_serialize(void *payload, char *buffer) {return 0;}
void tree_sitter_spthy_external_scanner_deserialize(void *payload, const char *buffer, unsigned length) {}

bool tree_sitter_spthy_external_scanner_scan(void *payload, TSLexer *lexer, const bool *valid_symbols) {
    while (iswspace(lexer->lookahead)) lexer->advance(lexer, true);

    if (lexer->lookahead == '/') {
        lexer->advance(lexer, false);
        if (lexer->lookahead == '*') {
            lexer->advance(lexer, false);

            bool after_star = false;
            unsigned nesting_depth = 1;
            for (;;) {
                switch (lexer->lookahead) {
                case '\0':
                    return false;
                case '*':
                    lexer->advance(lexer, false);
                    after_star = true;
                    break;
                case '/':
                    if (after_star) {
                        lexer->advance(lexer, false);
                        after_star = false;
                        nesting_depth--;
                        if (nesting_depth == 0) {
                            lexer->result_symbol = MULTI_COMMENT;
                            return true;
                        }
                    } else {
                        lexer->advance(lexer, false);
                        after_star = false;
                        if (lexer->lookahead == '*') {
                            nesting_depth++;
                            lexer->advance(lexer, false);
                        }
                    }
                    break;
                default:
                    lexer->advance(lexer, false);
                    after_star = false;
                    break;
                }
            }
        } else if (lexer->lookahead == '/') {
           lexer->advance(lexer, false);

           for (;;) {
               switch (lexer->lookahead) {
               case '\n':
                   lexer->result_symbol = SINGLE_COMMENT;
                   return true;
               case '\0':
                   lexer->result_symbol = SINGLE_COMMENT;
                   return true;
               default:
                   lexer->advance(lexer, false);
                   break;
               }
           }
        }
    }

    return false;
}
