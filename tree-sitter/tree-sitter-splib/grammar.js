const common = require('../common_grammar.js');

module.exports = grammar({
  name: 'splib',
  extras: common.extras,
  conflicts: common.conflicts,
  externals: common.externals,
  precedences: common.precedences,
  word: common.word,

  rules: {
    source_file: $ => $.splib,
    splib: $ => repeat1($._body_item),
    ...common.rules,
  }
});
