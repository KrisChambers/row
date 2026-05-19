/**
 * @file Experimental functional language with records and effects using Row Polymorphism.
 * @author Kris Chambers <kris.chambers@outlook.com>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

module.exports = grammar({
  name: "row",

  extras: $ => [
    /\s/, // whitespace
    $.comment
  ],

  rules: {
    source_file: $ => repeat($._top_level_item),

    comment: $ => token(choice(
      seq('//', /(\\(.|\r?\n)|[^\\\n])*/),
      seq(
        '/*',
        /[^*]*\*+([^/*][^*]*\*+)*/,
        '/'
      )
    )),
    _top_level_item: $ => choice(
      $.let_decl,
      $.effect_decl,
      $.data_decl,
    ),

    effect_decl: $ => seq(
      "effect",
      field("effect_name", $.effect_name),
      "{",
      repeat1($.effect_op),
      "}"
    ),

    effect_name: $ => $.type,
    effect_op: $ => seq(
      field("effect_op_name", $.lower_ident),
      ":",
      $.type,
      "->",
      $.type,
      optional(",")
    ),

    // This helps flatten the nesting of types into a list.
    type_param: $ => choice(/[a-z]/, "()"),
    type: $ => choice($._type_atom, $._type_seq),
    _type_seq: $ => prec.right(1, seq(
      $._type_atom,
      repeat1($._type_atom)
    )),
    _type_atom: $ => choice($.type_param, $.type_constructor, seq("(", choice($._type_atom, $._type_seq), ")")),
    type_constructor: $ => $.upper_ident,

    // data Name a b = ...
    data_decl: $ => seq(
      "data",
      field("type_name", $.type),
      "=",
      field("cstr_list", $.cstr_list),
      optional(";")
    ),

    cstr_list: $ => seq(
      $.type,
      repeat(seq(
        "|",
      $.type
      ))
    ),

    upper_ident: $ =>/[A-Z][a-zA-Z0-9_]*/,
    lower_ident: $ =>/[a-z][a-zA-Z0-9_]*/,

    // let name = ...
    let_decl: $ => seq(
      'let',
      field('name', $.variable),
      '=',
      field('value', $.expression),
      optional(';')
    ),

    expression: $ => choice(
      $.lambda,
      $.variable,
      $.let_exp,
      $.integer,
      $.string_literal
    ),

    lambda: $ => seq(
      '\\',
      field('var', $.variable),
      '->',
      field('body', $.expression)
    ),

    let_exp: $ => seq(
      "let",
      field('name', $.variable),
      "=",
      field("binding", $.expression),
      "in",
      field("body", $.expression)
    ),

    variable: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,
    integer: $ => /\d+/,
    string_literal: $ => seq(
      '"',
      repeat(/[^"\\]+|\\./),
      '"'
    ),
  }
});
