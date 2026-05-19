_default:
  @just --list

[working-directory: "tree-sitter-grammar"]
reload-grammar:
  #!/usr/bin/env bash
  tree-sitter generate && tree-sitter build && \
    tree-sitter test && \
    cp grammar.so $HOME/.local/share/nvim/lazy/nvim-treesitter/parser/row.so && \
    cp queries/highlights.scm $HOME/.local/share/nvim/lazy/nvim-treesitter/queries/row/highlights.scm;



