# Variables
CARGO = cargo
TREE_SITTER_CLI = tree-sitter-cli
TREE_SITTER_DIR_SPTHY = tree-sitter-spthy
TREE_SITTER_DIR_SPLIB = tree-sitter-splib

# Default target
.DEFAULT_GOAL := all

# Phony targets
.PHONY: all install generate

# Default task
all: install generate_spthy generate_splib

# Install tree-sitter-cli
install:
	$(CARGO) install $(TREE_SITTER_CLI)

# Generate tree-sitter grammar for spthy files
generate_spthy:
	cd $(TREE_SITTER_DIR_SPTHY) && tree-sitter generate

# Generate tree-sitter grammar for splib files
generate_splib:
	cd $(TREE_SITTER_DIR_SPLIB) && tree-sitter generate