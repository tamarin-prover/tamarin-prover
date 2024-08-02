#!/bin/bash
find ../../examples -type d \( -name 'deprecated' -o -name 'not-working' \) -prune -o -name '*.spthy' -print0 | xargs -0 tree-sitter parse --quiet --stat
