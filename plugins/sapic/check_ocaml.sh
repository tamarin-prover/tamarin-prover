#!/bin/bash

NEEDED_COMMANDS="ocamlc ocamllex ocamlyacc ocamldep"

for cmd in ${NEEDED_COMMANDS} ; do
    if ! command -v ${cmd} &> /dev/null ; then
        echo Please install ${cmd}!
        exit 1
    fi
done

touch .ocaml_ok
