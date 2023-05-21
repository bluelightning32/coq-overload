#!/bin/bash

echo "main"
coq_makefile -o CoqMakefile -f _CoqProject
make -f CoqMakefile "$@"

if [ "$1" != "install" ]; then
  (
    declare -a filtered
    filtered=()
    for o in "$@"; do
      if [ "$o" = "install" ]; then
        continue;
      fi
      filtered+=("$o")
    done
    echo "alt"
    cd alt
    coq_makefile -o CoqMakefile -f _CoqProject
    make -f CoqMakefile "${filtered[@]}"
  )
fi

