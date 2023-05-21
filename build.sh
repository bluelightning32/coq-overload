#!/bin/bash

echo "main"
coq_makefile -o CoqMakefile -f _CoqProject
make -f CoqMakefile "$@"

declare -a filtered
filtered=()
for o in "$@"; do
  if [ "$o" = "install" ]; then
    continue;
  fi
  filtered+=("$o")
done

(
  echo "Example"
  coq_makefile -o ExampleMakefile -f _ExampleProject
  make -f ExampleMakefile "${filtered[@]}"
)

(
  echo "alt"
  cd alt
  coq_makefile -o CoqMakefile -f _CoqProject
  make -f CoqMakefile "${filtered[@]}"
)
