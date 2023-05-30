#!/bin/bash

make_all() {
  echo "main"
  coq_makefile -o CoqMakefile -f _CoqProject
  make -f CoqMakefile "$@" || exit $?

  (
    echo "Example"
    coq_makefile -o ExampleMakefile -f _ExampleProject
    make -f ExampleMakefile "$@"
  ) || exit $?

  (
    echo "alt"
    cd alt
    coq_makefile -o CoqMakefile -f _CoqProject
    make -f CoqMakefile "$@"
  ) || exit $?
}

if [ "$1" = "install" ]; then
  make_all

  echo "install"
  coq_makefile -o CoqMakefile -f _CoqProject
  make -f CoqMakefile install || exit $?

  exit $?
elif [ "$1" = "clean" ]; then
  make_all clean
elif [ "$1" = "" ]; then
  make_all
else
  echo "Unknown command $@" >&2
  exit 1
fi
