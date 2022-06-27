#!/bin/bash

coq_makefile -o CoqMakefile grad3.v Universe.v AnnotatedType.v Grade.v LargeEq.v LargeHurkens.v Context.v
make -f CoqMakefile
