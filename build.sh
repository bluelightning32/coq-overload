#!/bin/bash

coq_makefile -o CoqMakefile -f _CoqProject
make -f CoqMakefile
