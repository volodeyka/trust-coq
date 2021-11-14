#! /bin/bash

cat $(find -name '*axioms_*.out') | egrep -v '^((\s)|(<)|(Fetching)|(Axioms))'

