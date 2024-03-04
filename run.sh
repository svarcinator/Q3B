#!/bin/bash

clear

echo "#################"
echo "    COMPILING    "
echo "#################"

cmake -DCMAKE_BUILD_TYPE=Debug -S . -B build
cmake --build build -j4 

echo "#################"
echo "     RUNNING     "
echo "#################"

ABSTR=under
METHOD=both
BENCHM=precise_mistakes/check_bvslt_bvor_64bit.smt2

./build/q3b --abstraction=$ABSTR --abstract:method=$METHOD --lazy-evaluation=1 --verbosity=5 ./benchmarks/$BENCHM

#../q3b_orig/Q3B/build/q3b --abstraction=$ABSTR   --abstract:method=$METHOD --verbosity=5 ./benchmarks/$BENCHM



