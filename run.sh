#!/bin/bash

echo "#################"
echo "    COMPILING    "
echo "#################"

cmake -DCMAKE_BUILD_TYPE=Debug -S . -B build
cmake --build build -j4 

echo "#################"
echo "     RUNNING     "
echo "#################"


./build/q3b --abstraction=under --abstract:method=variables --lazy-evaluation=1 --verbosity=5 ./benchmarks/RNDPRE_4_42.smt2


