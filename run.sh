#!/bin/bash

echo "#################"
echo "    COMPILING    "
echo "#################"

cmake -S . -B build
cmake --build build -j4 

echo "#################"
echo "     RUNNING     "
echo "#################"


./build/q3b --abstraction=over --lazy-evaluation=1 --verbosity=5 /var/tmp/vcloud-q3b/BV/2017-Preiner-keymaera/intersection-example-onelane.proof-node48996.smt2


