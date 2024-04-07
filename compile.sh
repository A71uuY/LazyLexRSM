#!/bin/bash

#require argument
if [ ! -n "$1" ]; then 
  echo "ERROR: argument required (0, 1, 2, 3)" ; exit 1
fi

#main script
if [ -e Makefile ]; then
  rm Makefile
fi
echo "all:
	g++ files/Parser.cpp main_alg$1.cpp -std=c++11 -g
wrapper: files/Parser.cpp files/Parser.h c_wrapper.cpp
	g++ files/Parser.cpp c_wrapper.cpp -std=c++11 -g -o wrapper
large: files/Parser.cpp files/Parser.h large_ifs.cpp
	g++ files/Parser.cpp large_ifs.cpp -std=c++11 -g -o large_ifs" >> Makefile
make
mv a.out alg$1.out
rm Makefile


