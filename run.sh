#!/bin/bash

clang -S -emit-llvm -Xclang -disable-O0-optnone "$@" -o "$@.ll"
opt -S -mem2reg < "$@.ll" > "$@.mem2reg.ll"
opt -S -load ./cmake-build-debug/PRE/libPRE.so -PRE --debug-pass=Structure < "$@.mem2reg.ll" >| "$@.lcm.ll"
opt -S -simplifycfg < "$@.lcm.ll" >| "$@.spf.ll"
opt -S -gvn -simplifycfg < "$@.mem2reg.ll" >| "$@.gvn.ll"

clang -lm "$@.lcm.ll" -o "$@.lcm.exe" # lcm
clang -lm "$@.spf.ll" -o "$@.spf.exe" # spf
clang -lm "$@.gvn.ll" -o "$@.gvn.exe" # gvn


