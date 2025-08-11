#!/bin/bash -vxe

dune_build_path=$(realpath $PWD/../../_build/)

if ! [ -d ${dune_build_path}/install ]; then
  git clean -fdX
  pip3 install -r python_requirements.txt
fi
dune build @../install @../cpp2v

export ROCQLIB=${dune_build_path}/default/fmdeps/coq
export ROCQBIN=${dune_build_path}/install/default/bin
export ROCQPATH=${dune_build_path}/install/default/lib/coq/user-contrib
export OCAMLPATH=${dune_build_path}/install/default/lib
export PATH=$ROCQBIN:$PATH

make clean -sj10
rm -rf sphinx/_build/ sphinx/cache/
./core-build.sh
