#!/bin/bash -xe

cd "$(dirname "$0")"

# Update for changes to remote URLs
git submodule sync --recursive
# Update submodule checkouts:
git submodule update --init --recursive
# --recursive will descend into any nested submodules, even if none are used here.

dune_build_path=$PWD/../../_build/
mkdir -p ${dune_build_path}
dune_build_path=$(realpath ${dune_build_path})
export COQLIB=${dune_build_path}/default/fmdeps/coq
export COQBIN=${dune_build_path}/install/default/bin
export COQPATH=${dune_build_path}/install/default/lib/coq/user-contrib
export OCAMLPATH=${dune_build_path}/install/default/lib
export PATH=$COQBIN:$PATH

usage() {
	cat <<-EOF
		$0 [-f]
		Options:
		  -f	fast: skip preparation
	EOF
  exit $1
}

usage_error() {
	echo -e ">>>> Usage error: $1\n"
	usage 1
}

fast=0
while :; do
	case "$1" in
		-f)
			fast=1
			shift;;
		-[h?])
			usage 0;;
		# Remember break stops the loop, not case!
		--)
			shift; break;;
		"")
			break;;
		*)
			usage_error "unrecognized argument: $1";;
	esac
done


if [ $fast -eq 0 ]; then
  dune build @../install @../cpp2v
  pip3 install -r python_requirements.txt
fi
./core-build.sh
