#!/bin/sh -xe
make init BHV= CPP2V=$(dune exec -- which cpp2v)
ALECTRYON_DRIVER=coqlsp make doc -sj10
