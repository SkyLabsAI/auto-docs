#
# Copyright (C) 2019 BlueRock Security, Inc.
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#
ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

CPPFLAGS=-std=c++17
CFLAGS=-std=c99

%_c.v: %.c $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_h.v: %.h $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CFLAGS)
%_cpp.v: %.cpp $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CPPFLAGS)
%_hpp.v: %.hpp $(CPP2V)
	$(CPP2V) -v -o $@ $< -- $(CPPFLAGS)

%_c_names.v: %.c $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CFLAGS)
%_h_names.v: %.h $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CFLAGS)
%_cpp_names.v: %.cpp $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CPPFLAGS)
%_hpp_names.v: %.hpp $(CPP2V)
	$(CPP2V) -v -names $@ $< -- $(CPPFLAGS)
