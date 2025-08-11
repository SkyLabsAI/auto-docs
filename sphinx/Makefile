####################################################################################
## Copyright (C) 2020 BlueRock Security, Inc.                                       ##
## All rights reserved.                                                           ##
## SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, ##
##                          see repository root for details.                      ##
####################################################################################

# Makefile for the BedRock Systems Formal Methods Documentation

# This is based heavily on the documentation efforts by the Coq development team.
# For more information, please refer to coq/doc/README.md, which covers dependencies
# and use cases; if extensions are needed, their coq/Makefile.doc is a good reference.

include src/noinit_msg.mk

ifeq ($(filter init,$(MAKECMDGOALS)),)
ifeq ($(filter uninit,$(MAKECMDGOALS)),)
ifeq ($(wildcard src/conf.mk),)
$(error $(MAKE_INIT_MESSAGE))
endif
endif
endif

-include src/conf.mk

ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
ALECTRYON = $(ROOT_DIR)/alectryon/alectryon.py
export ALECTRYON

COQPATHEXTRA = $(ROOT_DIR)/src:$(realpath ../../_build/default/fmdeps/fm-docs/src)

######################################################################
### Variables
######################################################################

# Sphinx-related variables
SPHINXENV:= ROCQBIN=$(ROCQBIN) ROCQLIB=$(ROCQLIB) ROCQPATH=$(COQPATHEXTRA):$(ROCQPATH) COQ_SRC_SUBDIRS=:$(COQ_SRC_SUBDIRS)
SPHINXWARNERROR ?= 1
ifeq ($(SPHINXWARNERROR),1)
SPHINXOPTS= -W
else
SPHINXOPTS=
endif

SPHINXDIR ?= $(ROOT_DIR)/sphinx
SPHINXTANGLEDIR = $(SPHINXDIR)/tangles
export SPHINXTANGLEDIR

SPHINXBUILD= $(shell which sphinx-build)
SPHINXBUILDDIR = $(SPHINXDIR)/_build

ALLSPHINXOPTS= -d $(SPHINXBUILDDIR)/doctrees $(SPHINXOPTS)

######################################################################
### General rules
######################################################################

all: doc

init:
	$(MAKE) -C src $(MAKECMDGOALS)
	$(MAKE) sphinx/_CoqProject

sphinx/_CoqProject: sphinx/_CoqProject.template src/coq.flags
	cat src/coq.flags > $@
	@sed -e 's,^<BHV_PATHS>,,' \
		sphinx/_CoqProject.template >> sphinx/_CoqProject

uninit:
	rm -f sphinx/_CoqProject
	$(MAKE) -C src uninit

.PHONY: doc doc-public doc-private init redoc src tangle-src tangle uninit FORCE_FULL_BHV

TANGLE_DIR     = $(SPHINXDIR)/orphans
TANGLE_INPUTS  = $(wildcard $(TANGLE_DIR)/*.v)
TANGLE_OUTPUTS = $(patsubst $(TANGLE_DIR)/%.v,$(SPHINXTANGLEDIR)/%.rst,$(TANGLE_INPUTS))

# This is responsible for building .rst files from .v files with Alectryon comments
$(SPHINXTANGLEDIR)/%.rst: $(TANGLE_DIR)/%.v
	@mkdir -p $(SPHINXDIR)/tangles
	python3 $(ALECTRYON) --frontend coq+rst --backend rst --debug \
	$< -o $@

tangle: $(TANGLE_OUTPUTS)

src:
	$(MAKE) -C src all
tangle-src:
	$(MAKE) -C src tangle-all

doc-public: tangle-src tangle refman-public
doc-private: tangle-src tangle refman-private

doc: doc-private
redoc: clean doc

refman-public-%:
	@echo 'SPHINXBUILD sphinx ($*)'
	$(HIDE)$(SPHINXENV) $(SPHINXBUILD) -b $* \
		$(ALLSPHINXOPTS) sphinx $(SPHINXBUILDDIR)/$*

# NOTE: in sphinx/conf.py, the `private` tag is used to conditionally allow the sphinx/private directory
refman-private-%:
	@echo 'SPHINXBUILD sphinx ($*)'
	$(HIDE)$(SPHINXENV) $(SPHINXBUILD) -b $* \
		-t private \
		$(ALLSPHINXOPTS) sphinx $(SPHINXBUILDDIR)/$*

refman-public: | tangle-src tangle
	+$(MAKE) refman-public-html

refman-private: | tangle-src tangle
	+$(MAKE) refman-private-html

# Simpler is `cd $(SPHINXDIR); make latexpdf`, but Sphinx generatex .tex files
# with "’", which are printed incorrectly (disappear) in the pdfs generated
# by xelatex. Other unicode issues in the generated .tex file are discharged for
# now just by getting rid of the unicode.
drivers-pdf:
	cd $(SPHINXDIR); make latexpdf

clean:
	+$(MAKE) -C src clean
	rm -rf $(SPHINXBUILDDIR)
	rm -rf $(SPHINXDIR)/tangles

open:
	xdg-open $(SPHINXBUILDDIR)/html/index.html
