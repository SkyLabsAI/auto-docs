#
# Copyright (C) 2019 BlueRock Security, Inc.
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

include ../noinit_msg.mk

ifeq ($(filter init,$(MAKECMDGOALS)),)
ifeq ($(wildcard ../conf.mk),)
$(error $(MAKE_INIT_MESSAGE))
endif
endif

include ../conf.mk

ifneq ($(BHV),)
ROOT_OPT=--root=$(BHV)
else
ROOT_OPT=
endif
COQ_MAKEFILE=$(ROCQBIN)/coq_makefile

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	@ $(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq
	rm -f *_names.v *_hpp.v *_cpp.v *_c.v *_h.v

Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

_CoqProject: _CoqProject.template ../coq.flags
	cat ../coq.flags > $@
	@sed -e 's,^<BHV_PATHS>,,' \
		$@.template >> $@
