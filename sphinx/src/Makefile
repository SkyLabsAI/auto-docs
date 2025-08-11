#
# Copyright (C) 2020 BlueRock Security, Inc.
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

include noinit_msg.mk

ifeq ($(filter init,$(MAKECMDGOALS)),)
ifeq ($(filter uninit,$(MAKECMDGOALS)),)
ifeq ($(wildcard conf.mk),)
$(error $(MAKE_INIT_MESSAGE))
endif
endif
endif

-include conf.mk

ifeq ($(filter init,$(MAKECMDGOALS)),)
ifeq ($(filter uninit,$(MAKECMDGOALS)),)
ifeq ($(wildcard $(CPP2V)),)
$(error You are missing the `cpp2v` binary (configured to be located here: $(CPP2V)). \
	Please build the binary and/or reconfigure your local setup)
endif
endif
endif

DIRS=
COQ_DIRS = $(addprefix coq-, $(DIRS))
TANGLE_DIRS = $(addprefix tangle-, $(DIRS))

all: $(COQ_DIRS)
tangle-all: $(COQ_DIRS) $(TANGLE_DIRS)

_DOWNLOADS_DIR:=_downloads
_downloads:
	mkdir -p $(_DOWNLOADS_DIR)
	zip -r $(_DOWNLOADS_DIR)/fm-docs-full.zip . -x "_downloads/*" "*/.*" "*/*.vo*" \
							"*/*.glob" "*/Makefile.coq" "*/Makefile.coq.conf" \
							"conf.mk" "*/_CoqProject"

$(COQ_DIRS):
	$(MAKE) -C $(subst coq-,,$@) coq

$(TANGLE_DIRS):
	$(MAKE) -C $(subst tangle-,,$@) tangle

.PHONY: $(COQ_DIRS) $(TANGLE_DIRS)

clean:
	rm -rf _downloads/
	$(foreach d,$(DIRS),$(MAKE) -C $(d) clean;)

#
# config
#

.PHONY: init uninit

init: conf.mk

uninit:
	rm -f conf.mk
	$(foreach d,$(DIRS),rm -f $(d)/_CoqProject)

conf.mk:
	$(info Make: Current configuration saved at $@)
	@sed -e 's,^export BHV[ \t]*?= \(.*\),export BHV ?= $(if $(filter undefined,$(origin BHV)),\1,$(BHV)),'		\
		-e 's,^export ROCQBIN[ \t]*?= \(.*\),export ROCQBIN ?= $(if $(filter undefined,$(origin ROCQBIN)),\1,$(ROCQBIN)),'	\
		-e 's,^export ROCQLIB[ \t]*?= \(.*\),export ROCQLIB ?= $(if $(filter undefined,$(origin ROCQLIB)),\1,$(ROCQLIB)),'	\
		-e 's,^export CPP2V[ \t]*?= \(.*\),export CPP2V ?= $(if $(filter undefined,$(origin CPP2V)),\1,$(CPP2V)),'	\
		$@.default > $@

# Force a new config file when calling make init. Useful for:
# - Switching from one configuration to another on the command line
# - Trigger a rebuild when changing the configuration (future changes)
ifneq ($(filter init,$(MAKECMDGOALS)),)
ifeq ($(filter uninit,$(MAKECMDGOALS)),)
.PHONY: conf.mk
endif
endif
