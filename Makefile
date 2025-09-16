#
# Copyright (C) 2020-2025 BlueRock Security, Inc.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

AST_FILES := $(patsubst %/dune-gen.sh,%/dune.inc,$(shell find . -name dune-gen.sh))

all: ast-prepare

%/dune.inc: FORCE
	cd `dirname $@`; ./dune-gen.sh
.PHONY: FORCE

ast-prepare: $(AST_FILES)

.PHONY: ast-prepare

.PHONY: all

clean:
	rm -f $(AST_FILES)

.PHONY: clean
