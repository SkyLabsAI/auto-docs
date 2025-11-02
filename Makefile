#
# Copyright (C) 2020-2025 SkyLabs AI.
#
# This software is distributed under the terms of the BedRock Open-Source License.
# See the LICENSE-BedRock file in the repository root for details.
#

ast-prepare:
	dune b --auto-promote @dune_inc
.PHONY: ast-prepare

clean:
	rm -f $(AST_FILES)
.PHONY: clean
