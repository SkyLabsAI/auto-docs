#
# Copyright (C) 2020 BlueRock Security, Inc.
#
# SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
#

define MAKE_INIT_MESSAGE

|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|

Please run "make init" before calling make. This will set up the necessary
environment-variables so that the BedRock-FM infrastructure is available
when running examples locally. Currently, "make init" supports two different
FM infrastructure archetypes (From `bhv` is recommended):

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|~~~~~~~~~ From `bhv` ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For this option, you must have a local clone of bhv where you have already
completed the (To Prove)<https://gitlab.com/bedrocksystems/bhv#to-prove>
portion of the setup from the `README.md`. Assuming that <BHV_PATH> represents
the fully-qualified path to your local clone of `bhv`, you can use the
following command to complete initialization:

  `$$ make init BHV=<BHV_PATH>`

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
|~~~~~~~~~ From Source ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
NOTE: This option is only meant for advanced users who are actively developing
  on fm-docs and cpp2v(-core) simultaneously.

For this option, you must have a local clone of `cpp2v-core` and `cpp2v`, and
you must have installed both of them into your active `.opam` switch.
Furthermore, you must have installed the `cpp2v` executable in your path.
Assuming that you have done all of this, you can use the following command to
complete initialization:

  `$$ make init BHV= CPP2V=$$(which cpp2v)`
|~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~|

endef
