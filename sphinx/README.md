# *BedRock FM*: A Pragmatic Guide - Contributor Handbook

**The documentation is live** [here](https://bedrocksystems.gitlab.io/formal-methods/fm-docs). This documentation is maintained by Jasper Haag (jasper@bedrocksystems.com) and the gitlab repo is hosted [here](https://gitlab.com/bedrocksystems/formal-methods/fm-docs). There is a hidden **.rst** file called `fm-docs/sphinx/contributing.rst` which contains more specific details for contributing.

## New quick build instructions

- Checkout this repository inside `bhv/fmdeps`.
- Enter a suitable Python virtualenv.
- `bhv$ cd fmdeps/fm-docs`
- run `pip3 install -r python_requirements.txt` to install dependencies (only needed first time/when they change)

Then,
- if used inside bhv or fm-workspace, run `./build-plan.sh`
- else, run `core-build.sh`

## Table of Contents
- [Overview](#overview)
- [Building](#building)
- [Organization](#organization)
- [Technology](#technology)
  - [reStructuredText](#restructuredtext)
  - [Sphinx](#sphinx)
  - [Alectryon](#alectryon)
- [Contributing](#contributing)

## Overview
The BedRock Systems [FM-docs](https://gitlab.com/bedrocksystems/formal-methods/fm-docs) project is focused on providing a pragmatic guide to specifying C++ code using our public-facing **cpp2v-core** infrastructure. This guide should **NOT** reference internal details of BedRock Systems projects (like bhv, zeta or NOVA), and it should not (currently) reference any of the internal automation; the hope is to make this guide public at some point in the future, and when we do that we need to be sure that we don't leak any IP. Instead, this guide should be designed to familiarize (Systems/C++) programmers with the requisite infrastructure that they'll need in order to specify the code which they write.

## Building
In order to build the documentation locally you require the following dependencies:
- cpp2v-core/cpp2v (see depends file for the requisite versions)
- python3/pip3

You can install the Python dependencies (besides cpp2v(-core) and python3/pip3) with the following commands:
- `pip3 install -r python_requirements.txt`

**NOTE**: Make sure that the binaries installed via pip (in particular `sphinx-build`) are accessible in `$PATH`. This may mean adding `~/.local/bin` to `$PATH`.

### Configuring Access to the BedRock FM Stack

Before you are able to build any of the documentation or examples locally, you must configure access to the BedRock FM Stack. Currently, two archetypes are supported (although the *From `bhv`* method is highly recommended):

#### From `bhv`

For this option, you must have a local clone of bhv where you have already completed the [ToProve](https://gitlab.com/bedrocksystems/bhv#to-prove) portion of the setup from the `README.md`. Assuming that <BHV_PATH> represents the fully-qualified path to your local clone of `bhv`, you can use the following command to complete initialization:

  `$ make init BHV=<BHV_PATH>`

#### From Source

**NOTE**: This option is only meant for advanced users who are actively developing on fm-docs and cpp2v(-core) simultaneously.

For this option, you must have a local clone of `cpp2v-core` and `cpp2v`, and you must have installed both of them into your active `.opam` switch. Furthermore, you must have installed the `cpp2v` executable in your path. Assuming that you have done all of this, you can use the following command to complete initialization:

  `$$ make init BHV= CPP2V=$$(which cpp2v)`

## Organization
- **alectryon/**: this directory houses a clone of the *Alectryon* project (created by [Clément Pit-Claudel](http://pit-claudel.fr/clement/)).
- **coq/**: *DEPRECATED* - this was included so that *coqrst* could be utilized, but Alectryon replaces *coqrst*; we should remove this dependency.
- **sphinx/**: this directory houses all of the **.rst** files which are used to build the site (as well as other required configuration files).
  - **sphinx/conf.py**: this file configures the sphinx environment before building the site. **NOTE**: There are a few configurations which have been added to conf.py in order to patch issues with Alectryon.
  - **sphinx/_build**: this directory houses the result of building the site.
    - **sphinx/_build/doctree**: this directory houses the sphinx metadata associated with a build.
    - **sphinx/_build/html**: this directory houses the html/css/js associated with the most-recently built site.
  - **sphinx/_static**: this directory houses the static assets which are used for the site. Currently, this only contains an empty `.keep` file (which is used to get `git` to behave nicely). Most of the static assets are taken from **alectryon/assets**.
  - **sphinx/_templates**: this directory houses the html templates which are used for the site. Currently, this only contains an empty `.keep` file (which is used to get `git` to behave nicely).
  - **sphinx/private**: this directory houses the **.rst** files which should only be distributed with private copies of this documentation.
  - **sphinx/index.rst**: the entry-point for the documentation site.
    - **sphinx/*.rst**: the top-level reStructuredText files which constitute the guide.
- **src/**: this directory houses all of the *Coq* files which are run through *CPP2V* and imported into **.rst** files.

## Technology

### reStructuredText

[reStructuredText](https://docutils.sourceforge.io/rst.htm) is a plaintext markup syntax which was initially created for use within the Python development community. It is highly extensible which makes it possible to design tooling for specific application domains. It is highly recommended that you look at the [Sphinx reStructuredText Primer](https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html) in order to internalize the syntax and peculiarities of the reST format.

### Sphinx

[Sphinx](https://www.sphinx-doc.org/en/master/) is a documentation tool which was initially created for the Python documentation, but it has since been fleshed out with support for a variety of languages and use-cases.

### Alectryon

[Alectryon](https://github.com/cpitclaudel/alectryon) was created to ease the development of effective documentation for Coq projects and ideas; a guide for it can be found [here](https://plv.csail.mit.edu/blog/drafts/alectryon.html). Alectryon can be used within a variety of static-site-generators (include [Sphinx](#sphinx)) and relies on the [SerAPI](https://github.com/ejgallego/coq-serapi) library. While Alectryon makes it easy to add coq code (inline or in blocks) to reST (**.rst**) files, it also provides a tool for (invertibly) transforming between **.v** and **.rst** files; **.v** files can be documented using a custom comment syntax (```(*| |*)```, with *reStructuredText* within the blocks) in order to make them compatible with the translator. This makes it simple to generate documentation for particular **.v** files while ensuring that the code examples and prose are in-sync.

## Contributing

If you're contributing to the documentation, please ensure that you familiarize yourself with [Alectryon](https://plv.csail.mit.edu/blog/drafts/alectryon.html) and [Sphinx](https://www.sphinx-doc.org/en/master/)/[reStructuredText](https://docutils.sourceforge.io/rst.html) first. Once you've done this, feel free to add new sections or edit previous sections!

You can build a local version of the private documentation by running `make doc` (or `make doc-private`); you can build a local version of the public documentation by running `make doc-public`; and you can clean your local environment by running `make clean`. Once you've built a local version of the documentation, you can view it by opening `fm-docs/sphinx/_build/html/index.html` in your favorite browser.
