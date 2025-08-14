#!/usr/bin/ python3
####################################################################################
## Copyright (C) 2020 BlueRock Security, Inc.                                       ##
## All rights reserved.                                                           ##
## SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, ##
##                          see repository root for details.                      ##
####################################################################################

# TODO: Fix the following 5 fields
# General information about the project.
project = 'BlueRock FM: A Pragmatic Guide'
copyright = '2020-2025 BlueRock Security'
author = ''

version = "0.0.1"
release = "alpha"

# -*- coding: utf-8 -*-
#
# Configuration file for the Sphinx documentation builder.
#
# This file does only contain a selection of the most common options. For a
# full list see the documentation:
# http://www.sphinx-doc.org/en/master/config

# NOTE: This configuration is based on coq/doc/sphinx/conf.py, since we utilize
#       coqrst (and the custom coq documentation setup) in order to create our
#       own documentation.

# NOTE: Be sure to read coq/doc/README.md if you encounter issues

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.

import sys
import os
import sphinx

# Increase recursion limit for sphinx
sys.setrecursionlimit(10000)

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
sys.path.append(os.path.abspath('../alectryon/'))

# -- Prolog ------------------------------------------------------------------

# Include substitution definitions in all files
# TODO: Determine if/what we want in our preamble. A lot of this is coq-specific
#       so it may make sense to leave this part off for now
# with open(os.pat.abspath('../coq/doc/sphinx/refman-preamble.rst')) as s:
#     rst_prolog = s.read()

# -- General configuration ---------------------------------------------------

# If your documentation needs a minimal Sphinx version, state it here.
needs_sphinx = '2.3.1'

sertop_args = ['-w', '-notation-overridden', '-w', '-notation-incompatible-prefix']

coq_src_paths = os.environ.get("COQ_SRC_SUBDIRS", "").split(':')
for src_path in coq_src_paths:
    if src_path.strip() == '':
        continue
    sertop_args.extend(["-I", src_path])

import alectryon.docutils
import alectryon.core
alectryon.core.DEFAULT_MARKUP = "md"
alectryon.core.DEFAULT_DRIVERS["coq"] = "coqlsp"

alectryon.docutils.LONG_LINE_THRESHOLD = 90
alectryon.docutils.CACHE_DIRECTORY = os.path.abspath("cache/")

# NOTE: Clément resolved the sphinx docinfo issue, but we still need to grab the
#       paths for bedrock to feed to SerAPI, so we're still using this.
#alectryon.docutils.AlectryonTransform.SERTOP_ARGS = sertop_args
alectryon.docutils.AlectryonTransform.DRIVER_ARGS["sertop"] = list(sertop_args)
alectryon.docutils.AlectryonTransform.DRIVER_ARGS["sertop_noexec"] = list(sertop_args)
alectryon.docutils.AlectryonTransform.DRIVER_ARGS["coqc_time"] = list(sertop_args)
if 'ALECTRYON_DRIVER' in os.environ:
    driver = os.environ.get('ALECTRYON_DRIVER')
    if driver == 'SERTOP_NOEXEC':
        alectryon.docutils.AlectryonTransform.LANGUAGE_DRIVERS = {"coq": "sertop_noexec"}
    elif driver == 'COQC_TIME':
        alectryon.docutils.AlectryonTransform.LANGUAGE_DRIVERS = {"coq": "coqc_time"}
    elif driver == 'coqlsp':
        alectryon.docutils.AlectryonTransform.LANGUAGE_DRIVERS = {"coq": "coqlsp"}
    else:
        raise ValueError('')
alectryon.docutils.AlectryonTransform.LANGUAGE_DRIVERS = {"coq": "coqc_time"}

# NOTE: Add in other entries here if we want to register coqdoc things which are
#       compatible with the `:coqid:` role.
alectryon.docutils.COQ_IDENT_DB_URLS.append(
    ("bluerock", "https://bedrocksystems.gitlab.io/cpp2v/$modpath.html#$ident")
)

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    # This could be useful for delineating cpp2v-core and cpp2v
    'sphinx.ext.ifconfig',

    # NOTE: These are included for completeness, but it's not clear that
    #       we'll actually be using them
    'sphinx.ext.mathjax',
    'sphinx.ext.todo',

    # This extension supports output to pdf:
    'rst2pdf.pdfbuilder',
    'myst_parser',

    # NOTE: These are the key extensions which enables our documentation efforts
    'alectryon.sphinx'
    # 'coqrst.coqdomain'
]

# NOTE: This may not be as important in the fm-docs repo, but it's probably
#       useful when we enforce more thorough documentation standards in
#       cpp2v(-core)
report_undocumented_coq_objects = "warning"

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# The suffix(es) of source filenames.
# You can specify multiple suffix as a list of string:
#
# source_suffix = ['.rst', '.md']
source_suffix = '.rst'

# The master toctree document.
master_doc = 'index'

# The language for content autogenerated by Sphinx. Refer to documentation
# for a list of supported languages.
#
# This is also used if you do content translation via gettext catalogs.
# Usually you set "language" from the command line for these cases.
language = 'en'

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store', 'orphans/*.rst', '**/private/*.rst']

# The reST default role (used for this markup: `text`) to use for all
# documents.
default_role = 'coq'

# Use the Coq domain
# primary_domain = 'coq'

# If true, '()' will be appended to :func: etc. cross-reference text.
#add_function_parentheses = True

# If true, the current module name will be prepended to all description
# unit titles (such as .. function::).
#add_module_names = True

# If true, sectionauthor and moduleauthor directives will be shown in the
# output. They are ignored by default.
#show_authors = False

# The name of the Pygments (syntax highlighting) style to use.
#pygments_style = 'sphinx'
#highlight_language = 'text'
#suppress_warnings = ["misc.highlighting_failure"]

# A list of ignored prefixes for module index sorting.
#modindex_common_prefix = []

# If true, keep warnings as "system message" paragraphs in the built documents.
#keep_warnings = False

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = False

# Extra warnings, including undefined references
nitpicky = True

nitpick_ignore = [ ('token', token) for token in [
    'binders',
    'collection',
    'modpath',
    'tactic',
]]

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'sphinx_rtd_theme'
# html_theme = 'agogo'
# html_theme = 'alabaster'
# html_theme = 'haiku'
# html_theme = 'bizstyle'
# html_permalinks_icon = '<span>#</span>'
# html_theme = 'sphinxawesome_theme'

# Theme options are theme-specific and customize the look and feel of a theme
# further.  For a list of options available for each theme, see the
# documentation.
#
html_theme_options = {
    'prev_next_buttons_location': 'bottom',
#    'gitlab_url': 'https://gitlab.com/bedrocksystems/formal-methods/fm-docs',
    'style_external_links': True
}

# Add any paths that contain custom themes here, relative to this directory.
#import sphinx_rtd_theme
#html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static', '../alectryon/alectryon/assets']

html_css_files = [
    'css/justify.css',
]

# Custom sidebar templates, must be a dictionary that maps document names
# to template names.
#
# The default sidebars (for documents that don't match any pattern) are
# defined by theme itself.  Builtin themes are using these templates by
# default: ``['localtoc.html', 'relations.html', 'sourcelink.html',
# 'searchbox.html']``.
#
# html_sidebars = {}


# -- Options for HTMLHelp output ---------------------------------------------

# Output file base name for HTML help builder.
htmlhelp_basename = 'pragmaticFM-doc'


# -- Options for LaTeX output ------------------------------------------------

latex_elements = {
    # The paper size ('letterpaper' or 'a4paper').
    #
    # 'papersize': 'letterpaper',

    # The font size ('10pt', '11pt' or '12pt').
    #
    # 'pointsize': '10pt',

    # Additional stuff for the LaTeX preamble.
    #
    # 'preamble': '',

    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    (master_doc, 'pragmaticFM.tex', 'BedRock FM: A Pragmatic Guide',
     'Jasper Haag', 'manual'),
]


# -- Options for manual page output ------------------------------------------

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [
    (master_doc, 'pragmaticfm', 'BedRock FM: A Pragmatic Guide',
     [author], 1)
]

# -- Options for Texinfo output ----------------------------------------------

# Grouping the document tree into Texinfo files. List of tuples
# (source start file, target name, title, author,
#  dir menu entry, description, category)
texinfo_documents = [
    (master_doc, 'PragmaticFMDocumentation', 'BlueRock FM: A Pragmatic Guide',
     author, 'PragmaticFMDocumentation', 'A pragmatic guide to formal methods within BlueRock.',
     'Miscellaneous'),
]


# -- Options for Epub output -------------------------------------------------

# Bibliographic Dublin Core info.
epub_title = project

# The unique identifier of the text. This can be a ISBN number
# or the project homepage.
#
# epub_identifier = ''

# A unique identification for the text.
#
# epub_uid = ''

# A list of files that should not be packed into the epub file.
epub_exclude_files = ['search.html']

# -- Support rst2pdf output -------------------------------------------------
# Requires as a dependency `pip install rst2pdf`
# To build PDFs, do `sphinx> make pdf`.

pdf_documents = [('drivers', u'drivers', u'How To BedRock a Driver', u'Gordon Stewart'),]
pdf_stylesheets = ['bedrock-stylesheet.txt']
pdf_style_path = ['.']
pdf_use_coverpage = True
pdf_language = "en_US"
##NOTE: fixing the mono font to FreeMono, which has the unicode symbols we need,
## required fixing codec.py utf-8 decoding errors. The process was:
##  * Find all the .afm files in /usr/share/texmf-dist/fonts/afm
##  * Replace the literal '\xa9' (an outdated unicode copyright symbol, now
##    encoded as \u00a9) by '(c)'. sed -i 's/\xa9/(c)/g' */*.afm
##NOTE: on my machine, I get errors of the form
## [ERROR] findfonts.py:330 Error registering font:
##         FreeMono from /usr/share/fonts/gnu-free/FreeMono.otf
## but the generated PDF still looks fine (and appears to be using FreeMono)
pdf_font_path = ['/usr/share/fonts','/usr/share/texmf-dist']
pdf_break_level = 1 # Turn on "level 1" page breaks
##TODO: figure out how to template 'author' and 'date'
## E.g., #{title} as suggested in the rst2pdf docs doesn't appear to work.
pdf_cover_template = 'bedrock-cover.tmpl'

# -- Support latex output -------------------------------------------------
# Modified from https://sphinxguide.readthedocs.io/en/latest/sphinx_basics/settings.html

numfig = True

latex_engine = 'xelatex'
latex_elements = {
    # The paper size ('letterpaper' or 'a4paper').
    #
    'papersize': 'letterpaper',
    'releasename':"Release",
    'fncychap': '\\usepackage{fncychap}',
    'fontpkg': '\\usepackage{amsmath,amsfonts,amssymb,amsthm}',

    'figure_align':'htbp',
    # The font size ('10pt', '11pt' or '12pt').
    #
    'pointsize': '11pt',

    # Additional stuff for the LaTeX preamble.
    #
    'preamble': r'''
        %%%%%%%%%%%%%%%%%%%% Meher %%%%%%%%%%%%%%%%%%
        %%%add number to subsubsection 2=subsection, 3=subsubsection
        %%% below subsubsection is not good idea.
        \setcounter{secnumdepth}{3}
        %
        %%%% Table of content upto 2=subsection, 3=subsubsection
        \setcounter{tocdepth}{3}

        \usepackage{amsmath,amsfonts,amssymb,amsthm}
        \usepackage{graphicx}

        \usepackage{unicode-math}

        \usepackage[Latin,Greek]{ucharclasses}
        \usepackage{fontspec}
        \usepackage{fontenc}
        %\usepackage{newpxtext,newpxmath}
        \setmainfont{TeX Gyre Pagella}
        %\setmonofont{TeX Gyre Cursor}

        %Deal with missing unicode characters
        \usepackage{newunicodechar}
        \newfontfamily{\freeserif}{FreeSerif}
        \newunicodechar{∀}{\makebox[.5em]{\freeserif∀}}
        \newunicodechar{∃}{\makebox[.5em]{\freeserif∃}}
        \newunicodechar{⊤}{\makebox[.5em]{\freeserif⊤}}
        \newunicodechar{∖}{\makebox[.5em]{\freeserif∖}}
        \newunicodechar{↦}{\makebox[.5em]{\freeserif↦}}
        \newunicodechar{□}{\makebox[.5em]{\freeserif□}}
        \newunicodechar{∘}{\makebox[.5em]{\freeserif∘}}

        \newfontfamily\greekfont{GFS Artemisia}[
           Scale=MatchUppercase
        ]
        \setTransitionsForGreek{\begingroup\greekfont}{\endgroup}

        %\usepackage[T1]{fontenc}
        %\usepackage[utf8]{inputenc}
        %\usepackage[american]{babel}
        %\usepackage[sc]{mathpazo}

        \usepackage{draftwatermark}
        \SetWatermarkText{DRAFT}
        \SetWatermarkScale{1}
        \SetWatermarkColor[gray]{0.95}

        %%% reduce spaces for Table of contents, figures and tables
        %%% it is used "\addtocontents{toc}{\vskip -1.2cm}" etc. in the document
        \usepackage[notlot,nottoc,notlof]{}

        \usepackage{color}
        \usepackage{transparent}
        \usepackage{eso-pic}
        \usepackage{lipsum}

        \usepackage{footnotebackref} %%link at the footnote to go to the place of footnote in the text

        %% spacing between line
        \usepackage{setspace}
        %%%%\onehalfspacing
        %%%%\doublespacing
        \singlespacing


        %%%%%%%%%%% datetime
        \usepackage{datetime}

        \newdateformat{MonthYearFormat}{%
            \monthname[\THEMONTH], \THEYEAR}


        %% RO, LE will not work for 'oneside' layout.
        %% Change oneside to twoside in document class
        \usepackage{fancyhdr}
        \pagestyle{fancy}
        \fancyhf{}

        %%% Alternating Header for oneside
        \fancyhead[L]{\ifthenelse{\isodd{\value{page}}}{ \small \nouppercase{\leftmark} }{}}
        \fancyhead[R]{\ifthenelse{\isodd{\value{page}}}{}{ \small \nouppercase{\rightmark} }}

        %%% Alternating Header for two side
        %\fancyhead[RO]{\small \nouppercase{\rightmark}}
        %\fancyhead[LE]{\small \nouppercase{\leftmark}}

        %% for oneside: change footer at right side. If you want to use Left and right then use same as header defined above.
        %\fancyfoot[R]{\ifthenelse{\isodd{\value{page}}}{{\tiny Meher Krishna Patel} }{\href{http://pythondsp.readthedocs.io/en/latest/pythondsp/toc.html}{\tiny PythonDSP}}}

        %%% Alternating Footer for two side
        %\fancyfoot[RO, RE]{\scriptsize Meher Krishna Patel (mekrip@gmail.com)}

        %%% page number
        \fancyfoot[CO, CE]{\thepage}

        \renewcommand{\headrulewidth}{0.5pt}
        \renewcommand{\footrulewidth}{0.5pt}

        \RequirePackage{tocbibind} %%% comment this to remove page number for following
        \addto\captionsenglish{\renewcommand{\contentsname}{Table of contents}}
        \addto\captionsenglish{\renewcommand{\listfigurename}{List of figures}}
        \addto\captionsenglish{\renewcommand{\listtablename}{List of tables}}
        % \addto\captionsenglish{\renewcommand{\chaptername}{Chapter}}


        %%reduce spacing for itemize
        \usepackage{enumitem}
        \setlist{nosep}

        %%%%%%%%%%% Quote Styles at the top of chapter
        \usepackage{epigraph}
        \setlength{\epigraphwidth}{0.8\columnwidth}
        \newcommand{\chapterquote}[2]{\epigraphhead[60]{\epigraph{\textit{#1}}{\textbf {\textit{--#2}}}}}
        %%%%%%%%%%% Quote for all places except Chapter
        \newcommand{\sectionquote}[2]{{\quote{\textit{``#1''}}{\textbf {\textit{--#2}}}}}
    ''',


    'maketitle': r'''
        \pagenumbering{Roman} %%% to avoid page 1 conflict with actual page 1

        \begin{titlepage}
            \centering

            \vspace*{40mm} %%% * is used to give space from top

            \vspace{0mm}
            \begin{figure}[!h]
                \centering
                \includegraphics[scale=0.7]{../../images/brlogo.png}
            \end{figure}
            \vspace{15mm}
            \textbf{\Huge {How to BedRock a Driver}}

            \vspace{20mm}
            \Large \textbf{Gordon Stewart}%
                   \footnote{Based on joint work with G. Malecha, D. Swasey, P. Giarrusso, M. Ershov, S. Bundela, and U. Steinberg}

            \MonthYearFormat\today

            %% \vfill adds at the bottom
            \vfill
        \end{titlepage}

        \clearpage
        \pagenumbering{roman}
        \tableofcontents
        \listoffigures
        %\listoftables
        \clearpage
        \pagenumbering{arabic}

        ''',
    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',
    'sphinxsetup': \
        'hmargin={1.2in,1.2in}, vmargin={1in,1in}, \
        verbatimwithframe=true, \
        TitleColor={rgb}{0,0,0}, \
        HeaderFamily=\\rmfamily\\bfseries, \
        InnerLinkColor={rgb}{0,0,1}, \
        OuterLinkColor={rgb}{0,0,1}',

        'tableofcontents':' ',
}

latex_logo = 'images/brlogo.png'

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    ('drivers', 'drivers.tex', 'How to BedRock a Driver',
     'Gordon Stewart', 'report')
]
