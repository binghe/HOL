% !TEX encoding = UTF-8 Unicode
% !TEX TS-program = nv-metafun
% !MPOST tex = latex

% This is an example of a MetaFun macro (externalfigure) used in a figure whose
% labels are typeset with LaTeX. This file can be also typeset by
% nv-metapost.engine, although the preview won't display the external figure
% (but metafun-latex-label-0.pdf will be correct): just remove the leading %
% from the following directive:

%% !MPOST mem = metafun

% To compile this from the command line, use:
%
%  mpost -mem=metafun -tex=latex <this file>
%
% To see generated figures in PDF:
%
%  mptopdf figs/0.mps
%

% In PostScript output mode, when prologues is 3, the MetaPost output will be EPSF but will
% contain the PostScript font(s) (or a subset)
prologues := 3;

% MetaPost’s PostScript output is a low-featured dialect of the Postscript language,
% called purified EPS, which can be converted into the Portable Document Format (PDF)
% language on-the-fly (when using the pdfTEX engine with a built-in PDF output driver).
outputtemplate := "figs/%c.mps";

% see "Drawing Boxes with MetaPost" for the tradition box package
% obsoleted (use metaobj's newBox instead)
% input boxes;
input rboxes;

% see "The METAOBJ tutorial and reference manual" by Denis Roegel
input metaobj;

% see "FEATPOST Manual" (MetaPost macros for 3D) by L. Nobre G.
input featpost;

% Finite state machines, graphs and trees in MetaPost
input automata;

% see "Drawing Graphs with MetaPost" by John D. Hobby
input graph;

% see "The mpcolornames package" by Stephan Hennig
input mpcolornames;

% The TEX macro is useful when using MP variables in TeX/LaTeX labels.
% It is slow, but more general than the standard btex..etex construction.
input TEX;
TEXPRE ("\documentclass[12pt]{book}" &
  "\usepackage[T1]{fontenc}\usepackage[utf8]{inputenc}" &
  "\usepackage{amsmath}\usepackage{amssymb}" &
  "\begin{document}");
TEXPOST("\end{document}");

%% Full LaTeX settings (metafun only), copy code to TEXPRE when necessary
verbatimtex
  \documentclass[12pt]{book}
  \usepackage[T1]{fontenc}
  \usepackage[utf8]{inputenc}
  \usepackage{amsmath}
  \usepackage{amssymb}
  \begin{document}
etex

%% Global Parameters
show_empty_boxes := true;
defaultcolormodel := rgbmodel; % use greyscalemodel for black-and-white figs

%% General Macros

%% Metaobj Classes

%% Metaobj Methods

%%%%%%%%%%%%%%%%
%% Figures
%%%%%%%%%%%%%%%%

beginfig(0);
  begingroup; save x, y;
    drawdot(0,0);
  endgroup;
endfig;

% This ending part is actually not necessary
verbatimtex
  \end{document}
etex

end.
