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

def drawDescartes(expr x, y) =
  begingroup; save d;
    % NOTE: this value is twice of the current font size (12pt)
    numeric d;
    d := 24pt;

    % drawdot origin withpen pencircle scaled 4pt;
    drawarrow(-d,0)--(x,0); % x-axes
    drawarrow(0,-d)--(0,y); % y-axes

    % NOTE: valid label suffixes: lft | rt | top | bot | ulft | urt | llft | lrt
    label.llft(btex $0$ etex, (0,0));
    label.rt  (btex $x$ etex, (x,0));
    label.top (btex $y$ etex, (0,y));
  endgroup;
enddef;

%% Metaobj Classes

%% Metaobj Methods

%%%%%%%%%%%%%%%%
%% Figures
%%%%%%%%%%%%%%%%

% The differentiation process of \holtxt{diffl}
beginfig(0);
  begingroup; save u, w, P, f, s, t, h;
    % (u,w) is the total size of the main area
    numeric u, w;
    u := 4.6cm; w := 8cm;
    drawDescartes(w, u);

    pair P, P';
    P := (1cm,1cm); label.ulft(btex $P$ etex, P);
    drawdot P withpen pencircle scaled 4pt;

    path f;
    f := P{dir 45}..{dir -20}(7cm,3cm);
    draw f withpen pencircle scaled 1.5pt;
    label.urt(btex \begin{small}$y=f(x)$\end{small} etex, (7cm,3cm));

    % The tangent
    path t, t';
    t' := origin--(3.8cm,3.8cm);
    t := t' shifted P;
    draw t;

    % The secant
    path s; s := t' rotated -15 shifted P; % P--(6cm,4cm);
    draw s;

    % NOTE: use "subpath" to prevent the first intersection point at P
    P' = f intersectionpoint (subpath (0.2,1) of s);
    drawdot P' withpen pencircle scaled 4pt;
    label.top(btex $P'$ etex, P');

    % other solid lines
    path h; h := P--(xpart P',ypart P);
    draw h;
    draw (xpart P',ypart P)--P';
    
    % The angles
    drawarrow (6.5cm,0){up}..(0,6.5cm){left} cutbefore s cutafter t dashed evenly;
    drawdblarrow (xpart P + 2cm,ypart P){up}..(ypart P,xpart P + 2cm){left}
      cutbefore h cutafter t;
    label.urt(btex \begin{small}$\alpha$\end{small} etex,
        (xpart P + 1.9cm,ypart P + 0.6cm));

    % other dashed lines
    draw (xpart P,0)--P dashed evenly;
    draw (0, ypart P)--P dashed evenly;
    label.lft(btex \begin{small}$f(x)$\end{small} etex, (0, ypart P));
    draw (xpart P',0)--(xpart P',ypart P) dashed evenly;
    label.bot(btex $x$ etex, (xpart P,0));
    label.bot(btex $x+h$ etex, (xpart P',0));
    label.bot(btex \begin{small}$h\rightarrow 0$\end{small} etex, ((xpart P + xpart P')/2, ypart P));
    draw (0, ypart P')--P' dashed evenly;
    label.lft(btex \begin{small}$f(x+h)$\end{small} etex, (0, ypart P'));
    label.rt(btex \begin{small}$f(x+h)-f(x)$\end{small} etex,
        (xpart P',(ypart P' + ypart P)/2));
  endgroup;
endfig;

% The differentiation process of \holtxt{has_derivative}
beginfig(1);
  begingroup; save u, w, P, Q, f, s, t, h;
    % (u,w) is the total size of the main area
    u := 4.6cm; w := 8cm;
    drawDescartes(w, u);

    pair P, P';
    P := (1cm,1cm); label.ulft(btex $P$ etex, P);
    drawdot P withpen pencircle scaled 4pt;

    path f;
    f := P{dir 45}..{dir -20}(7cm,3cm);
    draw f withpen pencircle scaled 1.5pt;
    label.urt(btex \begin{small}$y=f(x)$\end{small} etex, (7cm,3cm));

    % The tangent (t)
    path t, t';
    t' := origin--(3.8cm,3.8cm);
    t := t' shifted P;
    draw t;

    % The secant
    path s; s := t' rotated -15 shifted P; % P--(6cm,4cm);
    draw s;

    % NOTE: use "subpath" to prevent the first intersection point at P
    P' = f intersectionpoint (subpath (0.2,1) of s);
    drawdot P' withpen pencircle scaled 4pt;
    label.ulft(btex $P'$ etex, P');

    % other solid lines
    path h; h := P--(xpart P',ypart P);
    draw h;
    path v; v := (xpart P',ypart P)--(xpart P',5cm);
    draw v cutafter t;
    pair Q; Q := (v intersectionpoint t);
    drawdot Q withpen pencircle scaled 4pt;
    label.ulft(btex $f'$ etex, (4cm,4cm));
    label.rt(btex \begin{small}$|f(x')-f(x)-f'(x'-x)|$\end{small} etex, 1/2[Q,P']);

    % other dashed lines
    draw (xpart P,0)--P dashed evenly;
    draw (0, ypart P)--P dashed evenly;
    label.lft(btex \begin{small}$f(x)$\end{small} etex, (0, ypart P));
    draw (xpart P',0)--(xpart P',ypart P) dashed evenly;
    label.bot(btex $x$ etex, (xpart P,0));
    label.bot(btex $x'$ etex, (xpart P',0));
    label.bot(btex \begin{small}$|x'-x|\rightarrow 0$\end{small} etex, ((xpart P + xpart P')/2, ypart P));
    draw (0, ypart P')--P' dashed evenly;
    label.lft(btex \begin{small}$f(x')$\end{small} etex, (0, ypart P'));
    label.rt(btex \begin{small}$f(x')-f(x)$\end{small} etex,
        (xpart P',(ypart P' + ypart P)/2));
  endgroup;
endfig;

% This ending part is actually not necessary
verbatimtex
  \end{document}
etex

% And this last "end." is mandatory for "mpost" to terminate
end.
