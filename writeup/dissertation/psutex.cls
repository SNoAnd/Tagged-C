\newcommand{\filename}{psutex}
\newcommand{\fileversion}{v1.2}
\newcommand{\filedate}{2022/09/20}

%----------------------------------------
% Adapted from BeavTex, part of OSU thesis template on Overleaf
%----------------------------------------

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{\filename}[\filedate\space\fileversion\space PSUTeX: Portland State thesis class]

\RequirePackage{setspace}
\RequirePackage{ifthen}
\RequirePackage[normalem]{ulem}
\newcommand{\ulinewithbreaks}[1]{\expandafter\uline\expandafter{#1}}

% -------------------------------------------------------------------------------
% psutex is a modified (default 12pt) book style. it accepts these options:

% [10pt], [11pt], and [12pt]. These options are passed to book class. The
% default is 12pt.

% [1.5in], [1.7in]. These two options set the left margin. Default is 1.7
% inches.

% [onehalf], [double]. These two options set the line spacing. Default is
% double.

% [preprint], [submission]. When [preprint] is set, it is assumed that the
% thesis is printed double-sided, opens right (so that every chapter begins on
% an odd page). Date is included in the header, along with the word "Draft". In
% the submission version, it is assumed that the document will be printed
% single-sided. Default is submission.
    
% [seploa]. When [seploa] is set, the appendices do not appear in the main table
% of contents (except for the entry "appendices" itself). Rather, they are
% listed in the list of appendices. According to T.G., you need this if you have
% more than five appendices. It is not set by default.
% -------------------------------------------------------------------------------
\newcommand{\bookclass}{book}

% Font size, this option is passed to book class. Default is 12pt.
\newcommand{\@ftsize}{}
\DeclareOption{10pt}{\renewcommand{\@ftsize}{10pt}}
\DeclareOption{11pt}{\renewcommand{\@ftsize}{11pt}}
\DeclareOption{12pt}{\renewcommand{\@ftsize}{12pt}}

% Left side margin. 
% [1.5in], [1.7in].
% default is 1.7, unless [1.5in] is specified.
\newcommand{\@lmarwidth}{}
\newcommand{\@smarwidth}{}
\newcommand{\@texwidth}{}

\DeclareOption{1.5in}{%
  \renewcommand{\@lmarwidth}{.5in}%
  \renewcommand{\@smarwidth}{.0in}%
  \renewcommand{\@texwidth}{6.0in}%
}
\DeclareOption{1.7in}{%
  \renewcommand{\@lmarwidth}{.7in}%
  \renewcommand{\@smarwidth}{.0in}%
  \renewcommand{\@texwidth}{5.8in}%
}

% One and half or double spacing?
% [onehalf], [double].
% default is double, unless [onehalf] is specified.
\newcommand{\@spacing}{}
\DeclareOption{onehalf}{\renewcommand{\@spacing}{\onehalfspacing}}
\DeclareOption{double}{\renewcommand{\@spacing}{\doublespacing}}
\AtEndOfClass{\@spacing}

% Draft or final version?
% [preprint], [submission]
% Default is submission.
\newif\if@preprint

\DeclareOption{preprint}{\@preprinttrue}
\DeclareOption{submission}{\@preprintfalse}

% [seploa]
\newif\if@seploa
\@seploafalse
\DeclareOption{seploa}{\@seploatrue}

% Other options are passed to the book class.
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{\bookclass}}

% These are the default options.
\ExecuteOptions{12pt,1.7in,double,submission}
\ProcessOptions\relax

\if@preprint
\PassOptionsToClass{twoside,openright}{\bookclass}
\else
\PassOptionsToClass{oneside,openany}{\bookclass}
\fi

\PassOptionsToClass{\@ftsize}{\bookclass}

\LoadClass[letterpaper,onecolumn]{\bookclass}

% -------------------------------------------------------------------------------
% Set up page layout.

% \evensidemargin is used when [twoside] is set (by [preprint]).
\setlength{\oddsidemargin}{\@lmarwidth}
\setlength{\evensidemargin}{\@smarwidth}
\setlength{\textwidth}{\@texwidth}
% Other margins.
\setlength{\topmargin}{0in}
\setlength{\headheight}{.5in}
\setlength{\headsep}{.3in}
\setlength{\footskip}{.5in}

% -------------------------------------------------------------------------------
% Font size for headings. 
% Use \heading when you typeset a heading.
\newcommand{\heading}{\fontsize{12}{14.5}\bf\selectfont}
\newcommand{\chapterheading}{\fontsize{12}{14.5}\bf\selectfont}
%-------------------------------------------------------------------------------
% Misc commands 

% Redefine the default (plain) pagestyle
\renewcommand{\ps@plain}{%
  \renewcommand{\@oddhead}{%
    \ifnum\value{page}=0\else
    \if@preprint
    \textit{\small Draft}\hfil\@formatdate
    \fi
    \hfil\thepage
    \fi
  }
  \renewcommand{\@evenhead}{%
    \thepage\hfil\@formatdate\hfil\textit{\small Draft}%
  }
  \renewcommand{\@oddfoot}{}
  \renewcommand{\@evenfoot}{}
}

\newcommand{\@formatdate}{%
  \textit{\scriptsize {\number\year/\number\month/\number\day}}%
}

% To clear completely empty pages. It's not really that necessary. The
% submission version is single-sided and won't need this anyway.
\renewcommand{\cleardoublepage}{%
  \clearpage%
  \if@twoside%
  \ifodd\c@page%
  \else\mbox{}\thispagestyle{empty}\newpage%
  \if@twocolumn\mbox{}\newpage\fi\fi\fi%
}



% Authors: use \mainmatter before the main content
\renewcommand{\mainmatter}{%
  \cleardoublepage%
  \@mainmattertrue%
  \pagestyle{plain}
  \setcounter{page}{1}%
  \pagenumbering{arabic}%
}

% T.G. : Figures and tables in the appendices should be listed in separate
% lists. So we will put them in separate files (loaf and loat). Use
% \listofappendixfigures and \listofappendixtables to make the listings.

% Authors: use \appendix before you begin the appendix to generate the appendix
% page and to set up some relevant variables.

\newif\if@appendix

\newcommand{\ext@toc}{toc}

\renewcommand\appendix{%
  \cleardoublepage%
  \@appendixtrue%
  \setcounter{chapter}{0}%
  \setcounter{section}{0}%
  \gdef\@chapapp{\appendixname}%
  \gdef\thechapter{\@Alph\c@chapter}%
  \renewcommand{\ext@figure}{loaf}%
  \renewcommand{\ext@table}{loat}%
  \if@seploa\def\ext@toc{loap}\fi%
  \addcontentsline{toc}{chapter}{Appendices}%
  \appendixpage%
}

% T.G. : An appendix page is required before the appendices.
\newcommand{\appendixpage}{%
  \vspace*{0.3\textheight}
  \begin{center}{\heading APPENDICES}\end{center}%
  \clearpage%
}

% Redefine \@chapter, so that appendices are added in .loap file if [seploa] is
% set. Also, I commented out the lines adding space between figures/tables of
% different chapters. I am not sure yet if it is necessary. The following code
% is pretty much copied from book.cls. If it looks messy, don't blame me :P
\def\@chapter[#1]#2{
  \ifnum \c@secnumdepth >\m@ne
    \if@mainmatter
      \refstepcounter{chapter}
      \typeout{\@chapapp\space\thechapter.}
      \addcontentsline{\ext@toc}{\if@appendix app\else chapter\fi}{\protect\numberline{\thechapter}#1}
    \else
      \addcontentsline{\ext@toc}{chapter}{#1}
    \fi
  \else
    \addcontentsline{\ext@toc}{chapter}{#1}
  \fi
  \chaptermark{#1}
  \addtocontents{\ext@figure}{\protect\addvspace{10\p@}}
  \addtocontents{\ext@table}{\protect\addvspace{10\p@}}
	\ifthenelse{\isundefined{\listofalgorithms}}{}{
  	\addtocontents{\ext@algorithm}{\protect\addvspace{10\p@}}
  }
  \if@twocolumn
    \@topnewpage[\@makechapterhead{#2}]
  \else
    \@makechapterhead{#2}
    \@afterheading
  \fi
}

% T.G. : These elements should be single-spaced: Blocked quotes, bibliography,
% footnotes, endnotes, multiple-line headers, figure titles, listed items
% (optional).

% Bibliography: Redefine the bibliography to make it single-spaced.
\renewcommand{\bibliography}[1]{%
  \if@filesw
    \immediate\write\@auxout{\string\bibdata{#1}}%
  \fi
  \addcontentsline{toc}{chapter}{Bibliography}
  \begin{singlespacing}
  \@input@{\jobname.bbl}
  \end{singlespacing}
}

% Footnotes: they are not effected by linespacing anyway (always single-spaced).
% Multiple-line headers: as long as we use \heading, it's single-spaced.
% Others: I am not sure yet...

% User definitions.
% A definition generator for variables.
% #1: optional default value, if missing, the variable is mandatory. Failing to
% define it will raise a latex error.
% #2: command to define the variable
% \define{somevar} will define a new command \somevar with 1 parameter. It
% stores the contents to a variable \@somevar.

\newcommand{\definevar}[2][-]{%
  \expandafter\def\csname #2\endcsname{%
    \expandafter\gdef\csname @#2\endcsname
  }
  \if#1-
  \csname #2\endcsname{\@latex@error{No #2 defined}\@ehc}
  \else
  \csname #2\endcsname{#1}
  \fi
}

\definevar{title}
\definevar{author}
\definevar{doctype}
\definevar{university}
\definevar{graddegree}
\definevar{major}
\definevar{department}
\definevar{committeemembers}

\definevar[\today]{submitdate}
\definevar[\the\year]{commencementyear}

\definevar{abstract}
\definevar[*]{nopretext}

% \xxxcontent commands will be generated when we generate definitions for the
% pretext pages. the following definitions provide backward compatibility and
% nicer names.
\newcommand{\acknowledgements}{\ackcontent}
\newcommand{\contributors}{\contricontent}
\newcommand{\preface}{\prefcontent}
\newcommand{\dedication}{\dedcontent}

%-------------------------------------------------------------------------------
% Document parts. See T.G.
%-------------------------------------------------------------------------------
\newcommand{\emptyline}{\mbox{}\newline}


% Flyleaf, a blankpage
\newcommand{\flyleaf}{\thispagestyle{empty}\phantom{}\newpage}

% Copyright page
\newcommand{\copyrightpage}{
  \begin{singlespacing}
  \thispagestyle{empty}
  \vspace*{10\baselineskip}
  \begin{center}
    ${}^\copyright$Copyright by \@author\\
    \@submitdate \\
    All Rights Reserved
  \end{center}
  \end{singlespacing}
  \clearpage
}

% Title page
\renewcommand{\titlepage}{
    \thispagestyle{empty}
    \begin{center}
      
      \@title \\
      \setlength{\baselineskip}{14.5pt}
      \vfill
      \emptyline by\\ \emptyline
      \@author\\
      \vfill
      A \MakeLowercase{\@doctype} submitted in partial fulfillment of the\\
      requirements for the degree of\\
      \vfill
      \@graddegree \\
      in\\
      \@department
      \vfill
      \@doctype~Committee:\\
      \@committeemembers\\
      \vfill
      \@university\\
      \@commencementyear\\
    \end{center}
  \clearpage
}


\definevar[*]{dedcontent}
\newcommand{\dedpage}{
  \if \@dedcontent *
  \else
  \thispagestyle{empty}
  \vspace*{10\baselineskip}
  \begin{center}
  \@dedcontent
  \end{center}
  \clearpage
  \fi
}

% Format all of the frontmatter
% The commands for optional pages will check if the content is defined. If not,
% the page will not be produced. There is no need to check here.
\newcommand{\pretext}{%
  
  % Mandatory pages
  \titlepage         % D. Title page
  \pagenumbering{roman}
%  \flyleaf           % A. Flyleaf
%  \abspage           % B. Abstract
%  \copyrightpage     % C. Copyright page
%  \approvalpage      % E. Approval page

}

\renewcommand{\maketitle}{\if\@nopretext \else\pretext\fi}

% T.G. : A flyleaf is needed at the end of the thesis.
\AtEndDocument{\clearpage}

% Chapter heading. T.G. : all title must be the same size (14 or normal).
\renewcommand{\@makechapterhead}[1]{%
  \vspace*{10\p@}%
  {
    \begin{center}
      \normalfont\heading
      \ifnum \c@secnumdepth >\m@ne
    %   \if@mainmatter\heading\@chapapp\ \thechapter:\ \fi % this includes "Chapter #:" in the chapter numbering
      \if@mainmatter\chapterheading\thechapter\hspace{1em}\ \fi
      \fi
      \chapterheading #1\par\nobreak
      \vskip 20\p@
    \end{center}
  }
}

% Silent chapter heading (\chapter*).
\renewcommand{\@makeschapterhead}[1]{%
  \vspace*{10\p@}%
  {
    \begin{center}
      \normalfont\chapterheading
      \chapterheading #1\par\nobreak
      \vskip 20\p@
    \end{center}
  }
}

\def\@sect#1#2#3#4#5#6[#7]#8{%
  \ifnum #2>\c@secnumdepth
    \let\@svsec\@empty
  \else
    \refstepcounter{#1}%
    \protected@edef\@svsec{\@seccntformat{#1}\relax}%
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@
    \begingroup
      #6{%
        \@hangfrom{\hskip #3\relax\@svsec}%
          \interlinepenalty \@M #8\@@par}%
    \endgroup
    \csname #1mark\endcsname{#7}%
    \if@appendix \else
      \addcontentsline{\ext@toc}{#1}{%
      \ifnum #2>\c@secnumdepth \else
        \protect\numberline{\csname the#1\endcsname}%
      \fi
      #7}%
      \fi
  \else
    \def\@svsechd{%
      #6{\hskip #3\relax
      \@svsec #8}%
      \csname #1mark\endcsname{#7}%
      \if@appendix \else
        \addcontentsline{\ext@toc}{#1}{%
         \ifnum #2>\c@secnumdepth \else
           \protect\numberline{\csname the#1\endcsname}%
         \fi
         #7}%
       \fi}%
  \fi
  \@xsect{#5}}

\renewcommand{\section}{\@startsection
  {section}%                   % the name
  {1}%                         % the level
  {0mm}%                       % the indent
  {-\baselineskip}%            % the before skip
  {0.5\baselineskip}%          % the after skip
  {\normalfont\heading}}       % the style

\renewcommand{\subsection}{\@startsection
  {subsection}%                % the name
  {1}%                         % the level
  {0mm}%                       % the indent
  {-\baselineskip}%            % the before skip
  {0.5\baselineskip}%          % the after skip
  {\normalfont\heading}}       % the style

\renewcommand{\subsubsection}{\@startsection
  {subsubsection}%             % the name
  {1}%                         % the level
  {0mm}%                       % the indent
  {-\baselineskip}%            % the before skip
  {0.5\baselineskip}%          % the after skip
  {\normalfont\heading}}       % the style

% Listings. l@kind handles an entry of a "kind" in the listing
% T.G. : No bold faces should appear in the pretext (including the listings, of
% course). This is why l@chapter is being redefined here.
\def\l@chapter#1#2{%
  \ifnum \c@tocdepth >\m@ne
    \addpenalty{-\@highpenalty}%
    \vskip 1.0em \@plus\p@
    \setlength\@tempdima{1.5em}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      \leavevmode %\large
      \advance\leftskip\@tempdima
      \hskip -\leftskip
%     #1\nobreak\hfil \nobreak\hb@xt@\@pnumwidth{\hss #2}\par  %Old version without dots in the Chapter part of the TOC
      #1\nobreak\normalfont\leaders\hbox{$\m@th
        \mkern \@dotsep mu\hbox{.}\mkern \@dotsep
        mu$}\hfill\nobreak\hb@xt@\@pnumwidth{\hss #2}\par
      \penalty\@highpenalty
    \endgroup
  \fi}

% For separate listings of appendices ([seploa] is set), every appendix is
% listed the same as a chapter, otherwise it is like a section. not sure if it's
% the optimal solution. but it looks nice for now.
\def\l@app#1#2{%
  \if@seploa\l@chapter{#1}{#2}
  \else
  {\vskip 4pt {\baselineskip 14.5pt%
    \@dottedtocline{1}{1pc}{2em}{#1}{#2}}}
  \fi
}

\def\l@section#1#2{\vskip 4pt {\baselineskip 14.5pt%
    \@dottedtocline{1}{1pc}{2em}{#1}{#2}} }
\def\l@subsection#1#2{ {\baselineskip 14.5pt%
    \@dottedtocline{2}{4pc}{2.8em}{#1}{#2}}}
\def\l@subsubsection#1#2{{\baselineskip 14.5pt%
    \@dottedtocline{3}{7pc}{3.4em}{#1}{#2}}}
\def\l@figure#1#2{\vskip 9.5pt {\baselineskip 14.5pt%
    \@dottedtocline{1}{1.5em}{2.3em}{#1}{#2}}}
\let\l@table\l@figure

% We want to ignore footnotes in any listing. If this is not what you want,
% change the line starting with \let\footnote in \definelisting
\newcommand{\@ignore}[1]{}

% There are these kinds of listings:
% Table of contents (toc)
% List of figures (lof)
% List of tables (lot)
% List of appendices (loap)
% List of appendix tables (loat)
% List of appendix figures (loaf)

% A definition generator for listings. It generates two page styles (one for the
% first page, one for the rest) and a command.
% #1 : file extension name
% #2 : full name (to appear as the heading of the listing)
% #3 : short name (to appear as the heading on the top of the left column)
% #4 : command name (to be used to make the listing)
\newcommand{\definelisting}[4]{
  \expandafter\def\csname #4\endcsname{%
    \cleardoublepage
    \chapter*{#2}
    \ifthenelse{\equal{#3}{}} {} {\addcontentsline{toc}{chapter}{#2}}
    {\let\footnote\@ignore\@starttoc{#1}}
  }
}

\definelisting{toc}{Table of Contents}{}{tableofcontents}
\definelisting{lof}{List of Figures}{Figure}{listoffigures}
\definelisting{lot}{List of Tables}{Table}{listoftables}
\definelisting{loap}{List of Appendices}{}{listofappendices}
\definelisting{loaf}{List of Appendix Figures}{Figure}{listofappendixfigures}
\definelisting{loat}{List of Appendix Tables}{Table}{listofappendixtables}

\endinput
