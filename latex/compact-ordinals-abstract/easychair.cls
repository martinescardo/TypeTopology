%
% Some credits
%

\def\easychairstyleauthor{easychair class style, by Serguei A. Mokhov and Andrei Voronkov <10 December 2015>}
\def\easychairstylerevision{CVS Revision: $Id: easychair.cls,v 3.4 2017/03/26 09:52 voronkov Exp $}
\def\easychairstylepurpose{Designed for easyChair.org, under guidelines and suggestions of}
\def\easychairstylevoronkov{\space\space\space\space\space\space\space\space\space\space\space\space\space Andrei Voronkov <www.voronkov.com>, and}
\def\easychairstylesutcliffe{\space\space\space\space\space\space\space\space\space\space\space\space\space Geoff Sutcliffe <www.cs.miami.edu/^geoff>}
\def\easychairstylecopyright{Copyright terms are that of easychair.org}
\def\easychairstylebugs{For bug reports, please contact <andrei@voronkov.com>}

\everyjob{\typeout{\easychairstyleauthor}}
\everyjob{\typeout{\easychairstylerevision}}
\everyjob{\typeout{\easychairstylepurpose}}
\everyjob{\typeout{\easychairstylevoronkov}}
\everyjob{\typeout{\easychairstylesutcliffe}}
\everyjob{\typeout{\easychairstylecopyright}}
\everyjob{\typeout{\easychairstylebugs}}

\immediate\write10{\easychairstyleauthor}
\immediate\write10{\easychairstylerevision}
\immediate\write10{\easychairstylepurpose}
\immediate\write10{\easychairstylevoronkov}
\immediate\write10{\easychairstylesutcliffe}
\immediate\write10{\easychairstylecopyright}
\immediate\write10{\easychairstylebugs}

%
% Require LaTeX 2.09 or later
%

\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{easychair}[2017/03/26 v3.5]
\def\@tempa#1#2\@nil{\edef\@classname{#1}}
\expandafter\@tempa\@currnamestack{}{}{}\@nil
\ifx\@classname\@empty \edef\@classname{\@currname}\fi

\RequirePackage{xcolor}

%
% Debug
%

\def\easychairdebug#1{\gdef\@EasyDebug{#1}}
\def\@EasyDebug{}

\newif\ifdebug
\debugfalse
\DeclareOption{debug}{\debugtrue}

\newif\ifEPiC
\EPiCfalse
\DeclareOption{EPiC}{\EPiCtrue}
\newif\ifKalpa
\Kalpafalse
\DeclareOption{Kalpa}{\Kalpatrue}

% EPiC with the empty header
\newif\ifEPiCempty
\EPiCemptyfalse
\DeclareOption{EPiCempty}{\EPiCemptytrue}

% Kalpa with the empty header
\newif\ifKalpaempty
\Kalpaemptyfalse
\DeclareOption{Kalpaempty}{\Kalpa emptytrue}

\newif\ifEPiCfinal
\EPiCfinalfalse
\DeclareOption{EPiCfinal}{\EPiCfinaltrue}

\def\easychairframe#1{\gdef\@EasyFrame{#1}}
\def\@EasyFrame{}

\newif\ifframe
\framefalse

\DeclareOption{frame}{\frametrue}

\def\easychairverbose#1{\gdef\@EasyVerbose{#1}}
\def\@EasyVerbose{}

\newif\ifverbose
\verbosefalse

\DeclareOption{verbose}{\verbosetrue}


%
% Thesis
% Perh Geoff, February 23, 2010 with support from Andrei
%

\def\easythesis#1{\gdef\@EasyThesis{#1}}
\def\@EasyThesis{}

\newif\ifthesis
\thesisfalse

\DeclareOption{thesis}{\thesistrue}


%
% Times New Roman or not
%

\def\easytimes#1{\gdef\@EasyTimes{#1}}
\def\@EasyTimes{}

\newif\ifnotimes
\notimesfalse

\DeclareOption{notimes}{\notimestrue}

\newif\ifwithtimes
\withtimesfalse

\DeclareOption{withtimes}{\withtimestrue}


%% Code added to use llncs style author list
\newcounter{@inst}
\newcounter{@auth}
\newcounter{auco}
\newdimen\instindent
\def\institute#1{\gdef\@institute{#1}}

\def\institutename{\par
 \begingroup
 \parskip=\z@
 \parindent=\z@
 \setcounter{@inst}{1}%
 \def\and{\par\stepcounter{@inst}%
 \noindent$^{\the@inst}$\enspace\ignorespaces}%
 \setbox0=\vbox{\def\thanks##1{}\@institute}%
 \ifnum\c@@inst=1\relax
   \gdef\fnnstart{0}%
 \else
   \xdef\fnnstart{\c@@inst}%
   \setcounter{@inst}{1}%
   \noindent$^{\the@inst}$\enspace
 \fi
 \ignorespaces
 \@institute\par
 \endgroup}

\def\inst#1{\unskip$^{#1}$}
\def\fnmsep{\unskip$^,$}
\def\email#1{{\tt#1}}

%%

\newif\ifauthorundefined
\authorundefinedtrue

\let\oldauthor=\author
\renewcommand
	{\author}
	[1]
	{%
		\ifauthorundefined
			\oldauthor{#1}
			\authorundefinedfalse
		\else
			\PackageWarning{easychair}{Another use of author ignored}
		\fi
	}

\newif\iftitleundefined
\titleundefinedtrue

\let\oldtitle=\title
\renewcommand
	{\title}
	[1]
	{
		\iftitleundefined
			\oldtitle{#1}
			\titleundefinedfalse
		\else
			\PackageWarning{easychair}{Another use of title ignored}
		\fi
	}


%
% Running heads definitions
%

%\def\titlerunning#1{\gdef\@titleRunning{#1}}
%\def\authorrunning#1{\gdef\@authorRunning{#1}}
%\titlerunning{easychair: Running title head is undefined.}
%\authorrunning{easychair: Running author head is undefined.}

\newif\iftitlerunningundefined
\titlerunningundefinedtrue

\newif\ifauthorrunningundefined
\authorrunningundefinedtrue

\gdef\@titleRunning{easychair: Running title head is undefined.}
\gdef\@authorRunning{easychair: Running author head is undefined.}

\def\titlerunning#1
{
	\iftitlerunningundefined
		\gdef\@titleRunning{#1}
		\titlerunningundefinedfalse
	\else
		\PackageWarning{easychair}{Another use of titlerunning ignored}
	\fi
}

\def\authorrunning#1
{
	\ifauthorrunningundefined
		\gdef\@authorRunning{#1}
		\authorrunningundefinedfalse
	\else
		\PackageWarning{easychair}{Another use of authorrunning ignored}
	\fi
}

%
% Affiliations
%

\newcommand{\affiliation}[1]{\footnotesize{#1}\vspace{-3pt}}


%
% Decide between letter and A4 paper formats
% as well as orientation
%

% Default is 'letterpaper'
\def\paperformat#1{\gdef\@PaperFormat{#1}}
\def\@PaperFormat{letterpaper}

\newif\ifletterpaper
\newif\ifafourpaper
\newif\ifcustompaper

\letterpapertrue

\DeclareOption{letterpaper}{\paperformat{letterpaper}\afourpaperfalse\custompaperfalse}
\DeclareOption{a4paper}{\paperformat{a4paper}\afourpapertrue\letterpaperfalse\custompaperfalse}
\DeclareOption{custompaper}{\paperformat{letterpaper}\afourpaperfalse\letterpaperfalse\custompapertrue}
\ExecuteOptions{letterpaper}

\newlength{\@LMarginSize}
\newlength{\@RMarginSize}
\newlength{\@TMarginSize}
\newlength{\@BMarginSize}

\DeclareOption{lmargin}{}
\DeclareOption{rmargin}{}
\DeclareOption{tmargin}{}
\DeclareOption{bmargin}{}


% Default is portrait {}
\def\paperorientation#1{\gdef\@PaperOrientation{#1}}
\def\@PaperOrientation{}

\DeclareOption{portrait}{\paperorientation{}}
\DeclareOption{landscape}{\paperorientation{landscape}}

% Two sided running heads for titlerunning and author running
% twosided is the default
\newif\iftwosided
\twosidedfalse

\DeclareOption{onesided}{}
\DeclareOption{twosided}{\twosidedtrue}

%
% Decide between 1- or 2-column formats
%

\def\columnCount#1{\gdef\@ColumnCount{#1}}
\def\@ColumnCount{onecolumn}

\DeclareOption{onecolumn}{}
\DeclareOption{twocolumn}{\columnCount{twocolumn}}

%
% Decide on line spacing
%

\def\lineSpacing#1{\gdef\@LineSpacing{#1}}
\def\@LineSpacing{1.0}

\DeclareOption{zerospacing}{\lineSpacing{0.0}}
\DeclareOption{singlespacing}{\lineSpacing{1.0}}
\DeclareOption{lineandhalfspacing}{\lineSpacing{1.5}}
\DeclareOption{doublespacing}{\lineSpacing{2.0}}

\DeclareOption{0.0}{\lineSpacing{0.0}}
\DeclareOption{1.0}{\lineSpacing{1.0}}
\DeclareOption{1.5}{\lineSpacing{1.5}}
\DeclareOption{2.0}{\lineSpacing{2.0}}

\DeclareOption{0.0pt}{\lineSpacing{0.0}}
\DeclareOption{1.0pt}{\lineSpacing{1.0}}
\DeclareOption{1.5pt}{\lineSpacing{1.5}}
\DeclareOption{2.0pt}{\lineSpacing{2.0}}

%
% Font point size; default is 10pt
%
% The \headheight will have to be changed later accordingly
% such that fancyhdr does not complain it is too small.
%

\def\baseFontSize#1{\gdef\@BaseFontSize{#1}}
\def\headHeightSize#1{\gdef\@HeadHeightSize{#1}}
\def\headSepSize#1{\gdef\@HeadSepSize{#1}}
\def\footSkipSize#1{\gdef\@FootSkipSize{#1}}

\def\@BaseFontSize{10pt}
\def\@HeadHeightSize{12.0pt}
\def\@HeadSepSize{16.0pt} % instead of the default 25pt
\def\@FootSkipSize{26.0pt} % instead of the default 30pt

\DeclareOption{8pt}{\PackageWarning{easychair}{Option '\CurrentOption' is not supported.}}
\DeclareOption{9pt}{\PackageWarning{easychair}{Option '\CurrentOption' is not supported.}}
\DeclareOption{10pt}{\baseFontSize{10pt}\headHeightSize{12.0pt}\headSepSize{16.0pt}\footSkipSize{26pt}}
\DeclareOption{11pt}{\baseFontSize{11pt}\headHeightSize{13.6pt}\headSepSize{23.0pt}\footSkipSize{28pt}}
\DeclareOption{12pt}{\baseFontSize{12pt}\headHeightSize{14.5pt}\headSepSize{25.0pt}\footSkipSize{30pt}}
\ExecuteOptions{10pt}

%
% Page sizing
%

%\newif\iffullpage
%\newif\ifsavetrees
%
%\DeclareOption{fullpage}{\fullpagetrue}
%\DeclareOption{savetrees}{\savetreestrue}

% Bark at any unknown package option
\DeclareOption*{\PackageWarning{easychair}{Unknown option '\CurrentOption'}}
\DeclareOption*{\PassOptionsToPackage{\CurrentOption}{geometry}}
%\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}

%\ExecuteOptions{centertags,portrait,10pt,twoside,onecolumn,final}
%\ExecuteOptions{}
\ProcessOptions\relax

%
% Required packages and classes.
%
% All must be standard as per most common LaTeX
% distributions.
%

\ifthesis
	\LoadClass[\@PaperFormat,\@PaperOrientation,\@ColumnCount,\@BaseFontSize,twoside]{report}
	\RequirePackage{makeidx}
\else
	% We are an article (more customized later)
	\LoadClass[\@PaperFormat,\@PaperOrientation,\@ColumnCount,\@BaseFontSize,twoside]{article}
	%\LoadClass[\@PaperFormat,\@PaperOrientation,\@ColumnCount,\@BaseFontSize]{article}
\fi

% Require UTF8 encoding, per Andrei Voronkov, to accomodate
% all sorts of author names.
%\RequirePackage[utf8]{inputenc}

% To ensure the footnotes are always at the bottom.
% IMPORTANT: footmisc should precede hyperref for the footnotes to hyperlink
%            correctly to their pages where they are at instead of always at
%            page 1. Per bug reports from a couple of users and a suggestion by
%            Uwe Pfeiffer.
\RequirePackage[bottom]{footmisc}

% TOC/thumbnail LHS preview in the PDFs as well as active URLs and other cross-refs
% Newer versions of hyperref declare a4paper or letterpaper as obsolete and issue warnings
\definecolor{linkcolor}{RGB}{170,0,0} % aa0000
\definecolor{citecolor}{RGB}{44,160,46} % 2ca02d
\definecolor{urlcolor}{RGB}{0,51,153} % 003399
\RequirePackage[linktocpage,pdfcreator=easychair.cls-3.4,colorlinks=True,urlcolor=urlcolor,citecolor=citecolor,linkcolor=linkcolor]{hyperref}

% Traditional graphics processing
\RequirePackage{graphicx}
%\RequirePackage{pdflscape}
%\RequirePackage{lscape}


%% Fonts, generally more compact but preserving point size

% Pick "Times Roman" as a base font unless explicitly told not to
\ifnotimes
	\ifwithtimes
		\PackageWarning{easychair}{Cannot really use 'notimes' and 'withtimes' together}
		\PackageWarning{easychair}{Defaulting to 'notimes'...}
	\else
		\PackageWarning{easychair}{'notimes' has been deprecated as it is the default in 2.0}
	\fi
\else
	\ifwithtimes
		\RequirePackage{mathptmx}
	\fi
\fi

% Pick "Helvetica" as a "Sans-Serif" font
%\RequirePackage[scaled=.85]{helvet}

% For algorithm and source code listings
\RequirePackage{listings}

%% Different Math and non-Math symbols and definitions

\RequirePackage{latexsym}
\RequirePackage{amsthm}
\RequirePackage{empheq}

%% Line spacing to be applied AFTER the above space saving packages

\renewcommand{\baselinestretch}{\@LineSpacing}

%% Final text printing area, per Geoff Sutcliffe

\RequirePackage{keyval}

\define@key{Ec}{lmargin}{\Ec@defbylen{lmargin}{#1}}

\newlength{\@MarginSize}
\setlength{\@MarginSize}{1in}

\setlength{\@LMarginSize}{\@MarginSize}
%\setlength{\@LMarginSize}{\Ec@lmargin}
\setlength{\@RMarginSize}{\@MarginSize}
\setlength{\@TMarginSize}{\@MarginSize}
\setlength{\@BMarginSize}{\@MarginSize}


% Head height is dependent on the font point size
\setlength{\headheight}{\@HeadHeightSize}
\setlength{\headsep}{\@HeadSepSize}
\setlength{\footskip}{\@FootSkipSize}

\ifletterpaper
	\immediate\write10{easychair: Selecting letter paper margin sizes.}
 	\RequirePackage[%
                papersize={8.5in,11in},
                total={145mm,224mm},
                centering,
                twoside,
		includeheadfoot]{geometry}
\fi
\ifafourpaper
	\immediate\write10{easychair: Selecting A4 paper margin sizes.}
 	\RequirePackage[%
                papersize={210mm,297mm},
                total={145mm,224mm},
                centering,
                twoside,
		includeheadfoot]{geometry}
\fi

\ifcustompaper
	\immediate\write10{easychair: Selecting custom paper margin sizes.}
	\RequirePackage[%
                papersize={189mm,246mm},
                total={145mm,224mm},
                top=9mm,
                left=24mm,
                twoside,
		includeheadfoot]{geometry}
        \headHeightSize{12.0pt}
        \headSepSize{16.0pt}
        \footSkipSize{26pt}
\fi

%\setlength{\textwidth}{16cm}
%\setlength{\textheight}{9in}


%
% Volume
%

\RequirePackage{lastpage}

\newif\ifvolumeundefined
\volumeundefinedtrue

% e.g.
% \volumeinfo
%		{J. Bloe}   % editor(s)      #1
%		{1}         % No. of editors #2
%		{LICS 2008} % event title    #3
%		{1}         % volume number  #4
%		{4}         % issue          #5
%		{134}       % start page     #6

\def\@EasyFontStyle{\footnotesize}
\newcommand{\headfootstyle}[1]{\def\@EasyFontStyle{#1}}

\def\@EasyVolumeInfo{}

\ifthesis
	\newcommand{\volumeinfo}[6]
		{\PackageWarning{easychair}{Cannot use volumeinfo with 'thesis' option. Ignoring...}}
\else
	\newcommand{\volumeinfo}[6]{%
		\ifvolumeundefined
	%		\def\@makefntext##1{\noindent ##1}%
			\def\@EasyEdsNames{#1}%
			\def\@EasyEds{ed.}%
			\def\@EasyEvent{#3}%
			\def\@EasyVolume{}%
			\def\@EasyIssue{}%
			\def\@EasyFirstPage{#6}%
			\ifnum #2>1 \gdef\@EasyEds{eds.}\fi%
			\ifnum #4>0 \gdef\@EasyVolume{; Volume #4}\fi%
			\ifnum #5>0 \gdef\@EasyIssue{, issue: #5} \fi%
	%		\footnotetext[0]{\sf \@EasyEdsNames (\@EasyEds); \@EasyEvent\@EasyVolume\@EasyIssue, pp. #6-\pageref*{LastPage}}%
	%		\def\@EasyVolumeInfo{\footnotesize{\sf\@EasyEdsNames~(\@EasyEds); \@EasyEvent\@EasyVolume\@EasyIssue, pp. \@EasyFirstPage--\pageref*{LastPage}}}%
			\def\@EasyVolumeInfo{\@EasyFontStyle\@EasyEdsNames~(\@EasyEds); \@EasyEvent\@EasyVolume\@EasyIssue, pp. \@EasyFirstPage--\pageref*{LastPage}}%
			%\def\@makefntext##1{\noindent\@makefnmark##1}%
			\setcounter{page}{\@EasyFirstPage}
			\volumeundefinedfalse
		\else
			{\PackageWarning{easychair}{May not redefine volumeinfo}}
		\fi
	}
\fi

\def\@EventInfo{}
\def\@VolumeInfo{}

%
% Allow for more space to place floats.
%

\renewcommand{\topfraction}{0.95}
\renewcommand{\bottomfraction}{0.95}
\renewcommand{\textfraction}{0.05}
\renewcommand{\floatpagefraction}{0.8}


%
% Running heads and ``foots''
%

\RequirePackage{fancyhdr}
\pagestyle{fancy}

\fancyhead{}
%\ifdebug
%	\iftwosided
%		\fancyhead[RE]{\overline{\@titleRunning}}
%		\fancyhead[RO]{\overline{\@authorRunning}}
%	\else
%		\fancyhead[LO,LE]{\begin{math}\overline{\mbox{\@titleRunning}}\end{math}}
%		\fancyhead[RO,RE]{\begin{math}\overline{\mbox{\@authorRunning}}\end{math}}
%	\fi
%\else
	\iftwosided
		\fancyhead[RE]{{\@EasyFontStyle\@titleRunning}}
		\fancyhead[RO]{{\@EasyFontStyle\@authorRunning}}
	\else
		\fancyhead[LO,LE]{{\@EasyFontStyle\@titleRunning}}
		\fancyhead[RO,RE]{{\@EasyFontStyle\@authorRunning}}
	\fi
%\fi

\fancyfoot{}
\ifodd\c@page
	\fancyfoot[LO]{{\@EasyFontStyle\@VolumeInfo}}
	\fancyfoot[RE]{{\@EasyFontStyle\@EventInfo}}
\else
	\fancyfoot[RE]{{\@EasyFontStyle\@VolumeInfo}}
	\fancyfoot[LO]{{\@EasyFontStyle\@EventInfo}}
\fi
\ifodd\c@page
	\fancyfoot[RO]{{\normalsize\thepage}}
	\fancyfoot[LE]{{\normalsize\thepage}}
\else
	\fancyfoot[LE]{{\normalsize\thepage}}
	\fancyfoot[RO]{{\normalsize\thepage}}
\fi
	\renewcommand{\headrulewidth}{0pt}
	\renewcommand{\footrulewidth}{0pt}
%\fi

% Suppress the default date, per Geoff
\date{}

% For the first page
\fancypagestyle{plain}{%
\fancyhf{} % clear all header and footer fields
\ifodd\c@page
	\fancyfoot[L]{\@EasyVolumeInfo{}}%
	\fancyfoot[R]{}
\else
	\fancyfoot[R]{\@EasyVolumeInfo}%
	\fancyfoot[L]{}
\fi
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}}

\def\@maketitle{%
  %% Code added to use llncs style author list
\def\andname{and}
\def\lastandname{\unskip, and}
  \def\lastand{\ifnum\value{@inst}=2\relax
                 \unskip{} \andname\
                 \else
                 \unskip \lastandname\
            \fi}%
 \def\and{\stepcounter{@auth}\relax
          \ifnum\value{@auth}=\value{@inst}%
             \lastand
          \else
             \unskip,
             \fi}%
   %%
  \newpage
	\null
  % Facelift a bit the title and make it bold, per Geoff
	\vspace{-1cm}
	\begin{center}%
		\let\footnote\thanks%
		\ifwithtimes
			{\LARGE{\@title}\par}
		\else
			{\LARGE\@title\par}
                 \fi
                 \vskip \baselineskip
                 \@date
                 {\large
               \setbox0=\vbox{\setcounter{@auth}{1}\def\and{\stepcounter{@auth}}%
               \def\thanks##1{}\@author}%
               \global\value{@inst}=\value{@auth}%
               \global\value{auco}=\value{@auth}%
               \setcounter{@auth}{1}%
               {\lineskip .5em
               \noindent\ignorespaces
               \@author\vskip.35cm}}
               {\small\institutename}
	\end{center}%
}

\ifEPiCfinal
\definecolor{volume}{RGB}{0,112,144}
\def\EPiCSeries{EPiC Series in Computer Science}
\def\EPiCVolume{XXX}
\def\EPiCYear{2017}
\def\EPiCPages{Pages 19--27}
\def\EPiCConference{99th International Conference on Topics of Superb Significance (CATSS)}
\def\ChairLogo{logo_chair.png}
\def\EPiCLogo{logo_epic.png}
\fi

% ------------------------------------------------
% Change the maketitle command in EPiC
\let\oldmaketitle=\@maketitle
% ------------------------------------------------
\def\@maketitle{%
\ifEPiCfinal

%\vspace*{-10mm}\par
\definecolor{headerframe}{rgb}{0.473,0.676,0.656} % 79ada8
\definecolor{headerback}{rgb}{0.953125,0.95703125,0.9609375} % f4f5f6

\begin{tcolorbox}[
  enhanced,center,width=\linewidth-2cm,
  underlay={
    \node[inner sep=0pt,outer sep=0pt,right] at ([xshift=-1cm]frame.west)
      {\includegraphics[height=74.5pt]{\ChairLogo}};
    \node[inner sep=0pt,outer sep=0pt,left] at ([xshift=1cm]frame.east)
      {\includegraphics[height=73pt]{\EPiCLogo}};
  },
  before skip=0pt,% <--- before box
  after skip=6pt,%  <--- after box
  left=71.54pt-1cm+4mm,
  right=56.22423pt-1cm+4mm,
  sharp corners,text fill,
  colback=headerback,colframe=headerframe,
  height=73pt,toprule=0.5pt,bottomrule=0.5pt,leftrule=0pt,rightrule=0pt,
  halign=center,valign=center,boxsep=0pt,
  top=2mm,%     space to top border
  bottom=2mm,%  space to bottom border
  ]%
{\Large \EPiCSeries}\par\vfill%
{\color{volume}Volume \EPiCVolume, \EPiCYear, \EPiCPages}\par\vfill%
\EPiCConference
\end{tcolorbox}

\par\ \vspace*{12pt}\par
{\let\newpage\relax\oldmaketitle}%
\else \ifEPiC
\definecolor{grayheader}{RGB}{112,112,112}%
{\color{grayheader}\vspace*{-23pt}\noindent \hrulefill\\
\noindent\centering
\raisebox{0pt}[36.5pt][36.5pt]{This space is reserved for the EPiC Series header, do not use it}%

\noindent\hrulefill}%
\\

{\let\newpage\relax\oldmaketitle}%
\else \ifEPiCempty
\raisebox{0pt}[47pt][47pt]{~}
\\

{\let\newpage\relax\oldmaketitle}%

% otherwise the old maketitle

\else
\oldmaketitle
\fi\fi\fi
}
% ------------------------------------------------

% Tighten up bibliography
\let\oldthebibliography=\thebibliography
\let\endoldthebibliography=\endthebibliography
\renewenvironment{thebibliography}[1]
{
	\small
	\begin{oldthebibliography}{#1}
		\setlength{\parskip}{2pt}
		\setlength{\itemsep}{0pt}
}
{
	\end{oldthebibliography}
}

\ifdebug
	\ifverbose
		\RequirePackage[colorgrid,pscoord]{eso-pic}%
	\else
		\RequirePackage[pscoord]{eso-pic}
		\newcommand\ShowFramePicture{%
		  \begingroup
		    \color{red}
		    \AtTextLowerLeft{\framebox(\LenToUnit{\textwidth},\LenToUnit{\textheight}){}}%
		    \AtTextUpperLeft{\put(0,\LenToUnit{\headsep}){\framebox(\LenToUnit{\textwidth},\LenToUnit{\headheight}){}}}%
		    \AtTextLowerLeft{\put(0,\LenToUnit{-\footskip}){\framebox(\LenToUnit{\textwidth},\LenToUnit{\headheight}){}}}%
		  \endgroup
		}
		\AddToShipoutPicture{\ShowFramePicture}
	\fi
	%\RequirePackage[a4,cam,center]{crop}%
	%\RequirePackage[cam,center]{crop}%
\fi

\ifframe
	\ifverbose
		\RequirePackage[colorgrid,pscoord]{eso-pic}%
	\else
		\RequirePackage[pscoord]{eso-pic}
		\newcommand\ShowBlueFrame{%
		  \begingroup
		    \color{blue}
                    % odd page
%		    \AtTextLowerLeft{\put(\LenToUnit{-23.6mm},\LenToUnit{-21.8mm}){\framebox(\LenToUnit{188.3mm},\LenToUnit{245.4mm}){}}}%
                    % even page
%		    \AtTextLowerLeft{\put(\LenToUnit{-19.6mm},\LenToUnit{-21.8mm}){\framebox(\LenToUnit{188.3mm},\LenToUnit{245.4mm}){}}}%
		  \endgroup
		}
		\AddToShipoutPicture{\ShowBlueFrame}
	\fi
\fi

% \geometry{papersize={170mm,240mm},total={124mm,185mm}}

%% Indexing options for proceedings to link up people's names to their
%% various participation and affiliation options.

\newcommand
	{\indexedperson}
	[3]
	{\index{#2!#1}\index{#1}\index{#1!#3}}

\newcommand
	{\indexedauthor}
	[1]
	{\indexedperson{#1}{Authors}{Author}}

\newcommand
	{\indexededitor}
	[1]
	{\indexedperson{#1}{Editors}{Editor}}

\newcommand
	{\indexedpcmember}
	[1]
	{\indexedperson{#1}{PC Members}{PC Member}}

\newcommand
	{\indexedreviewer}
	[1]
	{\indexedperson{#1}{Reviewers}{Reviewer}}

\newcommand
	{\indexedorganizer}
	[1]
	{\indexedperson{#1}{Organizers}{Organizer}}

\newcommand
	{\indexedwebmaster}
	[1]
	{\indexedperson{#1}{Webmasters}{Webmaster}}

\newcommand
	{\indexedaffiliation}
	[2]
	{\indexedperson{#1}{#2}{#2}}

\newcommand
	{\indexedsupervisor}
	[2]
	{\indexedperson{#1}{}{Supervisor: #2}\indexedperson{#2}{Supervisors}{Supervisor}}

\endinput

% \crop[font=\upshape\mdseries\small\textsf]

% EOF
