%     Continuity of Gödel's system T definable functionals
%     via effectful forcing
%
%     Martin Escardo
%
%     24-31 July 2012, updated 3 August 2012, 21 and 28 Feb 2013 and 6 Mar 2013.
%
%     This file proof-checks in Agda version 2.3.2.
%
%     (NB. With earlier versions of Agda this file has unsolved metas
%      arising from the definition B = D ℕ ℕ.)
%
% This is a literate Agda file that generates latex, pdf and html.
% Search for "code" to find the agda code.
%
% This is best viewed as http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.pdf
% in the form of an article.
%
% The source file is http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.lagda
% You are probably browsing http://www.cs.bham.ac.uk/~mhe/dialogue/dialogue.html

\documentclass{entcs} \usepackage{prentcsmacro}
\usepackage{graphicx}
\sloppy
% The following is enclosed to allow easy detection of differences in
% ascii coding.
% Upper-case    A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
% Lower-case    a b c d e f g h i j k l m n o p q r s t u v w x y z
% Digits        0 1 2 3 4 5 6 7 8 9
% Exclamation   !           Double quote "          Hash (number) #
% Dollar        $           Percent      %          Ampersand     &
% Acute accent  '           Left paren   (          Right paren   )
% Asterisk      *           Plus         +          Comma         ,
% Minus         -           Point        .          Solidus       /
% Colon         :           Semicolon    ;          Less than     <
% Equals        =           Greater than >          Question mark ?
% At            @           Left bracket [          Backslash     \
% Right bracket ]           Circumflex   ^          Underscore    _
% Grave accent  `           Left brace   {          Vertical bar  |
% Right brace   }           Tilde        ~


% ----------------------------------------------------------------------
% Some useful commands when doing highlightning of Agda code in LaTeX.
% ----------------------------------------------------------------------
%

% This is actually agda.sty provided by the agda distribution,
% suitably modified an extended for our purposes, and included here to
% avoid hassle for the editors of the MFPS proceedings.

\newcommand{\AgdaC}[1]{\mbox{#1}}

\usepackage{ifxetex, xcolor, polytable}

% XeLaTeX
\ifxetex
    \usepackage{polyglossia}
    \usepackage{fontspec}
    \usepackage[]{unicode-math}

% pdfLaTeX
\else
    \usepackage{bbm, ucs, amsfonts, amssymb, stmaryrd} % mhe
    \usepackage[safe]{tipa} % See page 12 of the tipa manual for what
                            % safe does.

    % FIX: This doesn't seem to help solve the pipe problem?
    % http://tex.stackexchange.com/questions/1774/how-to-insert-pipe-symbol-in-latex
    \usepackage[T1]{fontenc}
    \usepackage[utf8x]{inputenc}

    % FIX: Complete the list and send it upstream to the ucs package devs.
    \DeclareUnicodeCharacter{951}{$\eta$} % mhe
    \DeclareUnicodeCharacter{937}{$\Omega$} % mhe
    \DeclareUnicodeCharacter{931}{$\Sigma$} % mhe
    \DeclareUnicodeCharacter{928}{$\Pi$} % mhe
    \DeclareUnicodeCharacter{945}{$\alpha$} % mhe
    \DeclareUnicodeCharacter{960}{$\pi$} % mhe
    \DeclareUnicodeCharacter{963}{$\sigma$} % mhe
    \DeclareUnicodeCharacter{964}{$\tau$} % mhe
    \DeclareUnicodeCharacter{961}{$\rho$} % mhe
    \DeclareUnicodeCharacter{10214}{$\llbracket$} % mhe (stmaryrd)
    \DeclareUnicodeCharacter{10215}{$\rrbracket$} % mhe (stmaryrd)
    \DeclareUnicodeCharacter{9657}{$\triangleright$}
    \DeclareUnicodeCharacter{8759}{::}
    \DeclareUnicodeCharacter{8263}{$?\!?$}
    \DeclareUnicodeCharacter{737} {$^l$}  % FIX: Ugly, apparently ^r is
                                          % defined, I can't find the
                                          % definition though.
    \DeclareUnicodeCharacter{8718}{$\blacksquare$}
    \DeclareUnicodeCharacter{8255}{$\_$} % FIX: Couldn't find \undertie.
    \DeclareUnicodeCharacter{9667}{$\triangleleft$}
    \DeclareUnicodeCharacter{10218}{$\langle\!\langle$}
    \DeclareUnicodeCharacter{10219}{$\rangle\!\rangle$}
\fi

% ----------------------------------------------------------------------
% Font styles.

% Default font style.
\newcommand{\AgdaFontStyle}[1]{\textsf{#1}}

% String font style.
\newcommand{\AgdaStringFontStyle}[1]{\texttt{#1}}

% Comment font style.
\newcommand{\AgdaCommentFontStyle}[1]{\texttt{#1}}

% Bounded variables font style.
\newcommand{\AgdaBoundFontStyle}[1]{\textit{#1}}

% ----------------------------------------------------------------------
% Colours.

% Aspect colours.
\definecolor{AgdaComment}      {HTML}{B22222}
\definecolor{AgdaKeyword}      {HTML}{CD6600}
\definecolor{AgdaString}       {HTML}{B22222}
\definecolor{AgdaNumber}       {HTML}{A020F0}
\definecolor{AgdaSymbol}       {HTML}{181818} % was {404040} % mhe
\definecolor{AgdaPrimitiveType}{HTML}{0000CD}
\definecolor{AgdaOperator}     {HTML}{000000}

% NameKind colours.
\definecolor{AgdaBound}                 {HTML}{000000}
\definecolor{AgdaInductiveConstructor}  {HTML}{008B00}
\definecolor{AgdaCoinductiveConstructor}{HTML}{8B7500}
\definecolor{AgdaDatatype}              {HTML}{0000CD}
\definecolor{AgdaField}                 {HTML}{EE1289}
\definecolor{AgdaFunction}              {HTML}{0000CD}
\definecolor{AgdaModule}                {HTML}{A020F0}
\definecolor{AgdaPostulate}             {HTML}{0000CD}
\definecolor{AgdaPrimitive}             {HTML}{0000CD}
\definecolor{AgdaRecord}                {HTML}{0000CD}

% Other aspect colours.
\definecolor{AgdaDottedPattern}     {HTML}{000000}
\definecolor{AgdaUnsolvedMeta}      {HTML}{FFFF00}
\definecolor{AgdaTerminationProblem}{HTML}{FFA07A}
\definecolor{AgdaIncompletePattern} {HTML}{F5DEB3}
\definecolor{AgdaError}             {HTML}{FF0000}

% Misc.
\definecolor{AgdaHole}              {HTML}{9DFF9D}

% ----------------------------------------------------------------------
% Commands.

% Aspect commands.
\newcommand{\AgdaComment}     [1]
    {\AgdaCommentFontStyle{\textcolor{AgdaComment}{#1}}}
\newcommand{\AgdaKeyword}     [1]
    {\AgdaFontStyle{\textcolor{AgdaKeyword}{#1}}}
\newcommand{\AgdaString}      [1]{\AgdaStringFontStyle{\textcolor{AgdaString}{#1}}}
\newcommand{\AgdaNumber}      [1]{\textcolor{AgdaNumber}{#1}}
\newcommand{\AgdaSymbol}      [1]{\textcolor{AgdaSymbol}{#1}}
\newcommand{\AgdaPrimitiveType}[1]
    {\AgdaFontStyle{\textcolor{AgdaPrimitiveType}{#1}}}
\newcommand{\AgdaOperator}    [1]{\textcolor{AgdaOperator}{#1}}

% NameKind commands.
\newcommand{\AgdaBound}    [1]{\AgdaBoundFontStyle{\textcolor{AgdaBound}{#1}}}
\newcommand{\AgdaInductiveConstructor}[1]
    {\AgdaFontStyle{\textcolor{AgdaInductiveConstructor}{#1}}}
\newcommand{\AgdaCoinductiveConstructor}[1]
    {\AgdaFontStyle{\textcolor{AgdaCoinductiveConstructor}{#1}}}
\newcommand{\AgdaDatatype} [1]{\AgdaFontStyle{\textcolor{AgdaDatatype}{#1}}}
\newcommand{\AgdaField}    [1]{\AgdaFontStyle{\textcolor{AgdaField}{#1}}}
\newcommand{\AgdaFunction} [1]{\AgdaFontStyle{\textcolor{AgdaFunction}{#1}}}
\newcommand{\AgdaModule}   [1]{\AgdaFontStyle{\textcolor{AgdaModule}{#1}}}
\newcommand{\AgdaPostulate}[1]{\AgdaFontStyle{\textcolor{AgdaPostulate}{#1}}}
\newcommand{\AgdaPrimitive}[1]{\AgdaFontStyle{\textcolor{AgdaPrimitive}{#1}}}
\newcommand{\AgdaRecord}   [1]{\AgdaFontStyle{\textcolor{AgdaRecord}{#1}}}

% Other aspect commands.
\newcommand{\AgdaDottedPattern}     [1]{\textcolor{AgdaDottedPattern}{#1}}
\newcommand{\AgdaUnsolvedMeta}      [1]
    {\AgdaFontStyle{\colorbox{AgdaUnsolvedMeta}{#1}}}
\newcommand{\AgdaTerminationProblem}[1]
    {\AgdaFontStyle{\colorbox{AgdaTerminationProblem}{#1}}}
\newcommand{\AgdaIncompletePattern} [1]{\colorbox{AgdaIncompletePattern}{#1}}
\newcommand{\AgdaError}             [1]
    {\AgdaFontStyle{\textcolor{AgdaError}{\underline{#1}}}}

% Misc.
\newcommand{\AgdaHole}[1]{\colorbox{AgdaHole}{#1}}
\long\def\AgdaHide#1{} % Used to hide code from LaTeX.

\newcommand{\AgdaIndent}[1]{\quad}

% ----------------------------------------------------------------------
% The code environment.

% \newcommand{\AgdaCodeStyle}{}
\newcommand{\AgdaCodeStyle}{\small}

\ifdefined\mathindent
  {}
\else
  \newdimen\mathindent\mathindent\leftmargini
\fi

\newenvironment{code}% modified by mhe
{\noindent\AgdaCodeStyle\pboxed}%
{\endpboxed\par\noindent%
\ignorespacesafterend}

% Default column for polytable.
\defaultcolumn{l}
% End of Agda.sty.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\usepackage{amsmath}
\usepackage{url}
\usepackage[english]{babel}
\usepackage{diagrams}

\def\lastname{Escardo} % should be Escard\'o but this generates "Escard" in the pdf (entcs style's fault).
\begin{document}
\begin{frontmatter}
  \title{Continuity of G\"odel's system T definable functionals via effectful forcing}
  \author{Mart\'\i{n} Escard\'o\thanksref{myemail}}
  \address{School of Computer Science\\ University of Birmingham \\
    Birmingham, England} \thanks[myemail]{Email: \href{mailto:m.escardo@cs.bham.ac.uk} {\texttt{\normalshape m.escardo@cs.bham.ac.uk}}}

\begin{abstract}

   It is well-known that the Gödel's system T definable functions
   \AgdaC{(ℕ → ℕ) → ℕ} are continuous, and that their restrictions
   from the Baire type \AgdaC{(ℕ → ℕ)} to the Cantor type \AgdaC{(ℕ →
   2)} are uniformly continuous. We offer a new, relatively short and
   self-contained proof. The main technical idea is a concrete notion
   of generic element that doesn't rely on forcing, Kripke semantics
   or sheaves, which seems to be related to generic effects in
   programming.  The proof uses standard techniques from programming
   language semantics, such as dialogues, monads, and logical
   relations. We write this proof in intensional Martin-Löf type
   theory (MLTT) from scratch, in Agda notation. Because MLTT has a
   computational interpretation and Agda can be seen as a programming
   language, we can run our proof to compute moduli of (uniform)
   continuity of T-definable functions.

\end{abstract}
\begin{keyword}
   Gödel's system T, continuity, uniform continuity, Baire space,
   Cantor space, intensional Martin-Löf theory, Agda, dialogue,
   semantics, logical relation.
\end{keyword}
\end{frontmatter}

\section{Introduction} \label{formulation}

This is a relatively short, and self-contained, proof of the
well-known fact that any function \AgdaC{$f$ : (ℕ → ℕ) → ℕ} that is
definable in Gödel's system T is continuous, and that its restriction
from the Baire type \AgdaC{(ℕ → ℕ)} to the Cantor type \AgdaC{(ℕ → 2)}
is uniformly continuous~\cite{MR0325352,beeson}. We believe the proof
is new, although it is related to previous work discussed below.  The
main technical idea is a concrete notion of generic element that
doesn't rely on forcing, Kripke semantics or sheaves, which seems to
be related to generic effects in
programming~\cite{Plotkin03algebraicoperations}.  Several well-known
ideas from logic, computation, constructive mathematics and
programming-language semantics naturally appear here, in a relatively
simple, self-contained, and hopefully appealing, development.

The idea is to represent a function \AgdaC{$f$ : (ℕ → ℕ) → ℕ} by a
well-founded dialogue tree, and extract continuity information about
$f$ from this tree. To calculate such a tree from a system T term
\AgdaC{$t$: (ι ⇒ ι) ⇒ ι} denoting $f$, we work with an auxiliary
interpretation of system T, which gives a function \AgdaC{$\tilde{f}$
: $(\tilde{\mathbb{N}}$ → $\tilde{\mathbb{N}})$ →
$\tilde{\mathbb{N}}$}, where $\tilde{\mathbb{N}}$ is the set of
dialogue trees. Applying $\tilde{f}$ to a certain \emph{generic
sequence} $\tilde{\mathbb{N}}$ → $\tilde{\mathbb{N}}$, the desired
dialogue tree is obtained. We now explain this idea in more detail.

In the set-theoretical model of system T, the ground type ι is
interpreted as the set ℕ of natural numbers, and if the types σ and τ
are interpreted as sets~$X$ and $Y$, then the type σ ⇒ τ is
interpreted as the set of all functions \AgdaC{$X$ → $Y$}. We consider
an auxiliary model that replaces the interpretation of the ground
type by the set $\tilde{\mathbb{N}}$, but keeps the interpretation of
⇒ as the formation of the set of all functions. In this
model, the zero constant is interpreted by a suitable element
$\tilde{0}$ of $\tilde{\mathbb{N}}$, the successor constant is
interpreted by a function $\tilde{\mathbb{N}}$ → $\tilde{\mathbb{N}}$,
and each iteration combinator is interpreted by a function
($X$ → $X$) → $X$ → $\tilde{\mathbb{N}}$ → $X$. An element of the set
$\tilde{\mathbb{N}}$ is a well-founded dialogue tree that describes
the computation of a natural number relative to an unspecified oracle
\AgdaC{α : ℕ → ℕ}. An internal node is labeled by a natural number
representing a query to the oracle, and has countably many branches
corresponding to the possible answers. Each leaf is labeled by a
natural number and represents a possible outcome of the computation.
These dialogues represent computations in the sense of
Kleene~\cite{KleeneSC:rfqftI}.

If a particular oracle \AgdaC{α : ℕ → ℕ} is given, we get a natural
number from any \AgdaC{$d \in \tilde{\mathbb{N}}$} via a
decodification function
\begin{quote}
  decode : (ℕ → ℕ) → $\tilde{\mathbb{N}}$ → ℕ.
\end{quote}
It turns out that there is a function
\begin{quote}
  generic : $\tilde{\mathbb{N}}$ → $\tilde{\mathbb{N}}$
\end{quote}
that can be regarded as a \emph{generic sequence} in the sense that,
for any particular sequence \AgdaC{α : ℕ → ℕ},

\begin{small}
\begin{diagram}[small]
\tilde{\mathbb{N}} & \rTo^{\text{generic}} & \tilde{\mathbb{N}} \\
\dTo^{\text{decode α}} & & \dTo_{\text{decode α}} \\
\text{ℕ} & \rTo_{\text{α}} & \text{ℕ}.
\end{diagram}
\end{small}

\noindent That is, the generic sequence codes any concrete sequence
\AgdaC{α}, provided the sequence α itself is used as the concrete
oracle for decodification. The idea is that the application of the
function \AgdaC{generic} to a dialogue tree adds a new layer of
choices at its leaves.

Next we show that for any given term \AgdaC{$t$ : (ι ⇒ ι) ⇒ ι} denoting a
function \AgdaC{$f$ : (ℕ → ℕ) → ℕ} in the standard interpretation and
\AgdaC{$\tilde{f}$ : $(\tilde{\mathbb{N}}$ → $\tilde{\mathbb{N}})$ →
$\tilde{\mathbb{N}}$} in the dialogue interpretation, we have that
\begin{quote} \AgdaC{$f$ α = decode α ($\tilde{f}$ generic).}  \end{quote}
This is proved by establishing a logical
relation between the set-theoretic and dialogue models.
Thus we can compute a dialogue tree of $f$ by applying $\tilde{f}$ to
the generic sequence.

The set $\tilde{\mathbb{N}}$ is constructed as \AgdaC{B ℕ} for a
suitable dialogue monad B. Then the interpretation of the constant
zero is η 0 where η is the unit of the monad, the interpretation of
the successor constant is given by functoriality as \AgdaC{B succ},
and the interpretation of the primitive recursion constant is given by
the Kleisli extension of its standard interpretation. The object part
\AgdaC{B $X$} of the monad is inductively defined by the constructors
\begin{quote} η : $X$ → B $X$, \\ β : (ℕ → B $X$) → ℕ → B $X$,
\end{quote} where η constructs leaves and β constructs a tree β φ $n$
given countably many trees φ and a label~$n$. With $X$ = ℕ, we have β
η : ℕ → B ℕ, and the generic sequence is the Kleisli extension of β η.
Thus, the generic sequence seems to be a sort of \emph{generic effect}
in the sense of~\cite{Plotkin03algebraicoperations}. Notice that our
interpretation is a call-by-name version of Moggi's
semantics.

Using this, it follows that if a function \AgdaC{$f$ : (ℕ → ℕ) → ℕ} is
the set-theoretical interpretation of some system T term \AgdaC{$t$ :
(ι ⇒ ι) ⇒ ι}, then it is continuous and its restriction to \AgdaC{ℕ →
2} is uniformly continuous, where $2$ is the set with elements $0$ and
$1$. The reason is that a dialogue produces an answer after finitely
many queries, because it is well-founded, and that a dialogue tree for
a function \AgdaC{$(ℕ → 2) → ℕ$} is finite, because it is finitely
branching. Recall that continuity means that, for any sequence of
integers \AgdaC{α : ℕ → ℕ}, there is \AgdaC{$m$ : ℕ}, called a modulus
of continuity of $f$ at the point~α, such that any sequence
\AgdaC{α$'$} that agrees with α at the first $m$ positions gives the
same result, that is, \AgdaC{$f$ α = $f$ α$'$}.  Uniform continuity
means that there is \AgdaC{$m$ : ℕ}, called a modulus of uniform
continuity of $f$ on \AgdaC{ℕ → 2}, such that any two binary sequences
α and α$'$ that agree at the first $m$ positions give the same result.


Our arguments are constructive, and we write the full proof from
scratch in intensional Martin-Löf type theory (MLTT), in Agda
notation~\cite{bove:dybjer}, without the use of libraries.  We don't
assume previous familiarity with Agda, but we do require rudimentary
knowledge of MLTT.  The Agda source file for this
program/proof~\cite{escardo:dialogue} is written in Knuth's
\emph{literate} style, which automatically generates the \LaTeX\ file
that produces this article. Agda both checks proofs and can run them.
Notice that MLTT or Agda cannot prove or disprove that all functions
\AgdaC{(ℕ → ℕ) → ℕ} are continuous, as they are compatible with both
classical and constructive mathematics, like Bishop
mathematics~\cite{bishop:foundations}. The theorem here is that
certain functions \AgdaC{(ℕ → ℕ) → ℕ} are continuous: those that can
be defined in system~T.

\noindent{\itshape\bfseries Related work.}
The idea of computing continuity information by applying a function
to effectful arguments goes back to Longley~\cite{Longley99whenis},
who passes exceptions to the function. A similar approach is
described in an example given by Bauer and Pretnar~\cite{bauer:pretnar}.

The idea of working with computation trees is of course very old,
going back to Brouwer~\cite{beeson} in intuitionistic mathematics, and
to Kleene~\cite{KleeneSC:rfqftI} in computability theory in the form
of dialogues, where the input is referred to as an
oracle. Howard~\cite{Howard(80)} derives computation trees for system
T, by operational methods, by successively reducing a term so that
each time an oracle given by a free variable of type ι ⇒ ι is
queried, countably many branches of the computation are created,
corresponding to the possible answers given by the oracle.
Hancock and Setzer use variations of dialogue trees to describe
interactive computation in type
theory~\cite{DBLP:conf/csl/HancockS00} (see also~\cite{Hancock_representationsof}).

Our work is directly inspired by Coquand and Jaber's work on forcing
in type
theory~\cite{Coquand:2010:NFT:1839560.1839564,DBLP:series/leus/CoquandJ12}. Like
Howard, they derive computation trees by operational methods. They
extend dependent type theory with a constant for a generic element,
and then decorate judgements with subscripts that keep track of
approximation information about the generic element as the
computations proceed (similarly to \cite{MR0325352}).
In this way they extract continuity information.
They prove the termination and soundness of this
modification of type theory using Tait's computability method, which
here is manifested as a logical relation between our two models. They
also provide a Haskell implementation for the system~T case as an
appendix, which uses a monad that is the composition of the list monad
(for nondeterminism) and of the state monad. Their Haskell program
implements a normalization procedure with bookkeeping information,
tracked by the monad, that produces computation trees. Because they
only account for uniform continuity in their Haskell implementation,
such trees are finite. They describe their work as a computational
interpretation of forcing and continuity as presented in
Beeson~\cite{beeson}.
The difference is that
their approach is syntactical whereas ours is semantical,
and the reader may sense an analogy with normalization by
evaluation. Notice that these arguments only show that the
\emph{definable} functions are continuous. To get a constructive model
in which \emph{all} functions are continuous, they work with iterated
forcing, which is related to our recent work~\cite{escardo:xu}, but
this is another story.

\noindent {\itshape\bfseries Organization.}
(\ref{section:formal})~Formal proof in Agda.
(\ref{section:informal})~Informal, rigorous proof.

\noindent {\itshape\bfseries Acknowledgements.}  I benefitted from remarks on a
previous version of this paper by Thierry Coquand, Dan Ghica, Achim Jung,
Chuangjie~Xu, and the anonymous referees.

\section{Proof in Martin-L\"of type theory in Agda notation}
\label{section:formal}

\subsection{Agda preliminaries} \label{section:preliminaries}

The purpose of this subsection is two-fold: (1) To develop a tiny Agda
library for use in the following sections, and (2) to briefly explain
Agda notation~\cite{bove:dybjer} for MLTT. We assume rudimentary
knowledge of (intensional) Martin-L\"of type theory and the BHK
interpretation of the quantifiers as products Π and sums~Σ. We don't
use any feature of Agda that goes beyond standard MLTT. If we were
trying to be purist, we would use W-types rather than some of our
inductive definitions using the Agda keyword \emph{data}. Notice that
the coloured text in the electronic version of this paper is the Agda
code.

The universe of all types is denoted by Set, and types are called
sets (this is a universe \`a la Russell).  Products \AgdaC{Π} are
denoted by \AgdaC{∀} in Agda.
% Any Agda file, has to be a named module:
\AgdaHide{ % I don't think I am hiding anything else.
\begin{code}
module dialogue where
\end{code}
}
Consider the definition of the (interpretation of) the standard
combinators:

\begin{code}
Ķ : ∀{X Y : Set} → X → Y → X
Ķ x y = x
Ş : ∀{X Y Z : Set} → (X → Y → Z) → (X → Y) → X → Z
Ş f g x = f x (g x)
\end{code}
  The curly braces around the set variables indicate that these are
implicit parameters, to be inferred by Agda whenever \AgdaC{Ķ} and \AgdaC{Ş} are
used. If Agda fails to uniquely infer the missing arguments, one has
to write e.g.\ \AgdaC{$Ķ$ \{$X$\} \{$Y$\} $x$ $y$} rather than the
abbreviated form \AgdaC{$Ķ$ $x$ $y$}. The following should be
self-explanatory:

\begin{code}
_∘_ : ∀{X Y Z : Set} → (Y → Z) → (X → Y) → (X → Z)
g ∘ f = λ x → g(f x)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
rec : ∀{X : Set} → (X → X) → X → ℕ → X
rec f x  zero    = x
rec f x (succ n) = f(rec f x n)
\end{code}
Agda has a termination checker that verifies that recursions are
well-founded, and hence all functions are total. We also need types of
binary digits, finite lists, and finite binary trees:

\begin{code}
data ℕ₂ : Set where
  ₀ ₁ : ℕ₂

data List (X : Set) : Set where
  []        : List X
  _∷_ : X → List X → List X

data Tree (X : Set) : Set where
  empty : Tree X
  branch : X → (ℕ₂ → Tree X) → Tree X
\end{code}
Sums are not built-in and hence need to be defined:

\begin{code}
data Σ {X : Set} (Y : X → Set) : Set where
  _,_ : ∀(x : X)(y : Y x) → Σ {X} Y
\end{code}
The definition says that an element of \AgdaC{Σ \{$X$\} $Y$} is a pair
\AgdaC{($x$,$y$)} with \AgdaC{$x$ : $X$} and \AgdaC{$y$ : $Y$ $x$}.
Notice that comma is not a reserved symbol: we define it as a binary
operator to construct dependent pairs.  Because \AgdaC{$Y$ = λ($x$ : $X$) →
$Y$ $x$} if one assumes the η-law, and because the first argument is
implicit, we can write \AgdaC{Σ $\{X\}$ $Y$} as \AgdaC{Σ Y} or \AgdaC{Σ
\char`\\($x$ : $X$) → $Y$ $x$}, where backslash is the same thing as
lambda. We will use backslash exclusively for sums.
% (And hope it will be as invisible as possible.)

\begin{code}
π₀ : ∀{X : Set} {Y : X → Set} → (Σ \(x : X) → Y x) → X
π₀(x , y) = x
π₁ : ∀{X : Set} {Y : X → Set} → ∀(t : Σ \(x : X) → Y x) → Y(π₀ t)
π₁(x , y) = y
\end{code}
The identity type \AgdaC{Id $X$ $x$ $y$} is written
\AgdaC{$x$ ≡ $y$} with \AgdaC{$X$} implicit, and is inductively
defined as ``the least reflexive relation'':

\begin{code}
data _≡_ {X : Set} : X → X → Set where
  refl : ∀{x : X} → x ≡ x

sym : ∀{X : Set} → ∀{x y : X} → x ≡ y → y ≡ x
sym refl = refl
trans : ∀{X : Set} → ∀{x y z : X} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
cong : ∀{X Y : Set} → ∀(f : X → Y) → ∀{x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong f refl = refl
cong₂ : ∀{X Y Z : Set} → ∀(f : X → Y → Z)
      → ∀{x₀ x₁ : X}{y₀ y₁ : Y} → x₀ ≡ x₁ → y₀ ≡ y₁ → f x₀ y₀ ≡ f x₁ y₁
cong₂ f refl refl = refl
\end{code}

\subsection{Dialogues and continuity} \label{section:dialogues:continuity}

We consider the computation of functionals \AgdaC{($X$ → $Y$) → $Z$}
with dialogue trees. We work with the following inductively defined
type of (well founded) dialogue trees indexed by three types $X$, $Y$
and $Z$. These are $Y$-branching trees with $X$-labeled internal nodes
and $Z$-labeled leaves:

\begin{code}
data D (X Y Z : Set) : Set where
  η : Z → D X Y Z
  β : (Y → D X Y Z) → X → D X Y Z
\end{code}
A leaf is written \AgdaC{η $z$}, and it gives the final answer $z$ (η will
be the unit of a monad).  A forest is a $Y$-indexed family φ of
trees. Given such a forest \AgdaC{φ} and \AgdaC{$x$ : $X$}, we can build a
new tree \AgdaC{β φ $x$} whose root is labeled by $x$, which has a subtree
\AgdaC{φ $y$} for each \AgdaC{$y$ : $Y$}. We can imagine \AgdaC{$x$ : $X$} as
query, for which an oracle α gives some intermediate answer
\AgdaC{$y$ = α $x$ : Y}. After this answer~\AgdaC{$y$}, we move to the
subtree \AgdaC{φ $y$}, and the dialogue proceeds in this way, until a
leaf with the final answer is reached:

\begin{code}
dialogue : ∀{X Y Z : Set} → D X Y Z → (X → Y) → Z
dialogue (η z)   α = z
dialogue (β φ x) α = dialogue (φ(α x)) α
\end{code}
We say that a function \AgdaC{($X$ → $Y$) → $Z$} is \emph{eloquent} if
it is computed by some dialogue:

\begin{code}
eloquent : ∀{X Y Z : Set} → ((X → Y) → Z) → Set
eloquent f = Σ \d → ∀ α → dialogue d α ≡ f α
\end{code}
Here we are interested in the case \AgdaC{$X$=$Y$=$Z$=ℕ}.
Think of functions \AgdaC{α : ℕ → ℕ} as sequences of natural
numbers. The set of such sequences is called the Baire space:

\begin{code}
Baire : Set
Baire = ℕ → ℕ
\end{code}
Functions \AgdaC{Baire → ℕ} are coded by a particular kind of dialogue trees,
namely \AgdaC{B ℕ} where B is defined as follows:

\begin{code}
B : Set → Set
B = D ℕ ℕ
\end{code}
We work with a refined version of continuity, which gives more
information than the traditional notion introduced in
Section~\ref{formulation}, where the modulus of continuity is a finite
list of indices rather than an upper bound for the indices. The
agreement relation determined by a list of indices is inductively
defined as follows, where \AgdaC{\AgdaC{α ≡[ $s$ ] α$'$}} says that
the sequences \AgdaC{α} and \AgdaC{α$'$} agree at the indices
collected in the list \AgdaC{$s$}:

\begin{enumerate}
\item \AgdaC{α ≡[ [] ] α$'$},
\item \AgdaC{α $i$ ≡ α$'$ $i$ → α ≡[ $s$ ] α$'$ → α ≡[ $i$ ∷ $s$ ] α$'$}.
\end{enumerate}
We write this inductive definition as follows in Agda, where we give
the name~[] to the proof of the first clause and the name ∷ to the
proof of the second clause, that is, using the same constructor names
as for the inductively defined type of lists:

\begin{code}
data _≡[_]_ {X : Set} : (ℕ → X) → List ℕ → (ℕ → X) → Set where
  []  : ∀{α α' : ℕ → X} → α ≡[ [] ] α'
  _∷_ : ∀{α α' : ℕ → X}{i : ℕ}{s : List ℕ} → α i ≡ α' i → α ≡[ s ] α' → α ≡[ i ∷ s ] α'

continuous : (Baire → ℕ) → Set
continuous f = ∀(α : Baire) → Σ \(s : List ℕ) → ∀(α' : Baire) → α ≡[ s ] α' → f α ≡ f α'
\end{code}
It is an easy exercise, left to the reader, to produce an Agda proof
that this refined notion of continuity implies the traditional notion
of continuity, by taking the maximum value of the list~$s$.
Functions defined by dialogues are continuous, because a dialogue
produces an answer after finitely many queries:

\begin{code}
dialogue-continuity : ∀(d : B ℕ) → continuous(dialogue d)
dialogue-continuity (η n) α = ([] , lemma)
  where
    lemma : ∀ α' → α ≡[ [] ] α' → n ≡ n
    lemma α' r = refl
dialogue-continuity (β φ i) α = ((i ∷ s) , lemma)
  where
    IH : ∀(i : ℕ) → continuous(dialogue(φ(α i)))
    IH i = dialogue-continuity (φ(α i))
    s : List ℕ
    s = π₀(IH i α)
    claim₀ : ∀(α' : Baire) → α ≡[ s ] α' → dialogue(φ(α i)) α ≡ dialogue(φ(α i)) α'
    claim₀ = π₁(IH i α)
    claim₁ : ∀(α' : Baire) → α i ≡ α' i → dialogue (φ (α i)) α' ≡ dialogue (φ (α' i)) α'
    claim₁ α' r = cong (λ n → dialogue (φ n) α') r
    lemma : ∀(α' : Baire) → α ≡[ i ∷ s ] α'  → dialogue (φ(α i)) α ≡ dialogue(φ (α' i)) α'
    lemma α' (r ∷ rs) = trans (claim₀ α' rs) (claim₁ α' r)
\end{code}

\noindent This formal proof is informally explained as follows. We show that
\begin{quote}
  ∀($d$ : B ℕ) → continuous(dialogue $d$)
\end{quote}
by induction on $d$. Expanding the definition,
this amounts to,  using Agda notation,
\begin{quote}
  ∀ $d$ → ∀ α → Σ \char`\\$s$ → ∀ α$'$ → α ≡[ $s$ ] α$'$ → dialogue $d$ α ≡ dialogue $d$ α$'$.
\end{quote}
For the base case $d$ = η $n$, the definition of the function dialogue gives \AgdaC{dialogue $d$ α = $n$}, and so we must show that, for any α,
\begin{quote}
  Σ \char`\\$s$ → ∀ α$'$ → α ≡[ $s$ ] α$'$ → $n$ ≡ $n$.
\end{quote}
We can take $s = []$ and then we are done, because $n$ ≡ $n$ by reflexivity.
This is what the first equation of the formal proof says.
Thus notice that Agda, in accordance with MLTT, silently expands definitions by reduction to normal form.
For the induction step $d$ = β φ $i$, expanding the definition of the dialogue function, what we need to prove is that, for an arbitrary α,
\begin{quote}
  Σ \char`\\$s'$ → ∀ α$'$ → α ≡[ $s'$ ] α$'$ → dialogue (φ(α $i$)) α ≡ dialogue (φ α$'$ $i$) α$'$.
\end{quote}
The induction hypothesis is \AgdaC{∀($i$ : ℕ) → continuous(dialogue(φ(α $i$)))},
which gives, for any $i$ and our arbitrary α,
\begin{quote}
Σ \char`\\$s$ → ∀ α$'$ → α ≡[ $s$ ] α$'$ → dialogue(φ(α $i$)) α = dialogue(φ(α $i$)) α$'$.
\end{quote}
Using the two projections π₀ and π₁ we get $s$ and a proof that
\begin{quote}
∀ α$'$ → α ≡[ $s$ ] α$'$ → dialogue(φ(α $i$)) α = dialogue(φ(α $i$)) α$'$.
\end{quote}
Hence we can take $s'$ = $i$ ∷ $s$, and the desired conclusion holds
substituting equals for equals (with cong) using transitivity and the
definition α $i$ ≡ α$'$ $i$ → α ≡[ $s$ ] α$'$ → α ≡[ $i$ ∷ $s$ ]
α$'$. This amounts to the second equation of the proof, where in the
pattern of the proof of the lemma we have $r$ : α $i$ ≡ α$'$ $i$ and
$rs$ : α ≡[ $s$ ] α$'$.

~

We need the following technical lemma because it is not provable in
intensional MLTT that any two functions are equal if they are
pointwise equal. The proof is admitedly written in a rather
laconic form. The point is that the notion of continuity depends only
on the values of the function, and the hypothesis says that the two
functions have the same values. Notice that the axiom of function
extensionality (any two pointwise equal functions are equal) is not
false but rather not provable or disprovable, and is consistent~\cite{HoTTbook}.

\begin{code}
continuity-extensional : ∀(f g : Baire → ℕ) → (∀ α → f α ≡ g α) → continuous f → continuous g
continuity-extensional f g t c α = (π₀(c α) , (λ α' r → trans (sym (t α)) (trans (π₁(c α) α' r) (t α'))))
eloquent-is-continuous : ∀(f : Baire → ℕ) → eloquent f → continuous f
eloquent-is-continuous f (d , e) = continuity-extensional (dialogue d) f e (dialogue-continuity d)
\end{code}

The development for uniform continuity is similar to the above, with
the crucial difference that a dialogue tree in C ℕ is finite:

\begin{code}
Cantor : Set
Cantor = ℕ → ℕ₂
C : Set → Set
C = D ℕ ℕ₂
\end{code}
We work with a refined version of uniform continuity (cf.\
Section~\ref{formulation}), where the modulus is a finite binary tree
\AgdaC{$s$} of indices rather than an upper bound of the indices. We
could have worked with a list of indices, but the proofs are shorter
and more direct using trees. The agreement relation defined by a tree
of indices is inductively defined as follows, where α ≡[[ $s$ ]] α$'$
says that α and~α$'$ agree at the positions collected in the tree~$s$:

\begin{code}
data _≡[[_]]_ {X : Set} : (ℕ → X) → Tree ℕ → (ℕ → X) → Set where
  empty : ∀{α α' : ℕ → X} → α ≡[[ empty ]] α'
  branch :
    ∀{α α' : ℕ → X}{i : ℕ}{s : ℕ₂ → Tree ℕ}
    → α i ≡ α' i → (∀(j : ℕ₂) → α ≡[[ s j ]] α') → α ≡[[ branch i s ]] α'
\end{code}
Again we are using the same constructor names as for the type of trees.

\begin{code}
uniformly-continuous : (Cantor → ℕ) → Set
uniformly-continuous f = Σ \(s : Tree ℕ) → ∀(α α' : Cantor) → α ≡[[ s ]] α' → f α ≡ f α'

dialogue-UC : ∀(d : C ℕ) → uniformly-continuous(dialogue d)
dialogue-UC (η n) = (empty , λ α α' n → refl)
dialogue-UC (β φ i) = (branch i s , lemma)
  where
    IH : ∀(j : ℕ₂) → uniformly-continuous(dialogue(φ j))
    IH j = dialogue-UC (φ j)
    s : ℕ₂ → Tree ℕ
    s j = π₀(IH j)
    claim : ∀ j α α' → α ≡[[ s j ]] α' → dialogue (φ j) α ≡ dialogue (φ j) α'
    claim j = π₁(IH j)
    lemma : ∀ α α' → α ≡[[ branch i s ]] α' → dialogue (φ (α i)) α ≡ dialogue (φ (α' i)) α'
    lemma α α' (branch r l) = trans fact₀ fact₁
      where
        fact₀ : dialogue (φ (α i)) α ≡ dialogue (φ (α' i)) α
        fact₀ = cong (λ j → dialogue(φ j) α) r
        fact₁ : dialogue (φ (α' i)) α ≡ dialogue (φ (α' i)) α'
        fact₁ = claim (α' i) α α' (l(α' i))

UC-extensional : ∀(f g : Cantor → ℕ) → (∀(α : Cantor) → f α ≡ g α)
              → uniformly-continuous f → uniformly-continuous g
UC-extensional f g t (u , c) = (u , (λ α α' r → trans (sym (t α)) (trans (c α α' r) (t α'))))

eloquent-is-UC : ∀(f : Cantor → ℕ) → eloquent f → uniformly-continuous f
eloquent-is-UC f (d , e) = UC-extensional (dialogue d) f e (dialogue-UC d)
\end{code}
We finish this section by showing that the restriction of an eloquent
function \AgdaC{$f$ : Baire → ℕ} to the Cantor type is also eloquent. We first
define a pruning function from \AgdaC{B ℕ} to \AgdaC{C ℕ} that implements restriction:

\begin{code}
embed-ℕ₂-ℕ : ℕ₂ → ℕ
embed-ℕ₂-ℕ ₀ = zero
embed-ℕ₂-ℕ ₁ = succ zero

embed-C-B : Cantor → Baire
embed-C-B α = embed-ℕ₂-ℕ ∘ α

C-restriction : (Baire → ℕ) → (Cantor → ℕ)
C-restriction f = f ∘ embed-C-B

prune : B ℕ → C ℕ
prune (η n) = η n
prune (β φ i) = β (λ j → prune(φ(embed-ℕ₂-ℕ j))) i

prune-behaviour : ∀(d : B ℕ)(α : Cantor) → dialogue (prune d) α ≡ C-restriction(dialogue d) α
prune-behaviour (η n)   α = refl
prune-behaviour (β φ n) α = prune-behaviour (φ(embed-ℕ₂-ℕ(α n))) α

eloquent-restriction : ∀(f : Baire → ℕ) → eloquent f → eloquent(C-restriction f)
eloquent-restriction f (d , c) = (prune d , λ α → trans (prune-behaviour d α) (c (embed-C-B α)))
\end{code}

\subsection{Gödel's system T extended with an oracle} \label{section:oracle}

For simplicity, we work with system \AgdaC{T} in its original
combinatory form. This is no loss of generality, because both the
combinatory and the lambda-calculus forms define the same elements of
the set-theoretical model, and here we are interested in the
continuity of the definable functionals.  The system T type
expressions and terms are inductively defined as follows:

\begin{code}
data type : Set where
  ι          : type
  _⇒_ : type → type → type

data T : (σ : type) → Set where
  Zero   : T ι
  Succ   : T(ι ⇒ ι)
  Rec  : ∀{σ : type}     → T((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
  K    : ∀{σ τ : type}   → T(σ ⇒ τ ⇒ σ)
  S    : ∀{ρ σ τ : type} → T((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_  : ∀{σ τ : type}   → T(σ ⇒ τ) → T σ → T τ

infixr 1 _⇒_
infixl 1 _·_
\end{code}
Notice that there are five constants (or combinators) and one binary
constructor (application). Notice also that one can build only
well-typed terms.  The set-theoretical interpretation of type
expressions and terms is given by

\begin{code}
Set⟦_⟧ : type → Set
Set⟦ ι ⟧ = ℕ
Set⟦ σ ⇒ τ ⟧ = Set⟦ σ ⟧ → Set⟦ τ ⟧
\end{code}


\begin{code}
⟦_⟧ : ∀{σ : type} → T σ → Set⟦ σ ⟧
⟦ Zero ⟧  = zero
⟦ Succ ⟧  = succ
⟦ Rec ⟧   = rec
⟦ K ⟧     = Ķ
⟦ S ⟧     = Ş
⟦ t · u ⟧   = ⟦ t ⟧ ⟦ u ⟧
\end{code}
An element of the set-theoretical model is called T-definable if
there is a T-term denoting it:

\begin{code}
T-definable : ∀{σ : type} → Set⟦ σ ⟧ → Set
T-definable x = Σ \t → ⟦ t ⟧ ≡ x
\end{code}
As discussed above, the main theorem, proved in the last subsection, is
that every \AgdaC{T}-definable function \AgdaC{Baire → ℕ} is
continuous. The system \AgdaC{T} type of such functionals is \AgdaC{(ι
⇒ ι) ⇒ ι}.

We also consider system T extended with a formal oracle \AgdaC{Ω : ι ⇒
ι}:

\begin{code}
data TΩ : (σ : type) → Set where
  Ω    : TΩ(ι ⇒ ι)
  Zero   : TΩ ι
  Succ   : TΩ(ι ⇒ ι)
  Rec  : ∀{σ : type}     → TΩ((σ ⇒ σ) ⇒ σ ⇒ ι ⇒ σ)
  K    : ∀{σ τ : type}   → TΩ(σ ⇒ τ ⇒ σ)
  S    : ∀{ρ σ τ : type} → TΩ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  _·_  : ∀{σ τ : type}   → TΩ(σ ⇒ τ) → TΩ σ → TΩ τ
\end{code}
In the standard set-theoretical interpretation, the oracle can be
thought of as a free variable ranging over elements of the
interpretation Baire of the type expression \AgdaC{ι ⇒ ι}:

\begin{code}
⟦_⟧' : ∀{σ : type} → TΩ σ → Baire → Set⟦ σ ⟧
⟦ Ω ⟧'     α = α
⟦ Zero ⟧'  α = zero
⟦ Succ ⟧'  α = succ
⟦ Rec ⟧'   α = rec
⟦ K ⟧'     α = Ķ
⟦ S ⟧'     α = Ş
⟦ t · u ⟧'     α = ⟦ t ⟧' α (⟦ u ⟧' α)
\end{code}
To regard TΩ as an extension of T we need to work with an
embedding:

\begin{code}
embed : ∀{σ : type} → T σ → TΩ σ
embed Zero = Zero
embed Succ = Succ
embed Rec = Rec
embed K = K
embed S = S
embed (t · u) = (embed t) · (embed u)
\end{code}

\subsection{The dialogue interpretation of system \AgdaC{T}} \label{section:dialogue:interpretation}

We now consider an auxiliary interpretation of system T extended with
an oracle in order to show that the original T-definable functions
Baire → ℕ are continuous.  In the alternative semantics, types are
interpreted as the underlying objects of certain algebras of the
dialogue monad. The ground type is interpreted as the free algebra of
the standard interpretation, and function types as function sets.  For
the sake of brevity, we will include only the parts of the definition
of the monad that we actually need for our purposes.

\begin{code}
kleisli-extension : ∀{X Y : Set} → (X → B Y) → B X → B Y
kleisli-extension f (η x)   = f x
kleisli-extension f (β φ i) = β (λ j → kleisli-extension f (φ j)) i

B-functor : ∀{X Y : Set} → (X → Y) → B X → B Y
B-functor f = kleisli-extension(η ∘ f)
\end{code}
The following two lemmas are crucial. We first swap the two arguments
of the dialogue function to have the view that from an element of the
Baire type we get a B-algebra \AgdaC{B $X$ → $X$} for any \AgdaC{$X$}:

\begin{code}
decode : ∀{X : Set} → Baire → B X → X
decode α d = dialogue d α
\end{code}
The decodification map is natural for any oracle α : Baire:
%
%                  B g
%         B X --------------> B Y
%          |                   |
% decode α |                   | decode α
%          |                   |
%          v                   v
%          X ----------------> Y
%                   g
%

\begin{small}
\begin{diagram}[small]
\text{B $X$} & \rTo^{\text{B $g$}} & \text{B $Y$} \\
\dTo^{\text{decode α}} & & \dTo_{\text{decode α}} \\
X & \rTo_{g} & Y.
\end{diagram}
\end{small}

\begin{code}
decode-α-is-natural : ∀{X Y : Set}(g : X → Y)(d : B X)(α : Baire) → g(decode α d) ≡ decode α (B-functor g d)
decode-α-is-natural g (η x)   α = refl
decode-α-is-natural g (β φ i) α = decode-α-is-natural g (φ(α i)) α
\end{code}
The following diagram commutes for any \AgdaC{$f$ : $X$ → B $Y$}:
%
%                 kleisli-extension f
%            B X ---------------------> B Y
%             |                          |
%   decode α  |                          | decode α
%             |                          |
%             V                          |
%             X ---------> BY ---------> Y
%                 f           decode α

\begin{small}
\begin{diagram}[small]
\text{B $X$} & \rTo^{\text{~~~~~~~~~~~~kleisli-extension $f$}} & & & \text{B $Y$} \\
\dTo^{\text{decode α}} & & & & \dTo_{\text{decode α}} \\
X & \rTo_{f} & \text{B $Y$} & \rTo_{\text{decode α}} & Y.
\end{diagram}
\end{small}

\begin{code}
decode-kleisli-extension : ∀{X Y : Set}(f : X → B Y)(d : B X)(α : Baire)
  → decode α (f(decode α d)) ≡ decode α (kleisli-extension f d)
decode-kleisli-extension f (η x)   α = refl
decode-kleisli-extension f (β φ i) α = decode-kleisli-extension f (φ(α i)) α
\end{code}
System TΩ type expressions are interpreted as the underlying sets of
certain algebras of the dialogue monad. The base type is interpreted
as the underlying set of the free algebra of the standard interpretation, and function types
are interpreted as sets of functions,
exploiting the fact that algebras are exponential ideals (if $Y$ is
the underlying object of an algebra, then so is the set of all
functions $X$ → $Y$ for any $X$, with the pointwise structure).

\begin{code}
B-Set⟦_⟧ : type → Set
B-Set⟦ ι ⟧ = B(Set⟦ ι ⟧)
B-Set⟦ σ ⇒ τ ⟧ = B-Set⟦ σ ⟧ → B-Set⟦ τ ⟧
\end{code}
According to the official definition of an algebra of a monad, to show
that a set $X$ is the underlying object of an algebra one must provide a
structure map \AgdaC{B $X$ → $X$}. Alternatively, which is more
convenient for us, one can provide a generalized Kleisli extension
operator, defined as follows, where the base case is just Kleisli
extension, and the induction step is pointwise extension:

\begin{code}
Kleisli-extension : ∀{X : Set} {σ : type} → (X → B-Set⟦ σ ⟧) → B X → B-Set⟦ σ ⟧
Kleisli-extension {X} {ι} = kleisli-extension
Kleisli-extension {X} {σ ⇒ τ} = λ g d s → Kleisli-extension {X} {τ} (λ x → g x s) d
\end{code}
With this we can now define the dialogue interpretation of system TΩ.
The generic element of the Baire type under this
interpretation will interpret the Baire oracle Ω:

\begin{code}
generic : B ℕ → B ℕ
generic = kleisli-extension(β η)
\end{code}
As discussed in Section~\ref{formulation},
the crucial property of the generic element is this:
% the following diagram commutes for any \AgdaC{α : Baire}:
%
%                 generic
%          B ℕ ------------> B ℕ
%           |                 |
%           |                 |
%  decode α |                 | decode α
%           |                 |
%           |                 |
%           v                 v
%           ℕ --------------> ℕ
%                    α

\begin{small}
\begin{diagram}[small]
\text{B ℕ} & \rTo^{\text{generic}} & \text{B ℕ} \\
\dTo^{\text{decode α}} & & \dTo_{\text{decode α}} \\
\text{ℕ} & \rTo_{\text{α}} & \text{ℕ}.
\end{diagram}
\end{small}

\begin{code}
generic-diagram : ∀(α : Baire)(d : B ℕ) → α(decode α d) ≡ decode α (generic d)
generic-diagram α (η n) = refl
generic-diagram α (β φ n) = generic-diagram α (φ(α n))
\end{code}
The alternative interpretations of zero and successor are obvious:

\begin{code}
zero' : B ℕ
zero' = η zero
succ' : B ℕ → B ℕ
succ' = B-functor succ
\end{code}
And the interpretation of the primitive recursion combinator again
uses Kleisli extension in an obvious way:

\begin{code}
rec' : ∀{σ : type} → (B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧) → B-Set⟦ σ ⟧ → B ℕ → B-Set⟦ σ ⟧
rec' f x = Kleisli-extension(rec f x)
\end{code}
This gives the  dialogue interpretation. Notice that the interpretations
of K, S and application are standard. This is because we interpret
function types as sets of functions:

\begin{code}
B⟦_⟧ : ∀{σ : type} → TΩ σ → B-Set⟦ σ ⟧
B⟦ Ω ⟧     = generic
B⟦ Zero ⟧  = zero'
B⟦ Succ ⟧  = succ'
B⟦ Rec ⟧   = rec'
B⟦ K ⟧     = Ķ
B⟦ S ⟧     = Ş
B⟦ t · u ⟧   = B⟦ t ⟧ (B⟦ u ⟧)
\end{code}
This semantics gives the desired dialogue trees:

\begin{code}
dialogue-tree : T((ι ⇒ ι) ⇒ ι) → B ℕ
dialogue-tree t = B⟦ (embed t) · Ω ⟧
\end{code}

\noindent
The remainder of the development is the formulation and proof of the
correctness of the dialogue-tree function.  We conclude this section
with the trivial proof that the embedding of T into TΩ preserves the
standard interpretation and furthermore is independent of oracles:

\begin{code}
preservation : ∀{σ : type} → ∀(t : T σ) → ∀(α : Baire) → ⟦ t ⟧ ≡ ⟦ embed t ⟧' α
preservation Zero α = refl
preservation Succ α = refl
preservation Rec α = refl
preservation K α = refl
preservation S α = refl
preservation (t · u) α = cong₂ (λ f x → f x) (preservation t α) (preservation u α)
\end{code}

\subsection{Relating the two models} \label{section:logical:relation}

The main lemma is that for any term \AgdaC{$t$ : TΩ ι},
\begin{quote}
  ⟦ $t$ ⟧$'$ α ≡ decode α (B⟦ $t$ ⟧).
\end{quote}
We use the following logical relation to prove this:

\begin{code}
R : ∀{σ : type} → (Baire → Set⟦ σ ⟧) → B-Set⟦ σ ⟧ → Set

R {ι} n n' =
  ∀(α : Baire) → n α ≡ decode α n'

R {σ ⇒ τ} f f' =
  ∀(x : Baire → Set⟦ σ ⟧)(x' : B-Set⟦ σ ⟧) → R {σ} x x' → R {τ} (λ α → f α (x α)) (f' x')
\end{code}
We need a (fairly general) technical lemma, which is used for
constants with an interpretation using the Kleisli-extension
operator. In our case, this is just the recursion combinator.  The
proof is by induction on type expressions, crucially relying on the lemma
\emph{decode-kleisli-extension}, but is routine otherwise:

\begin{code}
R-kleisli-lemma : ∀(σ : type)(g : ℕ → Baire → Set⟦ σ ⟧)(g' : ℕ → B-Set⟦ σ ⟧)
  → (∀(k : ℕ) → R (g k) (g' k))
  → ∀(n : Baire → ℕ)(n' : B ℕ) → R n n' → R (λ α → g (n α) α) (Kleisli-extension g' n')

R-kleisli-lemma ι g g' rg n n' rn = λ α → trans (fact₃ α) (fact₀ α)
  where
    fact₀ : ∀ α → decode α (g' (decode α n')) ≡ decode α (kleisli-extension g' n')
    fact₀ = decode-kleisli-extension g' n'
    fact₁ : ∀ α → g (n α) α ≡ decode α (g'(n α))
    fact₁ α = rg (n α) α
    fact₂ : ∀ α → decode α (g' (n α)) ≡ decode α (g' (decode α n'))
    fact₂ α = cong (λ k → decode α (g' k)) (rn α)
    fact₃ : ∀ α → g (n α) α ≡ decode α (g' (decode α n'))
    fact₃ α = trans (fact₁ α) (fact₂ α)

R-kleisli-lemma (σ ⇒ τ) g g' rg n n' rn
  = λ y y' ry → R-kleisli-lemma τ (λ k α → g k α (y α)) (λ k → g' k y') (λ k → rg k y y' ry) n n' rn
\end{code}
The proof of the main lemma is by induction on terms, crucially
relying on the lemmas \emph{generic-diagram} (for the term
\AgdaC{Ω}), \emph{decode-is-natural} (for the term \AgdaC{Succ}) and
\emph{R-kleisli-lemma} (for the term \AgdaC{Rec}). The terms \AgdaC{K}
and \AgdaC{S} are routine (but laborious and difficult to get right in
an informal calculation), and so is the induction step for
application:

\begin{code}
main-lemma : ∀{σ : type}(t : TΩ σ) → R ⟦ t ⟧' (B⟦ t ⟧)

main-lemma Ω = lemma
  where
    claim : ∀ α n n' → n α ≡ dialogue n' α → α(n α) ≡ α(decode α n')
    claim α n n' s = cong α s
    lemma : ∀(n : Baire → ℕ)(n' : B ℕ) → (∀ α → n α ≡ decode α n')
          → ∀ α → α(n α) ≡ decode α (generic n')
    lemma n n' rn α = trans (claim α n n' (rn α)) (generic-diagram α n')

main-lemma Zero = λ α → refl
main-lemma Succ = lemma
  where
    claim : ∀ α n n' → n α ≡ dialogue n' α → succ(n α) ≡ succ(decode α n')
    claim α n n' s = cong succ s
    lemma : ∀(n : Baire → ℕ)(n' : B ℕ) → (∀ α → n α ≡ decode α n')
          → ∀ α → succ (n α) ≡ decode α (B-functor succ n')
    lemma n n' rn α = trans (claim α n n' (rn α)) (decode-α-is-natural succ n' α)
\end{code}

\begin{code}
main-lemma {(σ ⇒ .σ) ⇒ .σ ⇒ ι ⇒ .σ} Rec = lemma
  where
    lemma : ∀(f : Baire → Set⟦ σ ⟧ → Set⟦ σ ⟧)(f' : B-Set⟦ σ ⟧ → B-Set⟦ σ ⟧) → R {σ ⇒ σ} f f'
      → ∀(x : Baire → Set⟦ σ ⟧)(x' : B-Set⟦ σ ⟧)
      → R {σ} x x' → ∀(n : Baire → ℕ)(n' : B ℕ) → R {ι} n n'
      → R {σ} (λ α → rec (f α) (x α) (n α)) (Kleisli-extension(rec f' x') n')
    lemma f f' rf x x' rx = R-kleisli-lemma σ g g' rg
      where
        g : ℕ → Baire → Set⟦ σ ⟧
        g k α = rec (f α) (x α) k
        g' : ℕ → B-Set⟦ σ ⟧
        g' k = rec f' x' k
        rg : ∀(k : ℕ) → R (g k) (g' k)
        rg zero = rx
        rg (succ k) = rf (g k) (g' k) (rg k)

main-lemma K = λ x x' rx y y' ry → rx

main-lemma S = λ f f' rf g g' rg x x' rx → rf x x' rx (λ α → g α (x α)) (g' x') (rg x x' rx)

main-lemma (t · u) = main-lemma t ⟦ u ⟧' B⟦ u ⟧ (main-lemma u)
\end{code}
This gives the correctness of the dialogue-tree function defined
above: the standard interpretation of a term is computed by
its dialogue tree.

\begin{code}
dialogue-tree-correct : ∀(t : T((ι ⇒ ι) ⇒ ι))(α : Baire) → ⟦ t ⟧ α ≡ decode α (dialogue-tree t)
dialogue-tree-correct t α = trans claim₀ claim₁
  where
    claim₀ : ⟦ t ⟧ α ≡ ⟦ (embed t) · Ω ⟧' α
    claim₀ = cong (λ g → g α) (preservation t α)
    claim₁ : ⟦ (embed t) · Ω ⟧' α ≡ decode α (dialogue-tree t)
    claim₁ = main-lemma ((embed t) · Ω) α
\end{code}

\noindent The desired result follows directly from this:

\begin{code}
eloquence-theorem : ∀(f : Baire → ℕ) → T-definable f → eloquent f
eloquence-theorem f (t , r) = (dialogue-tree t , λ α → trans(sym(dialogue-tree-correct t α))(cong(λ g → g α) r))

corollary₀ : ∀(f : Baire → ℕ) → T-definable f → continuous f
corollary₀ f d = eloquent-is-continuous f (eloquence-theorem f d)

corollary₁ : ∀(f : Baire → ℕ) → T-definable f → uniformly-continuous(C-restriction f)
corollary₁ f d = eloquent-is-UC (C-restriction f) (eloquent-restriction f (eloquence-theorem f d))
\end{code}

\noindent This concludes the full, self-contained, MLTT proof in Agda
notation, given from scratch. Because MLTT proofs are programs, we can
run the two corollaries to compute moduli of (uniform) continuity of
T-definable functions.  Because MLTT itself has an interpretation in
ZF(C), in which types are sets in the sense of classical mathematics,
the results of this paper hold in classical mathematics too.  Because
the \LaTeX\ source for this article~\cite{escardo:dialogue} is
simultaneously an Agda file that type-checks, the readers don't need
to check the routine details of the proofs themselves, provided they
trust the minimal core of Agda used here, and can instead concentrate
on the interesting details of the constructions and proofs. One can
envisage a future in which it will be easier to write (constructive
and non-constructive) formal proofs than informal, rigorous proofs,
letting our minds concentrate on the insights. This is certainly a
provocative statement. But, in fact, the proof presented here was
directly written in its formal form, without an informal draft other
than a mental picture starting from the idea of generic sequence as
described in the introduction, with some rudimentary help by Agda to
perform the routine steps. Tactic-based systems such as e.g.\ Coq
provide much more help, which in some instances can be considered as
non-routine even if ultimately they are based on algorithms. But our
principal motivation for writing this formal proof in an MLTT or
realizability based computer system such as NuPrl, Coq, Lego, Agda,
Minlog etc.\ is that mentioned above, that the proof is literally a
program too, and hence can be used to compute moduli of (uniform)
continuity, without the need to write a separate algorithm based on an
informal, rigorous proof, as it is usually currently done, including
by ourselves in previous work.

Having said that, it is useful to have a self-contained informal
rigorous proof, which we include in the next section. Before that,
we conclude this section by running our formal constructive proof for
the purposes of illustration.

\subsection{Experiments} \label{section:experiments}

To illustrate the concrete sense in which the above formal proof is
constructive, we develop some experiments. These experiments are not
meant to indicate the usefulness of the theorem proved above. They
merely make clear that the theorems do have a concrete computational
content.

First of all, given a term \AgdaC{$t$ : (ι ⇒ ι) ⇒ ι}, we can compute
its modulus of (uniform) continuity.

\begin{code}
mod-cont : T((ι ⇒ ι) ⇒ ι) → Baire → List ℕ
mod-cont t α = π₀(corollary₀ ⟦ t ⟧ (t , refl) α)
mod-cont-obs : ∀(t : T((ι ⇒ ι) ⇒ ι))(α : Baire) → mod-cont t α ≡ π₀(dialogue-continuity (dialogue-tree t) α)
mod-cont-obs t α = refl

infixl 0 _∷_
infixl 1 _++_
_++_ : {X : Set} → List X → List X → List X
[] ++ u = u
(x ∷ t) ++ u = x ∷ t ++ u
flatten : {X : Set} → Tree X → List X
flatten empty = []
flatten (branch x t) = x ∷ flatten(t ₀) ++ flatten(t ₁)

mod-unif : T((ι ⇒ ι) ⇒ ι) → List ℕ
mod-unif t = flatten(π₀ (corollary₁ ⟦ t ⟧ (t , refl)))
\end{code}
The following Agda declaration allows us to write e.g.\ $3$ rather than
\AgdaC{succ(succ(succ zero))}:

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
\end{code}
A difficulty we face is that it is not easy to write system T
programs in the combinatory version of system~T. Hence we start by
developing some machinery.

\begin{code}
I : ∀{σ : type} → T(σ ⇒ σ)
I {σ} = S · K · (K {σ} {σ})
I-behaviour : ∀{σ : type}{x : Set⟦ σ ⟧} → ⟦ I ⟧ x ≡ x
I-behaviour = refl

number : ℕ → T ι
number zero = Zero
number (succ n) = Succ · (number n)
\end{code}
Here is our first example:

\begin{code}
t₀ : T((ι ⇒ ι) ⇒ ι)
t₀ = K · (number 17)
t₀-interpretation : ⟦ t₀ ⟧ ≡ λ α → 17
t₀-interpretation = refl
example₀ example₀' : List ℕ
example₀ = mod-cont t₀ (λ i → i)
example₀' = mod-unif t₀
\end{code}
These examples both evaluate to [].  To provide more sophisticated
examples, we work with an impoverished context γ that allows us to
consider just one free variable v, which is represented by the I
combinator:

\begin{code}
v : ∀{γ : type} → T(γ ⇒ γ)
v = I
\end{code}
Application for such a context amounts to the S combinator:

\begin{code}
infixl 1 _•_
_•_ : ∀{γ σ τ : type} → T(γ ⇒ σ ⇒ τ) → T(γ ⇒ σ) → T(γ ⇒ τ)
f • x = S · f · x

Number : ∀{γ} → ℕ → T(γ ⇒ ι)
Number n = K · (number n)
\end{code}
Here is an example:

\begin{code}
t₁ : T((ι ⇒ ι) ⇒ ι)
t₁ = v • (Number 17)
t₁-interpretation : ⟦ t₁ ⟧ ≡ λ α → α 17
t₁-interpretation = refl
example₁ : List ℕ
example₁ = mod-unif t₁
\end{code}
This evaluates to 17 ∷ [].

\begin{code}
t₂ : T((ι ⇒ ι) ⇒ ι)
t₂ = Rec • t₁ • t₁
t₂-interpretation : ⟦ t₂ ⟧ ≡ λ α → rec α (α 17) (α 17)
t₂-interpretation = refl
example₂ example₂' : List ℕ
example₂ = mod-unif t₂
example₂' = mod-cont t₂ (λ i → i)
\end{code}
These examples evaluate to 17 ∷ 17 ∷ 17 ∷ 0 ∷ 1 ∷ []
and to a list whose members are all 17.

\begin{code}
Add : T(ι ⇒ ι ⇒ ι)
Add = Rec · Succ
infixl 0 _+_
_+_ : ∀{γ} → T(γ ⇒ ι) → T(γ ⇒ ι) → T(γ ⇒ ι)
x + y = K · Add • x • y

t₃ : T((ι ⇒ ι) ⇒ ι)
t₃ = Rec • (v • Number 1) • (v • Number 2 + v • Number 3)
t₃-interpretation : ⟦ t₃ ⟧ ≡ λ α → rec α (α 1) (rec succ (α 2) (α 3))
t₃-interpretation = refl
example₃ example₃' : List ℕ
example₃ = mod-cont t₃ succ
example₃' = mod-unif t₃
\end{code}
These examples evaluate to 3 ∷ 2 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []
and 3 ∷ 2 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ 2 ∷ 1 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 0 ∷ 1 ∷ [].

\begin{code}
length : {X : Set} → List X → ℕ
length [] = 0
length (x ∷ s) = succ(length s)
max : ℕ → ℕ → ℕ
max 0 x = x
max x 0 = x
max (succ x) (succ y) = succ(max x y)
Max : List ℕ → ℕ
Max [] = 0
Max (x ∷ s) = max x (Max s)

t₄ : T((ι ⇒ ι) ⇒ ι)
t₄ = Rec • ((v • (v • Number 2)) + (v • Number 3)) • t₃
t₄-interpretation : ⟦ t₄ ⟧ ≡ λ α → rec α (rec succ (α (α 2)) (α 3)) (rec α (α 1) (rec succ (α 2) (α 3)))
t₄-interpretation = refl
example₄ example₄' : ℕ
example₄ = length(mod-unif t₄)
example₄' = Max(mod-unif t₄)
\end{code}
These examples evaluate to 215 and 3.

\begin{code}
t₅ : T((ι ⇒ ι) ⇒ ι)
t₅ = Rec • (v • (v • t₂ + t₄)) • (v • Number 2)
t₅-explicitly : t₅ ≡ (S · (S · Rec · (S · I · (S · (S · (K · (Rec · Succ)) · (S · I · (S · (S · Rec ·
                     (S · I · (K · (number 17))))· (S · I · (K · (number 17)))))) · (S · (S · Rec ·
                     (S · (S · (K · (Rec · Succ)) · (S · I · (S · I · (K · (number 2))))) · (S · I ·
                     (K · (number 3))))) · (S · (S · Rec · (S · I · (K · (number 1)))) · (S · (S ·
                     (K · (Rec · Succ)) · (S · I · (K · (number 2)))) · (S · I · (K · (number 3))))))))) ·
                     (S · I · (K · (number 2))))
t₅-explicitly = refl
t₅-interpretation : ⟦ t₅ ⟧ ≡ λ α → rec α (α(rec succ (α(rec α (α 17) (α 17))) (rec α (rec succ (α (α 2)) (α 3))
                                  (rec α (α 1) (rec succ (α 2) (α 3)))))) (α 2)
t₅-interpretation = refl
example₅ example₅' example₅'' : ℕ
example₅ = length(mod-unif t₅)
example₅' = Max(mod-unif t₅)
example₅'' = Max(mod-cont t₅ succ)
\end{code}
These examples evaluate to 15551, 17 and 57.  All evaluations reported
above are instantaneous, except this last set, which takes about a
minute in a low-end netbook. The use of Church encoding of dialogue
trees produces a dramatic performance
improvement~\cite{escardo:dialogue}, with an instantaneous answer in
these examples, because Klesli extension and the functor don't need to
walk through trees to be performed.

\section{Informal, rigorous proof} \label{section:informal}

\newcommand{\decode}{\operatorname{decode}}
\newcommand{\generic}{\operatorname{generic}}
\newcommand{\T}{\operatorname{T}}
\newcommand{\D}{\operatorname{D}}
\newcommand{\B}{\operatorname{B}}
\newcommand{\To}{\Rightarrow}
\newcommand{\Zero}{\operatorname{\mathtt{Zero}}}
\newcommand{\Succ}{\operatorname{\mathtt{Succ}}}
\newcommand{\Rec}{\operatorname{\mathtt{Rec}}}
\newcommand{\K}{\operatorname{\mathtt{K}}}
\renewcommand{\SS}{\operatorname{\mathtt{S}}}
\newcommand{\interp}[1]{\llbracket #1 \rrbracket}
\newcommand{\binterp}[1]{{\scriptstyle \B}\llbracket #1 \rrbracket}
\newcommand{\N}{\mathbb{N}}

We now provide a self-contained, informal, rigorous version of the
formal proof given above, in a foundationally neutral exposition.

We work with the combinatory version of (the term language of)
G\"odel's system~$\T$. We have a ground type~$\iota$ and a right-associative
type formation operation $-\To-$. Every term as a unique type. We have
the constants \begin{enumerate} \item $\Zero \colon \iota$.  \item
$\Succ \colon \iota \To \iota$.  \item $\Rec_{\sigma} \colon (\sigma
\To \sigma) \To \sigma \To \iota \To \sigma$.  \item $\K_{\sigma,\tau}
\colon \sigma \To \tau \To \sigma$.  \item $\SS_{\rho,\sigma,\tau}
\colon (\rho \To \sigma \To \tau) \To (\rho \To \sigma) \To \rho \To
\tau$.  \end{enumerate} We omit the subscripts when they can be
uniquely inferred from the context.  If $t \colon \sigma \To \tau$ and
$u \colon \tau$ are terms, then so is $tu \colon \tau$, with the
convention that this application operation is left associative.
Write $\T_\sigma$ for the set of terms of type~$\sigma$.

In the \emph{standard interpretation}, we map a type expression $\sigma$ to a set
$\interp{\sigma}$ and a term $t \colon \sigma$ to an element
$\interp{t} \in \interp{\sigma}$. These interpretations
are defined by induction as follows:
\begin{gather*}
\interp{\iota}  = \N,
\qquad \interp{\sigma \To \tau} = \interp{\tau}^{\interp{\sigma}} = ({\interp{\sigma}} \to \interp{\tau}) \,\,\text{(set of all functions $\interp{\sigma} \to \interp{\tau}$)}, \\[1ex]
\interp{\Zero} = 0,
\qquad \interp{\Succ} n = n+1,
\qquad \interp{\Rec} f x n  = f^n(x), \\[1ex]
\interp{\K} x y = x,
\qquad \interp{\SS} f g x = fx(gx),
\qquad \interp{tu} = \interp{t}(\interp{u}).
\end{gather*}
For any given three sets $X,Y,Z$, the set $\D X Y Z$ of \emph{dialogue trees}
is inductively defined as follows:
\begin{enumerate}
\item A leaf labeled by an element $z \in Z$ is a dialogue tree, written $\eta z$.
\item If $\phi \colon Y \to \D X Y Z$ is a $Y$-indexed family of dialogue trees and $x \in X$, then the tree with root labeled by $x$ and with one branch leading to the subtree $\phi y$ for each $y \in Y$  is also a dialogue tree, written $\beta \phi x$.
\end{enumerate}
Such trees are well founded, meaning that every path from the root to
a leaf is finite.  The above notation gives functions
\begin{eqnarray*}
  \eta & \colon & Z \to \D X Y Z, \\
  \beta & \colon & (Y \to \D X Y Z) \to X \to \D X Y Z.
\end{eqnarray*}
Dialogue trees describe ``computations'' of functions $f \colon Y^X
\to Z$.  Leaves give answers, and labels of internal nodes are queries
to an ``oracle'' $\alpha \in Y^X$, the argument of the function~$f$.
For any dialogue tree $d \in \D X Y Z$, we inductively define a function $f_d \colon
Y^X \to Z$ by
\[
f_{\eta z}(\alpha) = z,
\qquad
f_{\beta \phi x}(\alpha) = f_{\phi(\alpha x)}(\alpha).
\]
The functions $Y^X \to Z$ that arise in this way are called
\emph{eloquent}. Notice that the oracle $\alpha$ is queried
finitely many times in this computation, because a dialogue tree is
well founded. Hence the function $f = f_d \colon Y^X \to Z$
satisfies
\[
\forall \alpha \in Y^X \quad \exists \text{finite $S \subseteq X$ } \quad \forall \alpha' \in Y^X, \alpha =_S \alpha' \implies f\alpha=f\alpha',
\]
where $\alpha =_S \alpha'$ is a shorthand for $\forall x \in
S, \alpha x = \alpha'x$. When $X=Y=Z=\N$, this amounts to
continuity in the product topology of $\N^\N$ with $\N$ discrete,
which gives the Baire space.

For $Y$ finite and $X,Z$ arbitrary, the dialogue tree is finitely
branching and hence finite by well-foundedness (or directly by
induction), and so the set of potential queries to the oracle is
finite, so that, for any $f = f_d \colon Y^X \to Z$ with~$Y$ finite,
\[
\exists \text{finite $S \subseteq X$ } \forall \alpha,\alpha' \in Y^X, \quad
\alpha =_S \alpha' \implies f\alpha =f \alpha'.
\]
When $Y=2=\{0,1\}$ and $X=Z=\N$, this amounts to
(uniform) continuity in the product topology of $2^\N$ with $2$ discrete,
which gives the Cantor space.

Clearly, any $\N$-branching tree $d \in \D \N \N \N$ can be pruned to
a $2$-branching tree $d' \in \D \N 2 \N$ so that $f_{d'} : 2^\N \to
\N$ is the restriction of $f_d \colon \N^\N \to \N$ from sequences to
binary sequences.  Hence if we show that every $\T$-definable function
$\N^\N \to \N$ is eloquent, we conclude that every $\T$-definable
function $\N^\N \to \N$ is continuous and its restriction to $2^\N$ is
uniformly continuous. For this purpose, we consider an auxiliary
model of system $\T$.

Define $\B X = \D \N \N X$. We remark that although $\B$ is the object
part of a monad, as discussed in the introduction, it is not necessary
to know this for the purposes of this proof. The data given below do
obey the required laws to get a monad, but the details are left to the
interested reader.

For any function $f \colon X \to \B Y$,
inductively define $f^\sharp \colon \B X \to \B Y$ by
\begin{eqnarray*}
  f^\sharp(\eta x) &=& f x, \\
  f^\sharp(\beta \phi i) &=& \beta(\lambda j.f^\sharp(\phi j)) i.
\end{eqnarray*}
This says that the tree $f^\sharp(d)$ is $d$ with each leaf labeled by $x$
replaced by the subtree $f x$, with no changes to the internal nodes.
Given $f \colon X \to Y$, we define $f \colon \B X \to \B Y$ by
\[
\B f = (\eta \circ f)^\sharp.
\]
Hence $\B f(d)$ replaces each label $x$ of a leaf of $d$ by the
label $f(x)$, and we have the naturality condition
\begin{diagram}[small]
\B X & \rTo^{\B f} & \B Y \\
\uTo^{\eta} & & \uTo_{\eta} \\
X & \rTo_{f} & Y.
\end{diagram}
For each $\alpha \in \N^\N$ and any set $X$, define a
map $\decode_\alpha \colon \B X \to X$ by
\[
\decode_\alpha (d) = f_d(\alpha).
\]
Then, by definition, $\decode_\alpha(\eta x) = x$, and hence the
naturality of $\eta$ gives that of $\decode_\alpha$:
\begin{equation} \label{decode-is-natural}
\begin{diagram}[small]
\B X & \rTo^{\B f} & \B Y \\
\dTo^{\decode_\alpha} & & \dTo_{\decode_\alpha} \\
X & \rTo_{f} & Y.
\end{diagram}
\end{equation}
It is also easy to see, by induction on dialogue trees, that
\begin{equation} \label{decode:kleisli:extension}
\begin{diagram}[small]
\B X & & \rTo^{f^\sharp} & & \B Y \\
\dTo^{\decode_\alpha} & & & & \dTo_{\decode_\alpha} \\
X & \rTo_{f} & \B Y & \rTo_{\decode_\alpha} & Y.
\end{diagram}
\end{equation}
Now define
\begin{eqnarray*}
\generic & \colon & \B \N \to \B \N \\
\generic & = & (\beta \eta)^\sharp.
\end{eqnarray*}
Because $\beta \colon (\N \to \B \N) \to \N \to \B \N$ and $\eta
\colon \N \to \B \N$,
the function $\generic$ is well defined. Its crucial property is that
\begin{equation} \label{generic:diagram}
\begin{diagram}[small]
\B \N & \rTo^{\generic} & \B \N \\
\dTo^{\decode_\alpha} & & \dTo_{\decode_\alpha} \\
\N & \rTo_{\alpha} & \N.
\end{diagram}
\end{equation}
The proof that
\[
\decode_\alpha(\generic d) = \alpha(\decode_\alpha d)
\]
is straightforward by induction on $d$.

Now define the $\B$-interpretation of types as follows:
\begin{gather*}
\binterp{\iota}  = \B(\interp{\iota}) = \B \N, \qquad
\qquad \binterp{\sigma \To \tau} =  \binterp{\tau}^{\binterp{\sigma}}.
\end{gather*}
For any type $\sigma$ and $f \colon X \to \binterp{\sigma}$, define
$f^\sharp \colon \B X \to \binterp{\sigma}$ by induction on $\sigma$,
where the base case $\sigma = \iota$ is given by the above definition,
and the induction step $\sigma = (\rho \To \tau)$ is given pointwise as
\[
f^\sharp d y = (\lambda x. f x y)^\sharp d.
\]
Notice that $f \colon X \to \binterp{\rho} \to \binterp{\tau}$ and
$f^\sharp \colon \B X \to \binterp{\rho} \to \binterp{\tau}$.

Next extend system $\T$ with a new constant $\Omega \colon \iota \To
\iota$, a formal oracle, and define the $\B$-interpretation of terms
as follows:
\begin{gather*}
\binterp{\Omega} = \generic,
\quad \binterp{\Zero} = \eta 0,
\quad \binterp{\Succ} = \B(\lambda n.n+1),
\quad \binterp{\Rec}  f x = (\lambda n.f^n(x))^\sharp, \\[1ex]
\binterp{\K} x y = x,
\qquad \binterp{\SS} f g x = fx(gx),
\qquad \binterp{tu} = \binterp{t}(\binterp{u}).
\end{gather*}
We also need to consider the standard interpretation of system $\T$
extended with the oracle $\Omega$. We treat the oracle as a free
variable, as hence the value of this free variable has to be provided
to define the interpretation:
\begin{gather*}
\interp{\Omega} \alpha = \alpha,
\qquad \interp{\Zero} \alpha = 0,
\qquad \interp{\Succ} \alpha n = n+1,
\qquad \interp{\Rec} \alpha f x n  = f^n(x), \\[1ex]
\interp{\K} \alpha x y = x,
\qquad \interp{\SS} \alpha f g x = fx(gx),
\qquad \interp{tu} \alpha  = \interp{t}\alpha (\interp{u} \alpha).
\end{gather*}
We claim that for any term $t \colon \iota$,
\[
  \interp{t} \alpha = \decode_\alpha (\binterp{t}).
\]
To prove this, we work with a logical relation $R_\sigma$ between
functions $\N^\N \to \interp{\sigma}$ and elements of
$\binterp{\sigma}$ by induction on $\sigma$.
For any $n \colon \N^\N \to \N$ and $n' \in \B \N$, we define
\[ R_\iota n n' \iff \forall \alpha, n \alpha = \decode_\alpha n', \]
and, for any $f \colon \N^\N \to \interp{\sigma} \to \interp{\tau}$
and $f' \colon \binterp{\sigma} \to \binterp{\tau}$, we define
\[ R_{\sigma \to \tau} f f' \iff
  \forall x \colon \N^\N \to \interp{\sigma}, \,\, \forall x' : \binterp{\sigma}, \,\, R_{\sigma} x x' \to R_\tau (\lambda \alpha, f \alpha (x \alpha)) (f' x').\]
We need a technical lemma for
dealing with the dialogue interpretation of $\Rec$:
\begin{claim} \label{R:kleisli:claim}
For all $g \colon \N  \to \N^\N \to \binterp{\sigma}$ and $g' \colon \N \to \binterp{\sigma}$, if
\[
\forall k \in \N, \,\, R_{\sigma} (g k) (g' k),
\]
then
$
\forall n \colon \N^\N \to \N, \,\, \forall n' \in \B \N, \,\, R_{\iota} n n' \to
R_{\sigma} (\lambda \alpha \to g (n \alpha) \alpha) (g' n')^\sharp.
$
\end{claim}
The proof is straightforward by induction on types, using
diagram~\ref{decode:kleisli:extension}.

\begin{claim}
  $R_\sigma \, \interp{t} \, (\binterp{t})$ for every term $t \colon \sigma$.
\end{claim}
The proof is by induction on terms, using diagram~\ref{generic:diagram}
for the term~$\Omega$, diagram~\ref{decode-is-natural} for the term~$\Succ$,
and Claim~\ref{R:kleisli:claim} for the term~$\Rec$. The terms~$\K$ and~$\SS$ are
immediate but perhaps laborious, and the induction step, namely term
application, is easy.  This gives, in particular:
\begin{claim}
  For every term $t \colon (\iota \To \iota) \To \iota$, we have
  $ \interp{t} \alpha = \decode_\alpha (\binterp{t\Omega}).$
\end{claim}
It follows that every $\T$-definable function $f \colon \N^\N \to \N$ is
eloquent, with dialogue tree given by $\binterp{t\Omega}$, where $t \colon (\iota \To \iota) \To \iota$
is any term denoting~$f$,
and hence continuous, with uniformly continuous restriction to~$2^\N$.

\section{Discussion, questions and conjectures}

It may not be apparent from the informal proof of
Section~\ref{section:informal} that the argument is constructive, but
Section~\ref{section:formal} provides a constructive rendering in
Martin-L\"of type theory.  We emphasize that our proof doesn't invoke
the Fan Theorem~\cite{MR0325352,beeson} or any constructively
contentious axiom.

We have deliberately chosen system T in its combinatory form as the
simplest and most memorable non-trivial higher-type language to
illustrate the essence of the technique proposed here. It is clearly
routine (as well as interesting and useful) to apply the technique to
a number of well-known extensions of the simply-typed
lambda-calculus. But, for instance, at the time of writing, dependent
types seem to require further thought, particularly in the presence of
universes. Can one, e.g.\ (generalize and) apply the technique
developed here to show that all MLTT definable functions \AgdaC{(ℕ →
ℕ) → ℕ} are continuous, and that their restrictions to \AgdaC{(ℕ → 2)}
are uniformly continuous, in the main versions of (intensional) MLTT?
More ambitiously, does the technique apply to Homotopy Type
Theory~\cite{HoTTbook}?

As pointed out by one of the anonymous referees, the syntactical
techniques of~\cite{MR0325352} give more information: for any term $t$
of type $(\iota \Rightarrow \iota) \Rightarrow \iota$ one can
construct a term $m : (\iota \Rightarrow \iota) \Rightarrow \iota$
such that $m$ internalizes the modulus of continuity of $t$. We
adapted our technique to achieve this, as reported
in~\cite{escardo:dialogue}, by working with Church encodings of
dialogue trees defined within system~T, and turning our semantical
interpretation into a compositional translation of system~T into
itself. A corollary is that the dialogue trees of T-definable
functions \AgdaC{(ℕ → ℕ) → ℕ}, being themselves T-definable, have
height smaller than $\epsilon_0$.



% \bibliographystyle{plain}
% \bibliography{references}

\begin{thebibliography}{10}

\bibitem{bauer:pretnar}
A.~Bauer and M.~Pretnar.
\newblock Programming with algebraic effects and handlers.
\newblock Submitted for publication, 2012.

\bibitem{beeson}
M.J. Beeson.
\newblock {\em Foundations of Constructive Mathematics}.
\newblock Springer, 1985.

\bibitem{bishop:foundations}
E.~Bishop.
\newblock {\em Foundations of constructive analysis}.
\newblock McGraw-Hill Book Co., New York, 1967.

\bibitem{bove:dybjer}
A.~Bove and P.~Dybjer.
\newblock Dependent types at work.
\newblock {\em Proceedings of Language Engineering and Rigorous Software
  Development, LNCS}, 5520:57--99, 2009.

\bibitem{Coquand:2010:NFT:1839560.1839564}
T.~Coquand and G.~Jaber.
\newblock A note on forcing and type theory.
\newblock {\em Fundam. Inf.}, 100(1-4):43--52, January 2010.

\bibitem{DBLP:series/leus/CoquandJ12}
T.~Coquand and G.~Jaber.
\newblock A computational interpretation of forcing in type theory.
\newblock In {\em Epistemology versus Ontology}, pages 203--213. Springer,
  2012.

\bibitem{escardo:dialogue}
M.H. Escard\'o.
\newblock Continuity of {G}\"odel's system {T} definable functionals via
  effectful forcing.
\newblock Agda proof at \url{http://www.cs.bham.ac.uk/~mhe/dialogue/}, July
  2012.

\bibitem{Hancock_representationsof}
P.~Hancock, D.~Pattinson, and N.~Ghani.
\newblock Representations of stream processors using nested fixed points.
\newblock In {\em Logical Methods in Computer Science}, page 2009.

\bibitem{Howard(80)}
W.~A. Howard.
\newblock Ordinal analysis of terms of finite type.
\newblock {\em The Journal of Symbolic Logic}, 45:493--504, 1980.

\bibitem{KleeneSC:rfqftI}
S.C. Kleene.
\newblock Recursive functionals and quantifiers of finite types {I}.
\newblock {\em Trans.\ Amer.\ Math.\ Soc}, 91, 1959.

\bibitem{Longley99whenis}
J.~Longley.
\newblock When is a functional program not a functional program?
\newblock In {\em Proceedings of Fourth ACM SIGPLAN International Conference on
  Functional Programming}, pages 1--7. ACM Press, 1999.

\bibitem{DBLP:conf/csl/HancockS00}
P.Hancock and A.~Setzer.
\newblock Interactive programs in dependent type theory.
\newblock In {\em CSL}, pages 317--331, 2000.

\bibitem{Plotkin03algebraicoperations}
G.~Plotkin and J.~Power.
\newblock Algebraic operations and generic effects.
\newblock {\em Applied Categorical Structures}, 11, 2003.

\bibitem{HoTTbook}
The Univalent~Foundations Program.
\newblock Homotopy type theory: Univalent foundations of mathematics.
\newblock Technical report, Institute for Advanced Study, 2013.

\bibitem{MR0325352}
A.~S. Troelstra, editor.
\newblock {\em Metamathematical investigation of intuitionistic arithmetic and
  analysis}.
\newblock Lecture Notes in Mathematics, Vol. 344. Springer-Verlag, Berlin,
  1973.

\bibitem{escardo:xu}
C.~Xu and M.H. Escard\'o.
\newblock A constructive model of uniform continuity.
\newblock To appear in TLCA, 2013.

\end{thebibliography}


\end{document}
