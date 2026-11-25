#pragma once

#include <string>

namespace proof {

// A minimal offline TeX installation can lack hyperref. The three PDF
// engines can still emit named destinations and whole-phrase annotations.
inline constexpr char documentLinks[] = R"tex(\IfFileExists{hyperref.sty}{%
  \IfFileExists{color.sty}{\usepackage{color}\definecolor{paperlinkblue}{rgb}{0.10,0.25,0.42}%
    \usepackage[colorlinks=true,linkcolor=paperlinkblue]{hyperref}}{\usepackage[hidelinks]{hyperref}}%
}{}
\ifdefined\hyperlink
  \newcommand{\paperanchor}[1]{\hypertarget{#1}{}}%
  \newcommand{\paperlink}[2]{\hyperlink{#1}{\begin{NoHyper}#2\end{NoHyper}}}%
\else
  \ifdefined\pdfextension
    \ifnum\outputmode>0
      \def\paperdest{\pdfextension dest}\def\paperstart{\pdfextension startlink}%
      \def\paperend{\pdfextension endlink}\def\papercolor{\pdfextension colorstack}%
    \fi
  \else\ifdefined\pdfstartlink
    \ifnum\pdfoutput>0
      \let\paperdest\pdfdest\let\paperstart\pdfstartlink\let\paperend\pdfendlink\let\papercolor\pdfcolorstack
    \fi
  \fi\fi
  \ifdefined\paperdest
    \newcommand{\paperanchor}[1]{\paperdest name{#1} xyz}%
    \newcommand{\paperlink}[2]{\leavevmode\paperstart attr{/Border [0 0 0]} goto name{#1}%
      \papercolor 0 push {0.10 0.25 0.42 rg 0.10 0.25 0.42 RG}#2\papercolor 0 pop\paperend}%
  \else\ifdefined\XeTeXversion
    \newcommand{\paperanchor}[1]{\special{pdf:dest (#1) [@thispage /XYZ null @ypos null]}}%
    \newcommand{\paperlink}[2]{\leavevmode\special{pdf:bann << /Subtype /Link /Border [0 0 0] /A << /S /GoTo /D (#1) >> >>}%
      \special{color push rgb 0.10 0.25 0.42}#2\special{color pop}\special{pdf:eann}}%
  \else
    \PackageError{lean-to-latex}{No PDF hyperlink backend available}{Use XeLaTeX, pdfLaTeX, LuaLaTeX, or install hyperref.}%
  \fi\fi
\fi
\newcommand{\paperlineanchor}[1]{\raisebox{10pt}[0pt][0pt]{\paperanchor{#1}}}
\DeclareRobustCommand{\paperresultname}[1]{\paperlineanchor{theorem:\arabic{theorem}}#1}
)tex";

inline std::string paperLink(const std::string& destination, const std::string& text) {
    return "\\paperlink{" + destination + "}{" + text + "}";
}

inline std::string numberedReference(const std::string& prefix, const std::string& destination) {
    return paperLink(destination,prefix + "\\ref{" + destination + "}");
}

} // namespace proof
