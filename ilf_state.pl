/* File ilf_state.pl 
* For simplicity we don't parse configuration parameters from .ilfrc but write them directly here in Prolog format
*/
/* pciwm11
:- setval(prologhome,"//C/Program Files/ECLiPSe 6.0/lib"),
   setval(userilfhome,"//C/Users/dahn/CloudStation/ILF/ilf16"),
   setval(ilfhome,"//C/Users/dahn/CloudStation/ILF/ilf16"),
   setval(default_proof_file,"//C/Users/dahn/CloudStation/ILF/ilf16/proof.tex").
*/

/* Lenovo 
:- setval(prologhome,"//D/Programme/ECLiPSe 6.1/lib"),
   setval(userilfhome,"//D/User/CloudStation/ILF/ilf16"),
   setval(ilfhome,"//D/User/CloudStation/ILF/ilf16"),
   setval(default_proof_file,"//D/User/CloudStation/ILF/ilf16/proof.tex").
*/

/* Toshiba */
:- setval(prologhome,"//C/Program Files/ECLiPSe 6.1/lib"),
   setval(userilfhome,"//C/Users/dahn/CloudStation/ILF/ilf16"),
   setval(ilfhome,"//C/Users/dahn/CloudStation/ILF/ilf16"),
   setval(default_proof_file,"//C/Users/dahn/CloudStation/ILF/ilf16/proof.tex").

/* General */
:- setval(occur_check,off),
   setval(debug,on),
   setval(out_mode,latex),
   setval(style,none),
%   setval(known_rules,[copy(_),rewrite(_),back_rewrite(_),flip(_),para(_,_)]),
	setval(known_rules,[_]),
   setval(proof_title,"Joao's Proof"),
   setval(proof_author,"Prover 9 and ILF"),
   setval(tex_format,"\\documentclass[a4]{article}\n\
\n\
% ILF_STYLE 1.4 (03/25/97)\n\
  \\newlength{\\ilfformulalength}\\setlength{\\ilfformulalength}{\\textwidth}\n\
  \\addtolength{\\ilfformulalength}{-7em}\n\
  \\ifx\\mathindent\\undefined\n\
    \\newcommand{\\ilftformel}[1]{\\begin{equation}%\n\
\\parbox{\\ilfformulalength}{\\centering #1}\\end{equation}}\n\
  \\else\n\
    \\addtolength{\\ilfformulalength}{-\\mathindent}\n\
    \\newcommand{\\ilftformel}[1]{\\begin{equation}%\n\
\\parbox{\\ilfformulalength}{#1}\\end{equation}}\n\
\\fi\n\
  \\newcommand{\\ilfformula}[1]{\\ilftformel{$ #1 $}}\n\
  \\newenvironment{ilfproof}[1]{%\n\
Proof\\/\\footnote{#1}.}{\\begin{quote}\\raggedleft q.e.d.\\end{quote}}\n\
  \\newenvironment{ilf_cases}{%\n\
\\renewcommand{\\labelenumi}{Case \\arabic{enumi}.}\\begin{enumerate}}%\n\
{\\end{enumerate}}\n\
  \\newcommand{\\ilfUpCase}[1]{\\ifmmode#1\\else\\uppercase{#1}\\fi}\n\
  \\newcommand{\\ilftext}[1]{\\ifmmode$#1$\\else#1\\fi}\n\
  \\newcounter{ilflistdepth}\\setcounter{ilflistdepth}{0}\n\
  \\newcounter{ilflistolddepth}\n\
  \\newcounter{ilflistmaxdepth}\\setcounter{ilflistmaxdepth}{0}\n\
  \\newlength{\\ilflistmargin}\\settowidth{\\ilflistmargin}{1.\\ }\n\
  \\newcommand\\ilflistempty{}\n\
  \\newcommand\\ilflistconstlabel{}\n\
  \\def\\ilflistlabeli{}\n\
  \\def\\ilflistsetlabel#1#2{\\ifnum#2=0\\else\n\
\\ilflistsetlabelA{\\romannumeral#1}{\\romannumeral#2}\\fi}\n\
  \\def\\ilflistsetlabelA#1#2{\\expandafter\\xdef\\csname ilflistlabel#1\\endcsname{%\n\
\\csname ilflistlabel#2\\endcsname\\arabic{ilflist#2}.\\ }}\n\
  \\def\\ilflistlabel#1{\\ilflistconstlabel%\n\
\\csname ilflistlabel#1\\endcsname\\arabic{ilflist#1}.\\ }\n\
\\expandafter\\def\\csname p@ilflisti\\endcsname{}\n\
  \\def\\ilflistsetpa#1#2{\\ifnum#2=0\\else\n\
\\ilflistsetpaA{\\romannumeral#1}{\\romannumeral#2}\\fi}\n\
  \\def\\ilflistsetpaA#1#2{\\expandafter\\xdef\\csname p@ilflist#1\\endcsname{%\n\
\\csname p@ilflist#2\\endcsname\\arabic{ilflist#2}.}}\n\
  \\newenvironment{ilflist}[1]{\\par\\vspace{\\topsep}\\parskip\\parsep%\n\
\\advance\\leftskip by \\ilflistmargin%\n\
\\ifnum\\theilflistdepth=0\\advance\\leftskip by \\ilflistmargin\\fi%\n\
\\renewcommand\\ilflistconstlabel{#1}\n\
\\ifx\\ilflistconstlabel\\ilflistempty\\else\\renewcommand\\ilflistconstlabel{#1\\ }\\fi\n\
\\setcounter{ilflistolddepth}{\\theilflistdepth}\n\
\\addtocounter{ilflistdepth}{1}%\n\
\\ifnum\\theilflistdepth >\\theilflistmaxdepth\\relax%\n\
\\newcounter{ilflist\\romannumeral\\theilflistdepth}%\n\
\\setcounter{ilflistmaxdepth}{\\theilflistdepth}\\fi%\n\
\\setcounter{ilflist\\romannumeral\\theilflistdepth}{0}%\n\
\\ilflistsetpa{\\theilflistdepth}{\\theilflistolddepth}%\n\
\\ilflistsetlabel{\\theilflistdepth}{\\theilflistolddepth}}%\n\
{\\par\\vspace{\\topsep}%\n\
\\addtocounter{ilflistdepth}{-1}\\advance\\leftskip by -\\ilflistmargin%\n\
\\ifnum\\theilflistdepth=0\\advance\\leftskip by -\\ilflistmargin\\fi}\n\
  \\newcommand{\\ilfitem}{\\par\\vspace{\\itemsep}%\n\
\\hspace*{-\\ilflistmargin}\\hspace*{-\\parindent}%\n\
\\refstepcounter{ilflist\\romannumeral\\theilflistdepth}%\n\
\\ilflistlabel{\\romannumeral\\theilflistdepth}\\ignorespaces}\n\
  \\newtheorem{axiom}{Axiom}[section]\n\
  \\newtheorem{sysinfo}{System Information}\n\
  \\newtheorem{conjecture}{Conjecture}[section]\n\
  \\newtheorem{theorem}{Theorem}[section]\n\
  \\newtheorem{lemma}{Lemma}[section]\n\
% END ILF_STYLE\n\
").

