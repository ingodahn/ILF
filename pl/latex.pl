/*
 * @(#)latex.pl	1.33 (7/4/98)
 *
 * Ausgabe von Formeln und Beweisen für LaTeX
 *
 * basierend auf: ptex.pro 1.56 (06/06/96)
 * Aufbereitung der Axiome einer Theorie fuer TeX
 * Autoren: Dahn, Becker,Allner
 * Portierung nach Eclipse Prolog: Honigmann
 */

:- module_interface(latex).

:- begin_module(latex).

:- import ilfsys.

:- import
	apply_texop/2,
	apply_texop0/2,
	clear_varnumbers/0,
	find_file/3,
	ini_varnames/0,
	open_file/2,
	show_item/3,
        show_fla/2,
        show_fla0/2,
        show_fla0_list/3,
	show_type/2,
        tex_op/3,
        try_texop/3
	        from outtools.

:- dynamic 
	env/1.

file_extension(".tex").

/* Nachbearbeitung des tex-files */

postprocess_file(TempFileName, LabelList, RefList, Pid, Out) :-
	concat_strings(TempFileName, ".ref", RefFileName),
	write_ref_file(LabelList, RefList, RefFileName),
	get_right_file("bin/ppout.pl", PPLatex),
	os_file_name(PPLatex,PPLatexOs),
	os_file_name(RefFileName,RefFileNameOs),
	os_file_name(TempFileName,TempFileNameOs),
	% concat_string([PPLatexOs," -m latex -r ",RefFileNameOs," ",TempFileNameOs],CmdPar),
	% Cmd=["perl",CmdPar],
	ilfsys:spy_ilf,
	Cmd=["perl",PPLatexOs, "-m", "latex", "-r", RefFileNameOs, TempFileNameOs],
	exec(Cmd, [null, Out, null], Pid),
	/*
	exec(Cmd, [null]),
	read_string(Out, end_of_file, _, Message),
	close(Out),
	writeln(result=Message),
	wait(Pid, Status),
	writeln(status=Status),
	*/
	!.

write_ref_file(LabelList, RefList, RefFile) :-
	open(RefFile, write, RefStream),
	write_ll(RefStream, LabelList),
	writeln(RefStream, ""),
	write_rl(RefStream, LabelList),
	write_rl(RefStream, RefList),
	close(RefStream).

write_ll(_, []).
write_ll(RefStream, [Label|LabelList]) :-
	printf(RefStream, "%Dw\n", [Label]),
	write_ll(RefStream, LabelList).

write_rl(_, []).
write_rl(Stream, [Ref-Type-Name|RefList]) :-
	printf(Stream, "%Dw\n", [Ref]),
	(Name = [] ->
		NameS = ""
		;
		apply_texop(Name, NameS)
	),
	(NameS = "" ->
		apply_texop0(Type, TypeS),
		printf(Stream, "%w \\ref{%Dw}\n", [TypeS, Ref]),
		firstup(TypeS, TypeS1),
		printf(Stream, "%w \\ref{%Dw}\n", [TypeS1, Ref])
		;
		writeln(Stream, NameS),
		firstup(NameS, NameS1),
		writeln(Stream, NameS1)
	),
	write_rl(Stream, RefList).
write_rl(Stream, [Ref|RefList]) :-
	printf(Stream, "%Dw\n", [Ref]),
	printf(Stream, "(\\ref{%Dw})\n", [Ref]),
	printf(Stream, "(\\ref{%Dw})\n", [Ref]),
	write_rl(Stream, RefList).


/* TeX't das File mit dem uebergebenen Namen (plus Endung .tex) und
   zeigt das entstandene dvi-File an (jeweils fuer Theorien und Beweise).
   Die gegenwaertige Implementation ist recht rudimentaer, wuenschens-
   wert waere es, auf Fehler in der TeX-Bearbeitung zu reagieren und
   den zweiten TeX-Lauf nur dann durchzufuehren, wenn er notwendig ist.
   Der Viewer sollte ueber ilf_state's konfigurierbar sein.
   Ausserdem waere zu klaeren, ob evtl. ein einheitliches make_viewable
   moeglich ist.  */

view(FileName) :-
	find_file(FileName, ".dvi", Path),
	!,
	view0(Path).
view(FileName) :-
	find_file(FileName, ".tex", Path),
	!,
	view0(Path).
view(FileName) :-
	ilf_error("File %w[.tex,.dvi] not found.", [FileName]),
	!,
	fail.

view0(FileName) :-
	get_right_file("bin/view_dvi", ViewDvi),
	once(ilf_state(latex_viewer, Viewer) ; Viewer=ViewDvi),
	(ilf_state(debug, on) ->
		concat_string([Viewer, " -d ", FileName], ViewCmd)
		;
		concat_string([Viewer, " ", FileName], ViewCmd)
	),
	sh(ViewCmd).

print_dvi :-
	ilf_state(default_proof_file, FileName),
	print(FileName).

print_dvi(FileName) :-
	find_file(FileName, ".dvi", Path),
	latex(Path),
	concat_strings(Path, ".dvi", DviFileName),
	concat_string(["dvips -f ", DviFileName, "| lpr "], PrtCmd),
	printf("Printing ... ", []), flush(output),
	sh(PrtCmd),
	printf("done.", []).

latex(FileName) :-
	find_file(FileName, ".tex", Path),
	concat_strings(Path, ".tex", TexFileName),
	exists(TexFileName),
	concat_strings(Path, ".dvi", DviFileName),
	concat_string([
		"cat /dev/null >", DviFileName, "; ",
		"cd `dirname ", TexFileName, "`; ",
		"latex ", TexFileName, " </dev/null >/dev/null; ",
		"latex ", TexFileName, " </dev/null >/dev/null"], LatexCmd),
	write("Running LaTeX ... "), flush(output),
	sh(LatexCmd),
	!,
	check_size(Path).
	 	
check_size(FileName) :-
	concat_strings(FileName, ".dvi", DviFileName),
	get_file_info(DviFileName, size, Size),
	Size >0,
	!,
	write("done.\n").
check_size(FileName) :-
	printf("ERROR!\nPlease check %w.log.\n", [FileName]),
	fail.

/* "technical Header", d.h. documentstyle ... */

technical_header_th(Stream) :-
	print_format(Stream),
	printf(Stream, "\
\\newcommand{\\ilfUpCase}[1]{\\ifmmode#1\\else\\uppercase{#1}\\fi}\n\
\\newcommand{\\ilftext}[1]{\\ifmmode$#1$\\else#1\\fi}\n\
\\begin{document}\n\n\
"	, []),
	!.

technical_header(Stream) :-
	print_format(Stream),
	printf(Stream, "\
\\begin{document}\n\n\
", []),
%	printf(Stream, "\\begin{document}\n\n", []),
	print_style(Stream),
	!.

print_format(Stream) :-
	(
		ilf_state(tex_format, Format0)
		;
		default_tex_format(Format0)
	),
	show_item(tex_format, Format0, Format),
	!,
	write(Stream, Format),
	write(Stream, "\n").


default_tex_format("\
\\documentstyle{article}\n\
\\oddsidemargin0pt\n\
\\evensidemargin0pt\n\
\\parindent0pt\n\
\\parskip1ex\n").

print_style(_) :- 
	ilf_state(style,none),!.
print_style(Stream) :- 
	get_right_file(".ilfstyle", IlfStyleFile),
	open(IlfStyleFile, read, IlfStyleStream),
	read_string(IlfStyleStream, "", _, IlfStyle),
	close(IlfStyleStream),
	write(Stream, IlfStyle).

clearall :- 
	retract_all(env(_)).
	
/* title/3 Ausgabe des Titels und des Authors eines Dokuments.
   Es werden zunaechst ggf. texops fuer title und author ausgewertet. */

title(Stream, Title, Author) :- 
	show_item(title, Title, TitleS),
	show_item(author, Author, AuthorS),
	title0(Stream, TitleS, AuthorS).

title0(Stream, Title, Author) :- 
	ilf_note(Note),
	printf(Stream, "\\title{%w%w}\n", [Title, Note]),
	printf(Stream, "\\author{%w}\n", [Author]),
	printf(Stream, "\\maketitle\n", []),
	!.

ilf_note("\
\\thanks{\\fussy This manuscript was generated by ILF.\n\
The development of ILF was supported by the Deutsche Forschungsgemeinschaft.\n\
For information on ILF contact\n\
ilf--serv--request@ma\\-the\\-ma\\-tik.hu-ber\\-lin.de.}").

/* "technical trailer", im Moment nur \end{document} */

technical_trailer_th(Stream) :-
	technical_trailer(Stream).

technical_trailer(Stream) :-
	printf(Stream, "\n\\end{document}\n", []),
	!.

/* print_th_domain/2 leitet die Ausgabe einer Domain ein. */

print_th_domain(Stream, Domain, Status) :-
	write(Stream, "\\subsection*{Domain "),
	term2string(Domain, DomainS),
	no_underscore(DomainS, DomainS1),
	write(Stream, DomainS1),
	once((
		Status  == []
		;
		write(Stream, " is "),
		write(Stream, Status)
	)),
	write(Stream, "}\n\n\\mbox{}\n\n"),
	!.

/* print_th_axiom/3 gibt ein Axiom innerhalb einer Theorie aus. */

print_th_axiom(Stream, Name, Axiom) :-
	show_fla(Axiom, AxiomS1),
	firstup(AxiomS1, AxiomS2),
	append_punct(AxiomS2, ".", AxiomS),
	printf(Stream, "\n%w\n", [AxiomS]),
	printf(Stream, "\n\\verb|%w|\n\\vskip1ex\n", [Name]),
	!.

/* print_theorem_String/4 gibt eine (bereits in einen String umgewandelte
   Formel) in einer bestimmten (theorem-)Umgebung aus. Bevor eine Umgebung 
   das erste Mal verwendet wird, wird \newtheorem aufgerufen.
   Ist das letzte Argument (Name des Axioms) ein [], wird kein Name
   ausgegeben und eine Referenz gesetzt, um spaeter auf dieses Axiom
   verweisen zu koennen. */

print_theorem_string(Stream, Env, String, Handle, Name) :-
	check_env(Stream, Env),
	get_name_or_ref(Handle, Name, NameOrRef),
	firstup(String, String1),
	printf(Stream, "\\begin{%Dw}%w\n%w\n\\end{%Dw}\n", 
			[Env, NameOrRef, String1, Env]),
	!.

get_name_or_ref(Handle, AxName, NameOrRef) :-
	(AxName = [] ->
		Name1 = ""
		;
		apply_texop(AxName, Name1)
	),
	(Name1 = "" ->
		sprintf(NameOrRef, "\\label{%w}", [Handle])
		;
		firstup(Name1, Name),
		concat_string(["[{", Name, "}]"], NameOrRef)
	).

check_env(_, Env) :-
	env(Env),
	!.
check_env(Stream, Env) :-
	apply_texop0(Env, EnvS),
	printf(Stream, "\\expandafter\\ifx\\csname %Dw\\endcsname\\relax%%\n",
			[Env]),
	printf(Stream, "\\newtheorem{%Dw}{%w}[section]\\fi\n", [Env, EnvS]),
	assert(env(Env)).

print_text0(_, _, "") :-
	!.
print_text0(abstract, Stream, Text) :-
	!,
	write(Stream, "\\begin{abstract}\n"),
	write(Stream, Text),
	write(Stream, "\\end{abstract}\n").
print_text0(_, Stream, Text) :-
	write(Stream, Text),
	write(Stream, "\n\n").

/* Ausgabe der reservierten Variablen */

print_var_types(_, []) :- !.
print_var_types(Stream, List) :-
	printf(Stream, "We denote variables for\n\\begin{itemize}\n", []),
	print_var_types_list(Stream, List),
	printf(Stream, "\\end{itemize}\n", []).

print_var_types_list(Stream, [[Type,Vars]|TypeList]) :- 
	printf(Stream, "\\item %w by ", [Type]),
	print_var_list(Stream, Vars),
	write(Stream, "\n"), 
	print_var_types_list(Stream, TypeList).
print_var_types_list(_, []).

print_var_list(Stream, [Var]) :-
        make_varlist(Var, VarListS),
        write(Stream, VarListS).
print_var_list(Stream, [Var1, Var2]) :-
        make_varlist(Var1, Var1ListS),
        make_varlist(Var2, Var2ListS),
        printf(Stream, "%w and %w", [Var1ListS, Var2ListS]).
print_var_list(Stream, [Var1, Var2, Var3]) :-
        make_varlist(Var1, Var1ListS),
        make_varlist(Var2, Var2ListS),
        make_varlist(Var3, Var3ListS),
        printf(Stream, "%w, %w, and %w", [Var1ListS, Var2ListS, Var3ListS]).
print_var_list(Stream, [Var|Vars]) :-
        make_varlist(Var, VarListS),
        printf(Stream, "%w,\n", [VarListS]),
        print_var_list(Stream, Vars).

make_varlist(Var, String) :-
        make_varname(Var, [], VarS_),
        make_varname(Var, 1,  VarS1),
        make_varname(Var, 2,  VarS2),
        sprintf(String, "$%w, %w, %w, \\ldots$", [VarS_, VarS1, VarS2]).

/* Ausgabe der bekannten Theorien. */

print_known_theory(_, []) :- !.
print_known_theory(Stream, KnownTheories) :-
	(length(KnownTheories, 1) -> S="" ; S="s"),
	printf(Stream,"We assume that the reader is acquainted with the following domain%w:\n", [S]),
	printf(Stream, "\\begin{itemize}\n", []),
	print_known_theory_list(Stream, KnownTheories),
	printf(Stream, "\\end{itemize}\n\n", []),
	printf(Stream, "Moreover we assume:\n\n", []).

print_known_theory_list(Stream, [Theory|List]) :-
	get_theory_name(Theory, Name),
	first_ascii_up(Name, UpCaseName),
	printf(Stream, "\\item %w.\n", [UpCaseName]),
	print_known_theory_list(Stream, List).
print_known_theory_list(_, []).

first_ascii_up(S1,S2) :- string_list(S1,[E1|L]),97 < E1,E1 < 123,
	E2 is E1-32,
	string_list(S2,[E2|L]),!.
first_ascii_up(S,S).

get_theory_name(Theory, Name) :-
	th_title(Theory, Name),
	!.

th_title(Theory,Name) :- call(safe_transaction(
	retrieve_clause(domain(Theory,title,Name))),thman),!.
th_title(T,Name) :- show_fla(T,TS,latex),concat_string(["$ ",TS," $"],Name),!.

/* Der Beweisanfang ist gleichbedeutend mit dem Beginn einer proof-Umgebung.
   Der Parameter der Proof-Umgebung wird als Fussnote angegeben, das ist
   als Moeglichkeit gedacht, die verwendeten Systeme anzugeben. */

print_proof_begin(Stream) :-
	apply_texop(ilf, IlfS),
	printf(Stream, "\n\\begin{ilfproof}{%w} ", [IlfS]). 	

print_proof_begin(Stream, Systems) :-
	sprintf_systems(SystemsS, Systems),
	printf(Stream, "\n\\begin{ilfproof}{%w} ", [SystemsS]). 	

sprintf_systems(SystemsS, Systems) :-
	sprintf_systems(Systems, "", SystemsS),
	!.
	
sprintf_systems([System1, System2, System3], S, SS) :-
	apply_texop(System1, System1S),
	apply_texop(System2, System2S),
	apply_texop(System3, System3S),
	concat_string([S, System1S, ", ", System2S, ", and ", System3S], SS).
sprintf_systems([System1, System2], S, SS) :-
	apply_texop(System1, System1S),
	apply_texop(System2, System2S),
	concat_string([S, System1S, " and ", System2S], SS).
sprintf_systems([System1], S, SS) :-
	apply_texop(System1, System1S),
	concat_string([S, System1S], SS).
sprintf_systems([System|Systems], S, SS) :-
	apply_texop0(System, SystemS),
	sprintf_systems(Systems, SystemsS),
	concat_string([S, SystemS, ", ", SystemsS], SS).

/* qed. wird durch die Umgebung proof geschrieben */

print_qed(Stream) :-
	printf(Stream, "\n\n\\end{ilfproof}\n", []). 	

/* print_we/1,2 schreibt "We" ggf. mit den als Argument uebergebenenen
   Systemen als Fussnote */

print_we(Stream) :- printf(Stream, "We ", []).

print_we(Stream, Systems) :-
	sprintf_systems(SystemsS, Systems),
	printf(Stream, "We\\footnote{%w} ", [SystemsS]).

/* Durch print_constants/2,3 werden die "konstanten Variablen" ("beliebig,
   aber fest") ausgegeben. */

print_constants(Stream, [Const]) :-
	show_fla0(Const, ConstS),
	printf(Stream, "Let $ %w $ be an arbitrary element.\n", [ConstS]).
print_constants(Stream, ConstList) :-
	show_fla0_list(ConstList, ", ", ConstListS),
	printf(Stream, "Let $ %w $ be arbitrary elements.\n", [ConstListS]).

print_constants(Stream, Type, [Const]) :-
	show_type(Type, TypeS),
	show_fla0(Const, ConstS),
	printf(Stream, "Let $ %w $ be an arbitrary element from %w.\n",
		       [ConstS, TypeS]).
print_constants(Stream, Type, ConstList) :-
	show_type(Type, TypeS),
	show_fla0_list(ConstList, ", ", ConstListS),
	printf(Stream, "Let $ %w $ be arbitrary elements from %w.\n",
		       [ConstListS, TypeS]).


/* firstup/2 ersetzt das erste Zeichen c nach " ", "$", "\mbox{" oder
   "\ilftext{" durch \ilfUpCase{c}, wenn c ein Kleinbuchstabe ist. 
   Dadurch wird c in den entsprechenden Grossbuchstabe umgewandelt, wenn 
   c nicht im mathematischen Modus ausgegeben wird. */

firstup(OldString, NewString) :- 
	string_list(OldString, OldList),
	once(firstup_list(OldList, NewList)), 
	string_list(NewString, NewList).

firstup_list([0'$|OldList], [0'$|NewList]) :- 
	firstup_list(OldList, NewList).
firstup_list([0' |OldList], [0' |NewList]) :- 
	firstup_list(OldList, NewList).
firstup_list([0'\, 0'm, 0'b, 0'o, 0'x, 0'{|OldList], 
	     [0'\, 0'm, 0'b, 0'o, 0'x, 0'{|NewList]) :- 
	firstup_list(OldList, NewList).
firstup_list([0'\, 0'i, 0'l, 0'f, 0't, 0'e, 0'x, 0't, 0'{|OldList], 
	     [0'\, 0'i, 0'l, 0'f, 0't, 0'e, 0'x, 0't, 0'{|NewList]) :- 
	firstup_list(OldList, NewList).
firstup_list([First|List], 
	     [0'\,0'i,0'l,0'f,0'U,0'p,0'C,0'a,0's,0'e,0'{,First,0'}|List]) :- 
	0'a =< First, First =< 0'z.
firstup_list(List, List).

/* Ausgabe einer Formel mit Satzzeichen ohne Label (d.h. im laufenden Text), 
   ggf. mit erstem Buchstaben gross geschrieben. */

print_formula(Stream, Formula, Firstup, Punct) :-
	show_fla0(Formula, String1),
	(Firstup==on -> firstup(String1, String2) ; String2=String1),
	append_punct(String2, Punct, String),
	concat_string(["$ ", String, " $"], MathString),
	write(Stream, MathString),
	!.

/* Ausgabe einer Formel, wobei die Entscheidung, ob ein Label zu setzen ist,
   erst im Postprocessing getroffen wird. */

print_formula(Stream, Formula, Firstup, Punct, Label) :-
	show_fla0(Formula, String1),
	(
		String1 = ""
		;
		printf(Stream, "\nilf_formula %Dw\n", [Label]),
		(Firstup==on -> firstup(String1, String2) ; String2=String1),
		append_punct(String2, Punct, String),
		write(Stream, String),
		write(Stream, "\nilf_formula_end\n")
	),
	!.

/* Anhaengen einer Interpunktion. In Ermangelung eines besseren Algorithmus
   setzen wir das Interpunktionszeichen vor das letzte "\\end{...}" in
   der Formel. */

append_punct(Formula, Punct, Formula1) :-
	string_length(Formula, LFormula),
	substring(Formula, Pos, 5, "\\end{"),
	L is LFormula-Pos-4,
	PosEnd is Pos+5, 
	substring(Formula, PosEnd, L, End),
	not substring(End, "\\end{", _),
	LStart is Pos-1,
	substring(Formula, 1, LStart, Start),
	concat_string([Start, Punct, "\\end{", End], Formula1),
	!.
append_punct(Formula, Punct, Formula1) :-
	concat_string([Formula, Punct], Formula1).

/* Ausgabe einer Referenz mit einem Wort (Axiom, Lemma ...) davor oder
   in Klammern */

print_ref(Stream, [], Ref, _) :-
	printf(Stream, "(\\ref{%Dw})", [Ref]).
print_ref(Stream, Type, Ref, Firstup) :-
	apply_texop0(Type, TypeS1),
	(Firstup==on -> firstup(TypeS1, TypeS) ; TypeS=TypeS1),
	printf(Stream, "%w \\ref{%Dw}", [TypeS, Ref]).

print_ref(Stream, Ref, Firstup) :-
	(Firstup==on ->
		printf(Stream, "\nilf_ref_firstup %Dw\n", [Ref])
		;
		printf(Stream, "\nilf_ref %Dw\n", [Ref])
	).

math("$ ", " $").

/* Da "_" fuer LaTeX eine besondere Bedeutung hat, muss er in Atomen mittels
   Backslash maskiert werden. Das gleiche trifft auf $ zu. */

no_underscore(X,Y) :- 
	quote("_", X, X1),
	quote("$", X1, Y),
	!.

quote(Char, X, Y) :-
	substring(X, Char, Pos),
	Len1 is Pos-1,
	Pos2 is Pos+1,
	Len2 is string_length(X)-Pos,
	substring(X, 1, Len1, X1),
	substring(X, Pos2, Len2, X2),
	quote(Char, X2, XX2),
	concat_string([X1, "\\", Char,  XX2], Y),
	!.
quote(_, X, X).
	 
text(String, Text) :-
	concat_string(["\\ilftext{", String, "}"], Text).

make_varname(BaseName/Index, VarNumber, VarName) :-
	!,
	no_underscore(BaseName, BaseName1),
	supersub(BaseName1, Index, VarNumber, VarName).
make_varname(BaseName, VarNumber, VarName) :-
	no_underscore(BaseName, BaseName1),
	supersub(BaseName1, [], VarNumber, VarName).

supersub(BaseName, [], [], BaseName) :- !.
supersub(BaseName, [], Sub, VarName) :- 
	!,
	concat_string([BaseName, "_{", Sub, "}"], VarName).
supersub(BaseName, Super, [], VarName) :- 
	!,
	concat_string([BaseName, "^{", Super, "}"], VarName).
supersub(BaseName, Super, Sub, VarName) :- 
	concat_string([BaseName, "^{", Super, "}_{", Sub, "}"], VarName).

/* Dictionary der vorhandenen texop */

dict :-
	get_uih_file("tmp/.dict", DictFile),
	open_file(DictFile, Stream),
	technical_header_th(Stream),
	title(Stream, "Dictionary of Current Symbols", ""),
	ini_varnames,
	p_dict(Stream),
	technical_trailer_th(Stream),
	close(Stream),
	postprocess_file(DictFile),
	!,
	make_th_viewable(DictFile),
	view_file(DictFile),
	!.

p_dict(Stream) :-
	try_texop(Asso, _, What:-_),
	clear_varnumbers,
	once(p_symb(Stream, Asso, What)),
	fail.
p_dict(_).


p_symb(Stream, rule, What) :-
	set_vars_to_(What),
	printf(Stream, "\\verb%% %w %%\\hfill{\\sc Rule}\\\\\n", [What]).
p_symb(Stream, op, What) :- 
	What1=..[What,X,Y,Z],
	p_symb(Stream, none(X,Y,Z /* um Warnungen zum vermeiden */), What1).
p_symb(Stream, Asso, What) :- 
	member(Asso,[xfx,xfy,yfx,yfy]),
	What1=..[What,X,Y],
	p_symb(Stream, none(X,Y /* um Warnungen zum vermeiden */), What1).
p_symb(Stream, Asso, What) :- 
	member(Asso,[fx,xf,yf,fy]),
	What1=..[What,X],
	p_symb(Stream, none(X /* um Warnungen zum vermeiden */), What1).
p_symb(Stream, _, What) :- 
	show_fla0(What, FlaString),
	set_vars_to_(What),
	(check_symb(FlaString) ->
		printf(Stream, "\\verb%% %w %%\\dotfill $ %w $\\\\\n", 
	               [What, FlaString])
		;
		printf(Stream, "\\verb%% %w %%\\\\\n", [What])
	).

check_symb(S) :- 
	substring(S, "&", Pos), 
	Pos1 is Pos-1,
	not substring(S, "\\", Pos1),
	!, fail.
check_symb(_).


set_vars_to_(What) :-
	term_variables(What, Vars),
	set_vars_to_(What, Vars).

set_vars_to_(_, []).
set_vars_to_(What, [Var|Vars]) :-
	get_var_info(Var, name, _),
	set_vars_to_(What, Vars).
set_vars_to_(What, ['_'|Vars]) :-
	set_vars_to_(What, Vars).

/* Initialisierung. Hier werden Lock-Files des DVI-Viewers weggeraeumt.
   Das sollte wahrscheinlich eher in proofout/thout passieren, die
   Filenamen sollten ueber die entsprechenden ilf_states abgefragt
   werden und der (externe) Viewer sollte das tun (aufgefordert dazu 
   durch eine spezielle Option). Da dieser Code also sowieso nicht fuer
   die Ewigkeit gemacht ist, benutzen wir auch einen direkten Aufruf aus
   parasys statt eines imports. */

:-
	get_uih_file("tmp/.th.dvi.tst", Th),
	call(rm_if_exists(Th), parasys),
	get_uih_file("tmp/.proof.dvi.tst", Proof),
	call(rm_if_exists(Proof), parasys).
