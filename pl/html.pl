/*
 * @(#)html.pl	1.21 (7/16/98)
 *
 * Ausgabe von Formeln und Beweise als HTML.
 *
 */

:- module_interface(html).

:- begin_module(html).

:- import
	apply_texop/2,
	apply_texop0/2,
	apply_texop0_list/3,
	find_file/3,
	show_item/3,
	show_fla/2,
	show_fla0/2,
	show_fla0_list/3,
	show_type/2
		from outtools.
	
:- dynamic
	current/2,
	ref/2.

file_extension(".html").

/* Nachbearbeitung: Aufloesen der Vorwaertsreferenzen.  */

write_ref_file(LabelList, RefList, RefFileName) :-
	open(RefFileName, write, RefStream),
	write_ll(RefStream, LabelList),
	writeln(RefStream, ""),
	write_rl(RefStream, LabelList),
	write_rl(RefStream, RefList),
	close(RefStream),
	!.
 
write_ll(_, []).
write_ll(RefStream, [Label|LabelList]) :-
	new([], Nr),
	assert(ref(Label, Nr)),
	printf(RefStream, "%Dw\n%d\n", [Label, Nr]),
	write_ll(RefStream, LabelList).
 
write_rl(_, []).
write_rl(Stream, [Ref-Type-Name|RefList]) :-
	ref(Ref, Nr),
	printf(Stream, "%Dw\n", [Ref]),
	(Name = [] ->
		NameS = ""
		;
		apply_texop(Name, NameS)
	),
	(NameS = "" ->
		apply_texop0(Type, TypeS),
		printf(Stream, "<A HREF=\"#%Dw\">%w %w</A>\n", [Ref,TypeS,Nr]),
		string_firstup(TypeS, TypeS1),
		printf(Stream, "<A HREF=\"#%Dw\">%w %w</A>\n", [Ref,TypeS1,Nr])
		;
		printf(Stream, "<A HREF=\"#%Dw\">%w</A>\n", [Ref, NameS]),
		firstup(NameS, NameS1),
		printf(Stream, "<A HREF=\"#%Dw\">%w</A>\n", [Ref, NameS1])
	),
	write_rl(Stream, RefList).
write_rl(Stream, [Ref|RefList]) :-
	ref(Ref, Nr),
	printf(Stream, "%Dw\n", [Ref]),
	printf(Stream, "<A HREF=\"#%Dw\">(%w)</A>\n", [Ref, Nr]),
	printf(Stream, "<A HREF=\"#%Dw\">(%w)</A>\n", [Ref, Nr]),
	write_rl(Stream, RefList).
write_rl(Stream, [Ref|RefList]) :- /* sollte nicht passieren */
	ilf_error("error in write_rl(%Dw)", [Ref]),
	write_rl(Stream, RefList).

view(FileName) :-
	find_file(FileName, ".html", Path),
	concat_string(["file:", Path, ".html"], URL),
	once(ilf_state(html_viewer, Viewer) ; Viewer="view_html"),
	(ilf_state(debug, on) ->
		concat_string([Viewer, " -d ", URL], ViewCmd)
		;
		concat_string([Viewer, " ", URL], ViewCmd)
	),
	sh(ViewCmd).
view(FileName) :-
	ilf_error("File %w[.html] not found.", [FileName]),
        !,
        fail.

technical_header(Stream) :-
	write(Stream, "<HTML>\n<HEAD>\n<TITLE>Ilf</TITLE>\n</HEAD>\n"),
	write(Stream, "<BODY BGCOLOR=#ffffff>\n").
technical_trailer(Stream) :- 
	write(Stream, "\n</BODY>\n</HTML>\n").

clearall :-
	retract_all(current(_,_)),
	retract_all(ref(_,_)).
	
/* title/3 gibt Titel und Author aus. */

title(Stream, Title, Author) :-
	show_item(title, Title, TitleS),
	show_item(author, Author, AuthorS),
	printf(Stream, "<H1>%w</H1>\n", [TitleS]),
	printf(Stream, "<STRONG>%w</STRONG><p>\n", [AuthorS]).

/* print_var_types/2 gibt die Zuordnung Type <-> Variablenname aus */

print_var_types(_, []) :- !.
print_var_types(Stream, List) :-
	write(Stream, "We denote variables for\n<UL>\n"),
	print_var_types_list(Stream, List),
	write(Stream, "</UL>\n"),
	!.

print_var_types_list(_, []).
print_var_types_list(Stream, [[Type, Vars]|L]) :-
	printf(Stream, "<LI> %w by ", [Type]),
	print_var_list(Stream, Vars),
	write(Stream, "\n"),
	print_var_types_list(Stream, L).

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
	printf(Stream, "%w, ", [VarListS]),
	print_var_list(Stream, Vars).

make_varlist(Var, String) :-
	make_varname(Var, [], VarS_),
	make_varname(Var, 1,  VarS1),
	make_varname(Var, 2,  VarS2),
	sprintf(String, "<I>%w, %w, %w, ...</I>", [VarS_, VarS1, VarS2]).

print_th_domain(Stream, Domain, []) :-
	printf(Stream, "<H3>Domain %Dw</H3>\n", [Domain]),
	!.
print_th_domain(Stream, Domain, Status) :-
	printf(Stream, "<H3>Domain %Dw (this domain is %Dw)</H3>\n", 
		       [Domain, Status]),
	!.

print_th_axiom(Stream, Name, Axiom) :-
	show_fla(Axiom, AxiomS1),
	firstup(AxiomS1, AxiomS2),
	append_punct(AxiomS2, ".", AxiomS),
	printf(Stream, "<I>%w</I><BR>\n", [AxiomS]),
	printf(Stream, "<PRE>%Dw.</PRE><P>\n", [Name]),
	!.

/* print_theorem/5 gibt eine Formel in einer Umgebung (aehnlich den
   theorem-Umgebungen von Latex) aus.
   Ist das dritte Argument (Name des Axioms) ein [], wird kein Name
   ausgegeben. ref/3 wird (u.a.) der Zusammenhang 
   	Nummer des Axioms <-> Handle
   verwendet. */

print_theorem_string(Stream, Env, String, Handle, Name) :-
	new(Env, Nr),
	assert(ref(Handle, Nr)),
	apply_texop0(Env, EnvS1),
	string_firstup(EnvS1, EnvS),
	(Name=[] ->
		NameS1=""
		;
		apply_texop(Name, NameS1)
	),
	(NameS1="" ->
		NameS=""
		;
		firstup(NameS1, NameS2),
		concat_string([" (", NameS2, ")"], NameS)
	),
	printf(Stream, "<H4><A NAME=\"%Dw\">%w %d%w.</A></H4>\n",
			[Handle, EnvS, Nr, NameS]),
	string_firstup(String, String1),
	printf(Stream, "<BLOCKQUOTE>%w</BLOCKQUOTE>\n", [String1]),
	!.
	
print_known_theory(Stream, KnownTheories) :-
	(length(KnownTheories, 1) -> S="" ; S="s"),
	printf(Stream, "We assume that the reader is acquainted with the following domain%w:\n", [S]),
	print_known_theory_list(Stream, KnownTheories),
	write(Stream, "Moreover we assume:\n\n").

print_known_theory_list(Stream, [Theory|List]) :-
	printf(Stream, "- %w\n", [Theory]),
	print_known_theory_list(Stream, List).
print_known_theory_list(_, []).

print_proof_begin(Stream) :- 
	write(Stream, "<STRONG>Proof</STRONG>.\n").

print_proof_begin(Stream, Systems) :- 
	apply_texop0_list(Systems, ", ", SystemsS),
	printf(Stream, "<STRONG>Proof</STRONG>(<I>%w</I>).\n", [SystemsS]).

print_qed(Stream) :-
	write(Stream, "\
<TABLE><TR><TD WIDTH=500></TD><TD ALIGN=RIGHT>q.e.d.</TD></TR></TABLE>\n").

print_we(Stream) :-
	write(Stream, "We ").

print_we(Stream, Systems) :-
	write(Stream, "We ("),
	print_list(Stream, Systems),
	write(Stream, ") ").

print_constants(Stream, [Const]) :-
	printf(Stream, "Let %w be an arbitrary element.\n", [Const]).
print_constants(Stream, ConstList) :-
	write(Stream, "Let "),
	print_list(Stream, ConstList),
	write(Stream, "be arbitrary elements.\n").

print_constants(Stream, Type, [Const]) :-
	printf(Stream, "Let %w be an arbitrary element from %w.\n", 
			[Const, Type]).
print_constants(Stream, Type, ConstList) :-
	write(Stream, "Let "),
	print_list(Stream, ConstList),
	printf(Stream, "be arbitrary elements from %w.\n", [Type]).

print_formula(Stream, Formula, Firstup, Punct) :-
	show_fla0(Formula, String1),
	(Firstup==on -> firstup(String1, String2) ; String2=String1),
	append_punct(String2, Punct, String),
	write(Stream, "<I>"),
	write(Stream, String),
	write(Stream, "</I>").

print_formula(Stream, Formula, Firstup, Punct, Label) :-
	printf(Stream, "\nilf_formula %Dw\n", [Label]),
	show_fla0(Formula, String1),
	(Firstup==on -> firstup(String1, String2) ; String2=String1),
	append_punct(String2, Punct, String),
	write(Stream, "<I>"),
	write(Stream, String),
	write(Stream, "</I>"),
	write(Stream, "\nilf_formula_end\n").

/* Anhaengen einer Interpunktion.
   Die Interpunktion wird hinter das letzte "echte" "Zeichen" gesetzt.
   "Zeichen" sind alle Characters ausser ">" und HTML-Tags.
   "Echt" sind alle Character ausser " ", "\t", "n".
   "Echt" sind die HTML-Tags, fuer die es eine Klausel punct_tag/2 gibt. */

append_punct(Formula, Punct, Formula1) :-
	Pos is string_length(Formula),
	append_punct(Formula, Punct, Formula1, Pos).

append_punct(Formula, Punct, Formula1, 0) :-
	!,
	concat_string([Punct, Formula], Formula1).
append_punct(Formula, Punct, FormulaPunct, Pos) :-
	substring(Formula, Pos, 1, Last),
	append_punct(Formula, Punct, FormulaPunct, Pos, Last).

append_punct(Formula, Punct, FormulaPunct, Pos, ">") :-
	!,
	Pos1 is Pos-1,
	tag_start(Formula, TagStart, Pos1),
	(punct_tag(Formula, TagStart) ->
		do_append_punct(Formula, Punct, FormulaPunct, Pos)
		;
		TagStart1 is TagStart-1,
		append_punct(Formula, Punct, FormulaPunct, TagStart1)
	).
append_punct(Formula, Punct, FormulaPunct, Pos, " ") :-
	!,
	Pos1 is Pos-1,
	append_punct(Formula, Punct, FormulaPunct, Pos1).
append_punct(Formula, Punct, FormulaPunct, Pos, "\n") :-
	!,
	Pos1 is Pos-1,
	append_punct(Formula, Punct, FormulaPunct, Pos1).
append_punct(Formula, Punct, FormulaPunct, Pos, "\t") :-
	!,
	Pos1 is Pos-1,
	append_punct(Formula, Punct, FormulaPunct, Pos1).
append_punct(Formula, Punct, FormulaPunct, Pos, _) :-
	do_append_punct(Formula, Punct, FormulaPunct, Pos).

do_append_punct(Formula, Punct, FormulaPunct, Pos) :-
	string_length(Formula, Len),
	Pos2 is Pos+1,
	Len2 is Len-Pos,
	substring(Formula, 1, Pos, Formula1),
	substring(Formula, Pos2, Len2, Formula2),
	concat_string([Formula1, Punct, Formula2], FormulaPunct).

tag_start(_, 1, 0) :-
	!.
tag_start(Formula, TagStart, Pos) :-
	substring(Formula, Pos, 1, Last),
	Pos1 is Pos-1,
	(Last=="<" ->
		TagStart=Pos
		;
		(Last=="\"" ->
			skip_quote(Formula, TagStart, Pos1)
			;
			tag_start(Formula, TagStart, Pos1)
		)
	).
		
skip_quote(_, 1, 0) :-
	!.
skip_quote(Formula, TagStart, Pos) :-
	substring(Formula, Pos, 1, Last),
	Pos1 is Pos-1,
	(Last=="\"" ->
		tag_start(Formula, TagStart, Pos1)
		;
		skip_quote(Formula, TagStart, Pos1)
	).

punct_tag(Formula, TagStart) :-
	substring(Formula, TagStart, 4, Img),
	tag_compare(Img, "<IMG"),
	!.
punct_tag(Formula, TagStart) :-
	substring(Formula, TagStart, 5, Img),
	tag_compare(Img, "</SUB"),
	!.
punct_tag(Formula, TagStart) :-
	substring(Formula, TagStart, 5, Img),
	tag_compare(Img, "</SUP"),
	!.

tag_compare(Tag0, Tag1) :-
	name(Tag0, List0),
	name(Tag1, List1),
	taglist_compare(List0, List1).

taglist_compare(_, []) :- 
	!.
taglist_compare([Char|List0], [Char|List1]) :- 
	!, 
	taglist_compare(List0, List1).
taglist_compare([Char0|List0], [Char1|List1]) :- 
	Char0 >= 0'a,
	Char0 =< 0'z,
	Char0 is Char1+32, 
	!, 
	taglist_compare(List0, List1).

print_string_italic(Stream, String) :-
	write(Stream, "<I>"),
	write(Stream, String),
	write(Stream, "</I>").

print_string_footnote(Stream, String, Footnote) :-
	write(Stream, String),
	write(Stream, "<SUP>"),
	write(Stream, Footnote),
	write(Stream, "</SUP>").

print_ref(Stream, [], Ref, _) :-
	print_ref(Stream, [], Ref).
print_ref(Stream, Type, Ref, Firstup) :-
	ref(Ref, Nr),
	apply_texop0(Type, TypeS1),
	(Firstup==on -> firstup(TypeS1, TypeS) ; TypeS=TypeS1),
	printf(Stream, "<A HREF=\"#%Dw\">%w %w</A>", [Ref, TypeS, Nr]).

print_ref(Stream, Ref, Firstup) :-
	(Firstup==on ->
		printf(Stream, "\nilf_ref_firstup %Dw\n", [Ref])
		;
		printf(Stream, "\nilf_ref %Dw\n", [Ref])
	).

print_string_ref(Stream, String, Ref) :-
	printf(Stream, "<A HREF=\"#%Dw\">%w</A>", [Ref, String]).

end_par(Stream) :-
	write(Stream, "<P>\n\n").

math("<I>", "</I>").

text(String, Text) :-
	concat_string(["</I>", String, "<I>"], Text).

make_varname(BaseName/Index, VarNumber, VarName) :-
        !,
        supersub(BaseName, Index, VarNumber, VarName).
make_varname(BaseName, VarNumber, VarName) :-
        supersub(BaseName, [], VarNumber, VarName).

supersub(BaseName, [], [], BaseName) :- !.
supersub(BaseName, [], Sub, VarName) :-
        !,
	concat_string([BaseName, "<SUB>", Sub, "</SUB>"], VarName).
supersub(BaseName, Super, [], VarName) :-
        !,
	concat_string([BaseName, "<SUP>", Super, "</SUP>"], VarName).
supersub(BaseName, Super, Sub, VarName) :-
	concat_string(
		[BaseName, "<SUP>", Super, "</SUP>", "<SUB>", Sub, "</SUB>"], 
		VarName
	).
 
print_list(Stream, [X]) :-
	printf(Stream, "%w", [X]).
print_list(Stream, [X|R]) :-
	printf(Stream, "%w, ", [X]),
	print_list(Stream, R).

new(What, N1) :-
	retract(current(What, N)),
	N1 is N+1,
	assert(current(What, N1)).
new(What, 1) :-
	assert(current(What, 1)).

/*  firstup/2 ersetzt das erste Zeichen c nach " " oder HTML-Tags durch den
    entsprechenden Grossbuchstaben, wenn c ein Kleinbuchstabe und nicht
    im "mathematischen Mode" ist. Der "mathematische Mode" wird durch <I>
    betreten und mit </I> verlassen (keine Verschachtelung). 
    Bei firstup/2 ist der "mathematische Mode" am Anfang eingeschaltet, bei 
    string_firstup/2 nicht. 
    Die Argumente von firstup_list haben folgende Bedeutung:
    	3: "mathematischer Modus": 1=ja, 0=nein
    	4: innerhalb eines HTML-Tags: 1=ja, 0=nein
	5: innerhalb eines gequoteten Strings: 1=ja, 0=nein */

firstup(OldString, NewString) :-
	string_list(OldString, OldList),
	once(firstup_list(OldList, NewList, 1, 0, 0)),
	string_list(NewString, NewList).

string_firstup(OldString, NewString) :-
	string_list(OldString, OldList),
	once(firstup_list(OldList, NewList, 0, 0, 0)),
	string_list(NewString, NewList).

firstup_list([0' |OldList], [0' |NewList], Math, Tag, Quot) :-
	firstup_list(OldList, NewList, Math, Tag, Quot).
firstup_list([0'"|OldList], [0'"|NewList], Math, Tag, 0) :-
	firstup_list(OldList, NewList, Math, Tag, 1).
firstup_list([0'"|OldList], [0'"|NewList], Math, Tag, 1) :-
	firstup_list(OldList, NewList, Math, Tag, 0).
firstup_list([X|OldList], [X|NewList], Math, Tag, 1) :-
	firstup_list(OldList, NewList, Math, Tag, 1).
firstup_list([0'<, 0'I, 0'>|OldList], [0'<, 0'I, 0'>|NewList], _, 0, 0) :-
	firstup_list(OldList, NewList, 1, 0, 0).
firstup_list([0'<, 0'/, 0'I, 0'>|OldList], 
	     [0'<, 0'/, 0'I, 0'>|NewList], _, 0, 0) :-
	firstup_list(OldList, NewList, 0, 0, 0).
firstup_list([0'<|OldList], [0'<|NewList], Math, 0, 0) :-
	firstup_list(OldList, NewList, Math, 1, 0).
firstup_list([0'>|OldList], [0'>|NewList], Math, 1, 0) :-
	firstup_list(OldList, NewList, Math, 0, 0).
firstup_list([X|OldList], [X|NewList], Math, 1, 0) :-
	firstup_list(OldList, NewList, Math, 1, 0).
firstup_list([First|List], [FirstUp|List], 0, 0, 0) :-
	0'a =< First, First =< 0'z,
	FirstUp is First + 0'A - 0'a.
firstup_list(List, List, _, _, _).
