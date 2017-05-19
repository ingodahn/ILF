/*
 * @(#)thout.pl	1.18 (%G)
 *
 * Ausgabe von Theorien.
 *
 * basiert auf thman.pro 1.55 (11/15/95) 
 *         und thman.pl  1.39 checked in 07/03/96 (Author: Dahn)
 *
 * Portierung nach Eclipse-Prolog: Honigmann
 */

:- module(thout).

:- export
	axioms/0,
	axioms/1,
	save_axioms/1,
	save_axioms/2,
	show_axioms/0,
	show_axioms/1,
	view_axioms/0,
	view_axioms/1.

:- export
	th_out/1,
	th_out/2,
	th_out/3,
	th_out0/3.

/** Anfang Erweiterung von T.Baar */
?- export
	gen_input_file/2.
/** Ende Erweiterung von T.Baar */

:- begin_module(thout).
/*
:- import(database_kernel), lib(kb).
*/
:- import 
	mode_specific/2,
	print_text/3
		from genout.

:- dynamic
	axiom/2,
	axiom_printed/1,
	domain_retrieved/1,
	user_widens/2.

/** Anfang Erweiterung von T.Baar */
?- import
	get_attribute/2,
	get_axnameL/3,
	get_var_root/2
			from thman.
			
?- import
	get_right_item/4,
	getwrite_right_item/4
			from knowman.

:- dynamic
	ax_name/2,
	var_has_typeterm/2,
	sig/1.
			
/*  Ende Erweiterung von T.Baar */


/* Text-Darstellung einer Theorie: axioms/0,1 ohne,  show_axioms/0,1 mit 
   Anwendung der short_form */

axioms :-
	axioms(_).
axioms(AxList) :-
	ilf_state(default_th_file, FileName),
	( 
		ilf_state(short_form, Old, =) 
		; 
		Old = [], make_ilf_state(short_form, =)
	),
	th_out(FileName, text, AxList),
	(Old == [] ->
		remove_ilf_state(short_form)
		;
		ilf_state(short_form, _, Old)
	),
	mode_specific(view(FileName), text),
	!.

show_axioms :-
	show_axioms(_).
show_axioms(AxList) :-
	ilf_state(default_th_file, FileName),
	th_out(FileName, text, AxList),
	mode_specific(view(FileName), text).
	
/* LATEX-Darstellung der Theorie */

view_axioms :-
	view_axioms(_).
view_axioms(AxList) :-
	ilf_state(default_th_file, FileName),
	once((ilf_state(out_mode, Mode) ; Mode=latex)),
	th_out(FileName, Mode, AxList),
	mode_specific(view(FileName), Mode).
	

/* Ausfilen einer Theorie   */

save_axioms(FileName):-
        save_axioms(FileName, _).
save_axioms(FileName, AxList) :-
        th_out(FileName, th_ilf, AxList).

 



/* Ausgabe der Theorie in ein File in einem gegebenen Modus. 
   Der Modus muß dazu die Prädikate
   	open_file/2
	technical_header/1,
	technical_trailer/1,
   bereitstellen.  Die eigentliche Ausgabe der Axiome erfolgt in 
   	print_theory/3
   weiter unten. */

th_out(FileName) :-
	ilf_state(out_mode, Mode),
	th_out(FileName, Mode).
th_out(FileName, Mode) :-
	th_out(FileName, Mode, _).
th_out(FileName, Mode, AxList) :-
	mode_specific(open_file(FileName, Stream), Mode),
	mode_specific(technical_header(Stream), Mode),
	get_title(Title),
	get_author(Author),
	mode_specific(title(Stream, Title, Author), Mode),
	th_out0(Stream, Mode, AxList),
	mode_specific(technical_trailer(Stream), Mode),
	close(Stream),
	!.

th_out0(Stream, Mode, AxList) :-
	mode_specific(clearall, Mode),
	mode_specific(ini_varnames, Mode),
	mktemp("/tmp/.thout", TempFileName),
	open(TempFileName, write, TempStream),
	print_text(th_pre_text, TempStream, Mode), 
	mode_specific(
		open_include(TempStream, ".typevars", TypeVarStream), Mode),
	print_type_declarations(TempStream, Mode),
	mode_specific(print_var_types(TypeVarStream), Mode),
	close(TypeVarStream),
	mode_specific(hide_varnames, Mode),
	mode_specific(open_include(TempStream, ".vars", VarStream), Mode),
	print_predfunc_declarations(TempStream, Mode),
	print_text(th_declaration, TempStream, Mode), 
	print_theory(TempStream, Mode, AxList),
	close(TempStream),
	mode_specific(print_var_types(VarStream), Mode),
	close(VarStream),
	mode_specific(postprocess_file(TempFileName, PPPid, Output), Mode),
	repeat,
	(read_string(Output, "\n", _, Line) ->
	        writeln(Stream, Line),
	        fail
	        ;
	        true
	), !,
	close(Output),
	wait(PPPid, _),
	!.

get_title(Title) :-
	ilf_state(th_title, Title),
	!.
get_title("Axioms").

get_author(Author) :-
	ilf_state(th_author, Author),
	!.
get_author(Author) :-
	ilf_state(proof_author, Author),
	!.
get_author("The ILF Group").

print_type_declarations(_, _) :-
	retract_all(user_widens(_, _)),
	safe_transaction(( /* oder aus thman importieren */
		retrieve_clause(
			definition(_, user_widens(NewType, Definition))
		),
		call(assert(user_widens(Definition, NewType)), thout),
		fail
	)).
% naechsten Abschnitt veraendert T.Baar
%print_type_declarations(Stream, Mode) :-
%	user_widens(and(Attr, set), Type),
%	print_type_declarations(Stream, Mode, and(Attr, set), Type),
%	fail.
%print_type_declarations(_, _).
%
%print_type_declarations(Stream, Mode, Definition, Type) :-
%	once(mode_specific(
%		print_th_type_declaration(Stream, Definition, Type),
%		Mode
%	)),
%	user_widens(and(NewAttr, Type), NewType),
%	print_type_declarations(Stream, Mode, and(NewAttr, Type), NewType),
%	fail.
%print_type_declarations(_, _, _, _, _).

print_type_declarations(Stream, Mode) :-
	user_widens(Definition, Type),
	print_type_declarations(Stream, Mode, Definition, Type),
	fail.
print_type_declarations(_, _).

print_type_declarations(Stream, Mode, Definition, Type) :-
	once(mode_specific(
		print_th_type_declaration(Stream, Definition, Type),
		Mode
	)),
        !.
print_type_declarations(_, _, _, _, _).


print_predfunc_declarations(Stream, Mode) :-
	safe_transaction((
		retrieve_clause(definition(_, user_type(PredFunc, Type))),
		once(print_predfunc_declaration(Stream, Mode, PredFunc, Type)),
		fail
	)).
% ergaenzt T.Baar
print_predfunc_declarations(Stream, Mode) :-
	call(local_type(PredFunc, Type), thman),
	once(print_predfunc_declaration(Stream, Mode, PredFunc, Type)),
	fail.
print_predfunc_declarations(_, _).


% Sollten hier nicht auch die Operator-dekl. ausgegeben werden?? T.Baar

% Falls Type eine Var ist, handelt es sich um eine Funktion
print_predfunc_declaration(Stream, Mode, Func, and([], Var)):-
        var(Var),
        mode_specific(print_th_func_declaration(Stream, Func, and([], Var)), Mode),
        !.
print_predfunc_declaration(_, _, _, and([], type)).
print_predfunc_declaration(_, _, Pred, and([], wff)) :-
	Pred = (_{thman:and([], set)} = _{thman:and([],set)}).
print_predfunc_declaration(Stream, Mode, Pred, and([], wff)) :-
	!,
	mode_specific(print_th_pred_declaration(Stream, Pred), Mode).
print_predfunc_declaration(Stream, Mode, Func, Type) :- 
	mode_specific(print_th_func_declaration(Stream, Func, Type), Mode).

/* Ausgabe von Axiomen in einem gegebenen Modus. Die Liste der auszugebenden 
   Axiome besteht aus Termen Domain-AxName oder Domain. Beide Teile koennen 
   Variablen enthalten. Der Modus muß dazu die Prädikate
   	print_th_domain/3
   	print_th_axiom/3
   bereitstellen. */

print_theory(Stream, Mode, TemplateList) :-
	safe_transaction(
		setof(DomainInfo, get_domain_info(DomainInfo), Domains)
	),
	retract_all(axiom(_, _)),
	retract_all(axiom_printed(_)),
	retract_all(domain_retrieved(_)),
	print_theory_list(Stream, Mode, Domains, TemplateList).

get_domain_info(Domain-Title-Status) :-
	retrieve_clause(domain(Domain, title, Title)),
	once(retrieve_clause(domain(Domain, status, Status)) ; Status=[]).

print_theory_list(Stream, Mode, Domains, Var) :-
	var(Var),
	!,
	print_theory_list(Stream, Mode, Domains, [_]).
print_theory_list(Stream, Mode, Domains, [Var|_]) :-
	var(Var),
	!,
	print_domain_list(Stream, Mode, Domains, _-_).
print_theory_list(Stream, Mode, Domains, [Template|TemplateList]) :-
	!,
	print_domain_list(Stream, Mode, Domains, Template),
	print_theory_list(Stream, Mode, Domains, TemplateList).
print_theory_list(_, _, _, []).
	
print_domain_list(Stream, Mode, Domains, Template) :-
	functor(Template, -, 2),
	!,
	print_domain_list0(Stream, Mode, Domains, Template).
print_domain_list(Stream, Mode, Domains, Template) :-
	print_domain_list0(Stream, Mode, Domains, Template-_).

print_domain_list0(Stream, Mode, [Domain-Title-Status|_], Template) :-
	Domain-_ = Template,
	once(print_domain(Stream, Mode, Domain, Title, Status, Template)),
	fail.
print_domain_list0(Stream, Mode, [_|Domains], Template) :-
	!,
	print_domain_list0(Stream, Mode, Domains, Template).
print_domain_list0(_, _, [], _).

print_domain(Stream, Mode, Domain, Title, Status, AxName) :-
	retrieve_domain(Domain),
	bagof(AxName-Axiom, get_axiom(AxName, Axiom), AxList),
	mode_specific(print_th_domain(Stream, Domain, Title, Status), Mode),
	print_axiom_list(Stream, Mode, AxList).

retrieve_domain(Domain) :-
	domain_retrieved(Domain),
	!.
retrieve_domain(Domain) :-
	safe_transaction((
		retrieve_clause(formula(Domain, Name, fla, Axiom) :- Cond),
		once((call(Cond), assert(axiom(Domain-Name, Axiom)))),
		fail
	)).
retrieve_domain(Domain) :-
	assert(domain_retrieved(Domain)).

get_axiom(AxName, Axiom) :-
	axiom(AxName, Axiom),
	not(axiom_printed(AxName)).

print_axiom_list(Stream, Mode, [AxName-Axiom|AxList]) :-
	!,
	mode_specific(print_th_axiom(Stream, AxName, Axiom), Mode),
	assert(axiom_printed(AxName)),
	print_axiom_list(Stream, Mode, AxList).
print_axiom_list(_, _, []).

/******  Anfang Erweiterung von T.Baar  ********/

% gen_input_file/2 erhaelt	 
gen_input_file(File,AxNameL):-
	get_uih_file1(File,"/th/",".th",File1),
	open(File1,write,str1),
	gen_input_str(str1,AxNameL),
	close(str1).



% get_right_file1 soll als Basic auch absolute Filenamen zulassen, 
% Bezeichnungen mit und ohne Extensionen, Atoms und Strings und
% daraus AbsName bestimmen
% 
% Bis jetzt nur prototypisch wie in get_right_file implementiert

get_uih_file1(Basic,RelP,Ext,AbsName):-
	(atom(Basic), term_string(Basic,BasicS) ; BasicS = Basic),
	concat_string([RelP,BasicS,Ext],RelName),
	get_uih_file(RelName,AbsName).



gen_input_str(Str,AxNameL):-
	clear_module,
	getting_reservation,
%	prt_reservations,
	ass_genaxnamel(AxNameL),
%	get_symbols,
%	prt_declaration(Str),
	prt_flas(Str).
gen_input_str(_,_).
	

clear_module:-
	retract_all(ax_name(_,_)).
	
ass_genaxnamel([]):-!.
ass_genaxnamel([[Dom - Name]|T]):-
	(
	get_axnameL(Dom,Name,AxNameL) % Dom und Name koennen Variablen enthalte
	;
	 AxNameL = []
	) ,
	% gibt nur Namen zurueck, die in WB stehen, nicht in knowman T.Baar !!!
	ass_axnamel(AxNameL),
	ass_genaxnamel(T),
	!.
	
ass_genaxnamel([H|T]):-
	term_string(H,HS),
	ilf_error(["ass_genaxnamel: unexpected format in head of arglist ",HS]),
	ass_genaxnamel(T).
	
	
ass_axnamel([]):-!.
ass_axnamel([H|T]):-
	H=..[_,Dom,Name],
	assert(ax_name(Dom,Name)),
	ass_axnamel(T).	
	

get_symbols:-
	ax_name(Dom,Name),
	once(getwrite_right_item(Dom,Name,signature,[ SigL, [], [] ])),
	assert(sig(SigL)),
	fail.  
	
get_symbols.
	   
getting_reservation:-
	safe_transaction((
	retrieve_clause((reservation(V,T))),
	assert(var_has_typeterm(V,T)),
%	writeq(V),nl,
%	printf("  %mw",[V]),writeln("."),
%	printf("  %mw",[T]),writeln("."),
	fail)).
getting_reservation.


prt_reservations(Str):-
	setof(res(VarId,TypeT),var_has_typeterm(VarId,TypeT),ResL),
	sort_reserv(ResL,SortedResL),
	prt_sorted_reservations(Str,SortedResL).

prt_sorted_reservations(_,[]):-!.
prt_sorted_reservations(Str,[res(VarId,TypeT_as)|T]):-
	printf(Str,"   reserve  %w  for %w \n ",[VarId,TypeT_as]),
	prt_sorted_reservations(Str,T).
	

getting_decl:-
	call(user_type(Arg,Res),thman),	
	term_variables(Arg,VarL),
	VarL=[H|_],
	get_var_info(H,name,N),
	printf("  %mw",[VarL]),writeln("."),
	writeq(N),writeln("."),
	printf("  %mw",[Arg]),writeln("."),
	printf("  %mw",[Res]),writeln("."),
	fail.
	



	
prt_flas(Str):-
	ax_name(Dom,Name),
	write(Str,"fla "),write(Str,Name),write(Str," :\n"),
	once((
		get_right_item(Dom,Name,fla,Fla),
		prt_fla(Str,3,Fla),
		write(Str,".\n\n")
	    )),	
	fail.
prt_flas(_).


prt_fla(Str,D,all(X,Fla1)):-
	!,
	write_space(Str,D),
	check_reservation_of_var(X, X1),
	write(Str,"all("),write(Str,X1),write(Str,",(\n"),
	D1 is D + 1,
	prt_fla(Str,D1,Fla1),
	write(Str,"))").
	
prt_fla(Str,D,ex(X,Fla1)):-
	!,
	write_space(Str,D),
	check_reservation_of_var(X, X1),
	write(Str,"ex("),write(Str,X1),write(Str,",(\n"),
	D1 is D + 1,
	prt_fla(Str,D1,Fla1),
	write(Str,"))").
		
prt_fla(Str,D,','(Fla1,Fla2)):-
	!,
	prt_fla(Str,D,Fla1),
	write(Str,',\n'),
	prt_fla(Str,D,Fla2).
	
prt_fla(Str,D,';'(Fla1,Fla2)):-
	!,
	prt_fla(Str,D,Fla1),
	write(Str,';\n'),
	prt_fla(Str,D,Fla2).

prt_fla(Str,D,'->'(Fla1,Fla2)):-
	!,
	prt_fla(Str,D,Fla1),
	write(Str,"\n"),
	write_space(Str,D), write(Str,"->\n"),
	prt_fla(Str,D,Fla2).
	
prt_fla(Str,D,'<->'(Fla1,Fla2)):-
	!,
	prt_fla(Str,D,Fla1),
	write(Str,"\n"),
	write_space(Str,D), write(Str,"<->\n"),
	prt_fla(Str,D,Fla2).
		
prt_fla(Str,D,not(Fla)):-
	!,
	write_space(Str,D), write(Str,"not("),
	D1 is D + 4,
	prt_fla(Str,D1,Fla),
	write_space(Str,D), write(Str,"   )").
	
	
prt_fla(Str,D,AtomFla):-
	write_space(Str,D),
	printf(Str,"%Dw",AtomFla).	
	
% check_reservation_of_var/2 ueberprueft die Uebereinstimmung der 
% Variablenbenutzung mit den Reservierungen 

check_reservation_of_var(X, XCode):-
	var(X),
	(get_var_info(X,name,VarId)
	;
	 ilf_error(["check_reservation_of_var: variable in formula without name"])
	),
	get_attribute(X, TypTerm),
	get_var_root(VarId,BasicVarId),
	(
	 var_has_typeterm(BasicVarId, TypeTermReserv),
	 variant(TypTerm,TypeTermReserv), XCode = X
	 ;
	 TypTerm = and([],Typ),
	 XCode = (X as Typ)
	).
check_reservation_of_var(X,_):-
	ilf_error(["check_reservation_of_var: failed for Variable",X]),
	fail.	
	
write_space(_,0):-!.
write_space(Str,N):-
	write(Str," "), N1 is N - 1,
	write_space(Str,N1).
		


/****   Ende Erweiterung T. Baar   *******/
