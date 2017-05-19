/* File @(#)tools.pl	1.26 checked in 01/08/99
/* Author: Dahn
/*
/*  Hilfspraedikate 
*/

:- module(tools).


:- export
	coded_var/1,
	compile_with_failure/1,
	decode_vars/2,
	gensym/2,
	make_vars_coded/1,
	mktemp/2,
	rev/2,
	sprintf/3,
	strict_member/2,
	strict_remove/3,
	strict_remove_l/3,
	strict_union/3,
	substitute/5,
	term2string/2,
	term_string_wo_space/2,
	termcanonic2string/2,
	list_canonical/1,
	subterm/2.

:- export
	compile_pred/1,
	convert_tkS_list/2,
	convert_list_tkS/2,
	dialog/6,
	goal_selection/3,
	make_vars_atoms/2,
	make_dir/1,
	list_body/2,
	serv_list_body/2,
	body_list/2,
	serv_body_list/2,
	list_head/2,
	serv_list_head/2,
	head_list/2,
	serv_head_list/2,
	list_fmla/3,
	serv_list_fmla/3,
	sort_by_functor/4,
	list_seq/3,
	negate_l/2,
	serv_negate_l/2,
	remove_alls/2,
	prepare_dynamic/1,
	prepare_dynamic_l/1.
/* We don't need a GUI
?- import tk_dialog/6, tk_goal_selection/3 from tcltools.

:- dynamic
	tmp_tk_item/1.
*/

:- export (list_canonical/1,list_canonical/2).
list_canonical(X) :- current_module(M),list_canonical_body(X,M).
:- export (substitute/5,substitute/6).
substitute(X1,X2,X3,X4,X5) :- current_module(M),substitute(X1,X2,X3,X4,X5,M).
:- export (prepare_dynamic/1,prepare_dynamic/2).
prepare_dynamic(X) :- current_module(M),prepare_dynamic(X,M).
:- export (prepare_dynamic_l/1,prepare_dynamic_l/2).
prepare_dynamic_l(X) :- current_module(M),prepare_dynamic_l(X,M).
:- export (compile_pred/1,compile_pred/2).
compile_pred(X) :- current_module(M),compile_pred(X,M).
:- export (compile_with_failure/1, compile_with_failure_body/2).
compile_with_failure(X) :- current_module(M),compile_with_failure(X,M).

?- begin_module(tools).

strict_member(E,[H|_]) :- E==H,!.
strict_member(E,[_|L]) :- strict_member(E,L),!.

strict_union([E|L1],L2,L3) :- strict_member(E,L2),!,strict_union(L1,L2,L3).
strict_union([E|L1],L2,[E|L3]) :- strict_union(L1,L2,L3).
strict_union([],L,L).

strict_remove(X,[H|L],L1) :- H==X,!,strict_remove(X,L,L1),!.
strict_remove(X,[H|L],[H|L1]) :- strict_remove(X,L,L1).
strict_remove(_,[],[]).

strict_remove_l([E|L],L1,L2) :- strict_remove(E,L1,LL),
	strict_remove_l(L,LL,L2),!.
strict_remove_l([],L,L).

/*------------------------------------------*/
/* Neue Atome generieren                    */
/* gensym(Kunde,Kunde1)                     */
/*  ...                                     */
/* gensym(Kunde,Kunde25)                    */
/*------------------------------------------*/
?- mode gensym(+,-).

gensym(R,A) :- 
	get_num(R,N),
	number_string(N,NS),
        concat_strings(R,NS,S), 
	atom_string(A,S).

?- mode get_num(+,-).
?- dynamic(current_num/2).
get_num(R,N) :- 
	retract(current_num(R,N1)),
	!,
	N is N1+1,
	asserta(current_num(R,N)).
get_num(R,1) :- 
	asserta(current_num(R,1)).

/* Variablencodierung */

make_vars_coded(T) :- 
	var(T),
	!, 
	gensym("var",T).
make_vars_coded(T) :- 
	atomic(T),!.
make_vars_coded([H|T]) :- 
	!,
	make_vars_coded(H),
	make_vars_coded(T).
make_vars_coded(T) :- 
	T=..[_|L],
	!, 
	make_vars_coded(L).


decode_vars(C,T) :- 
	substitute(C,T,V,coded_var(V),_).

coded_var(X) :- 
	atom(X), 
	name(X,[118,97,114|_]),!.

/* substitute(T1,T2,TEST,FILTER,LISTE) konstruiert T2 aus T1 indem alle*/
/* Teilterme TEST, die FILTER erfuellen durch V' ersetzt werden, falls */
/* [TEST,V'] in LISTE vorkommt.                                      */
?- mode substitute(?,?,?,+,?).

substitute(T1,T2,Test,Filter,Liste,Module) :- 
        not(not((Test=T1,call(Filter,Module)))),
	member([T1,U],Liste), 
	!,
	T2=U.
substitute(T,T,_,_,_,_) :- 
	(var(T); atomic(T)),
	!.
substitute(T1,T2,Test,Filter,Liste,Module) :- 
	not(atomic(T1)), 
	T1=..[F|Arg],
        substitute_list(Arg,Argneu,Test,Filter,Liste,Module),
        T2=..[F|Argneu].

?- mode substitute_list(?,-,?,+,?).
substitute_list([],[],_,_,_,_) :- !.
substitute_list([A|L],[AN|LN],Test,Filter,Liste,Module) :-
        substitute(A,AN,Test,Filter,Liste,Module),
        substitute_list(L,LN,Test,Filter,Liste,Module).

% term2string wandelt Terme in Strings um und erhaelt dabei Variablennamen
% printf(S,"DOw",T) laesst tiefe Terme zu   
% 
% Wenn der Term eine Liste ist, dann druckt printf(S,"%DOw",Term) nur sein
% 1. Element (ohne Fehlermeldung uebrigens!) und deshalb muss
% dieser Fall abgefangen werden

term2string(Var, String):-
        var(Var),
        term2string_1(Var, String),
        !.
term2string(Liste, String):-
        length(Liste, _),
        term2string_1([Liste], String),
        !.
term2string(Term, String):-
        term2string_1(Term, String).

term2string_1(Term,String) :- open("",string,S),
	printf(S,"%DOw",Term),
	current_stream(String,_,S),
	close(S),!.

termcanonic2string(Term,String) :- open("",string,S),
	write_canonical(S,Term),
	current_stream(String,_,S),
	close(S),!.

% wandelt einen Term in einen String ohne Leerzeichen um
term_string_wo_space(Term,String):-
	term_string(Term,Str1),
	string_list(Str1,HelpL1),
	string_list(" ",[SpaceAscii]),
	subtract(HelpL1,[SpaceAscii],HelpL2),
	string_list(String,HelpL2),
	!.


list_canonical(Op/N,Mod) :- 
	functor(F,Op,N),
	call(F,Mod),
	write_canonical(F),
	write(".\n"),fail.
list_canonical(_,_).

/* sprintf/3 schreibt analog der gleichnamigen C-Funktion mittels printf/2 
   in eine Variable */

sprintf(String, Format, Args) :-
        open(_, string, Stream),
        printf(Stream, Format, Args),
        current_stream(String, _, Stream),
        close(Stream),
        !.

/* mktemp erzeugt aus dem uebergebenen Basisnamen und der PID einen
   eindeutigen Filenamen aehnlich der gleichnamigen C-Funktion */

mktemp(Template, Unique) :-
	get_flag(pid, Pid),
	concat_string([Template, ".", Pid], Unique).

/* make_vars_atoms/2 ersetzt im ersten Argument alle Variablen durch Atome
   die gleich dem Namen der Variablen sind. Im zweiten
   Argument wird eine Liste der eingesetzten Atome zurueckgegeben */

make_vars_atoms(Term,ConstList) :-
	term_variables(Term,TermVar),
	get_var_names(TermVar,ConstList),!.

get_var_names([X|V],[XN|VN]) :- get_var_info(X,name,XN),X=XN,
	get_var_names(V,VN),!.
get_var_names([],[]).


/* convert_list_tkS konvertiert Liste von Termen in einen String der keine 
 * Leerzeichen ausser den Termgrenzen hat 
 *
 * wird zur Aufbereitung fuer tk-Eingaben gebraucht  
 */   
convert_list_tkS([],""):-!.
convert_list_tkS([H|T],S):-
	convert_list_tkS(T,S1),
	term_string_wo_space(H, HS),
	concat_string([HS," ",S1],S).
convert_list_tkS(L,S):-
	ilf_error("convert_list_tkS(%w, %w): called with unexpected Parameters", [L,S]),!.
	
/* convert_tkS_list realisiert die Umkehrung  */
convert_tkS_list(String,List):-
	retract_all(tmp_tk_item(_)),
	open(String,string,Str),
	read_tk_str(Str),
	(setof(Item,tmp_tk_item(Item),List) ; List = []),
	retract_all(tmp_tk_item(_)),
	!.

read_tk_str(Str):-
	repeat, 
	(
	 at_eof(Str)
	; 
	 read_string(Str," ",_Lenght,ItemS),
	 not(ItemS = ""),
	 term_string(Item,ItemS),
	 assert(tmp_tk_item(Item)),
	 fail
	). 

/* Dynamische Praedikate manipulieren */
prepare_dynamic_l([P|PL],Module) :- prepare_dynamic(P,Module),prepare_dynamic_l(PL,Module),!.
prepare_dynamic_l([],_).

prepare_dynamic(P,Module) :- 
	once(call((
		current_predicate(P),
		get_flag(P,visibility,Vis),
		abolish(P),
		(
			Vis=global,
			global(P)
			;
			Vis=exported,
			export(P)
			;
			true
		)
	     ), Module)),
	fail.
prepare_dynamic(P,Module) :- call(dynamic(P),Module).

compile_pred(Op/N,Module) :- functor(F,Op,N),
	call((
		bagof((F :- B),clause((F :- B)),CL),
		abolish(Op/N),
		compile_term(CL)
	),Module),!.
compile_pred(_,_).


/* Umwandlung von Listen in Formeln; Variante mit serv_ benutzt translit */

list_body([C,D|L],(C,B)) :- list_body([D|L],B),!.
list_body([C],C) :- !.
list_body([],true).

serv_list_body([C,D|L],AndCB) :- translit(',',And),
	AndCB=..[And,C,B],
	serv_list_body([D|L],B),!.
serv_list_body([C],C) :- !.
serv_list_body([],True) :- translit(true,True),!.

body_list(X,[X]) :- var(X),!.
body_list((X,Y),L) :- !, body_list(X,LX),body_list(Y,LY),append(LX,LY,L),!.
body_list(X,[X]).

serv_body_list(F,[F]) :- var(F),!.
serv_body_list(F,FL) :- translit(',',And),
	F=..[And,F1,F2],!,
	serv_body_list(F1,F1L),serv_body_list(F2,F2L),
	append(F1L,F2L,FL),!.
serv_body_list(F,[F]).

list_head([C,D|L],(C;B)) :- list_head([D|L],B),!.
list_head([C],C) :- !.
list_head([],false).

serv_list_head([C,D|L],OrCB) :- 
	translit(';',Or),
	OrCB=..[Or,C,B],
	serv_list_head([D|L],B),!.
serv_list_head([C],C) :- !.
serv_list_head([],False) :- translit(false,False),!.

head_list(F,[F]) :- var(F),!.
head_list((F1;F2),FL) :- 
	!,
	head_list(F1,F1L),
	head_list(F2,F2L), 
	append(F1L,F2L,FL),
	!.
head_list(F,[F]).

serv_head_list(F,[F]).

serv_head_list(F,[F]) :- var(F),!.
serv_head_list(F,FL) :- translit(';',Or),
	F=..[Or,F1,F2],!,
	serv_head_list(F1,F1L),serv_head_list(F2,F2L),
	append(F1L,F2L,FL),!.
serv_head_list(F,[F]).

list_fmla([],Lp,F) :- list_head(Lp,F),!.
list_fmla(Ln,[],F) :- negate_l(Ln,Ln1),list_head(Ln1,F),!.
list_fmla(Ln,Lp,(B -> H)) :- list_body(Ln,B),list_head(Lp,H),!.

serv_list_fmla([],Lp,F) :- serv_list_head(Lp,F),!.
serv_list_fmla(Ln,[],F) :- serv_negate_l(Ln,Ln1),serv_list_head(Ln1,F),!.
serv_list_fmla(Ln,Lp,F) :- serv_list_body(Ln,B),serv_list_head(Lp,H),
	translit('->',Imp),
	F=..[Imp,B,H],!.

list_seq([],Lp,F) :- list_head(Lp,F),!.
list_seq(Ln,[],F) :- negate_l(Ln,Ln1),list_head(Ln1,F),!.
list_seq(Ln,Lp,(H :- B)) :- list_body(Ln,B),list_head(Lp,H),!.

negate_l([not(H)|L],[H|L1]) :- negate_l(L,L1),!.
negate_l([H|L],[not(H)|L1]) :- negate_l(L,L1),!.
negate_l([],[]).

serv_negate_l([NotH|L],[H|L1]) :- translit(not,Not),
	NotH=..[Not,H],serv_negate_l(L,L1),!.
serv_negate_l([H|L],[NotH|L1]) :- translit(not,Not),
	NotH=..[Not,H],
	serv_negate_l(L,L1),!.
serv_negate_l([],[]).

remove_alls(forall(_,H),F) :- remove_alls(H,F),!.
remove_alls(all(_,H),F) :- remove_alls(H,F),!.
remove_alls(H,H).

/* Das erste Argument ist ein einstelliger Funktor (z.B. not). Die als
   zweites Argument uebergebene Liste wird zerlegt: das dritte Argument
   nimmt alle Elemente auf, die den Funktor als Hauptfunktor haben (der
   wird dabei entfernt), das vierte Argument alle uebrigen. */

sort_by_functor(_, [], [], []).
sort_by_functor(Op, [X|L], [X1|L1], L2) :-
	X=..[Op, X1],
	!,
	sort_by_functor(Op, L, L1, L2).
sort_by_functor(Op, [X|L], L1, [X|L2]) :-
	!,
	sort_by_functor(Op, L, L1, L2).

/* goal_selection/3 erlaubt die Auswahl eines Ziels aus der als zweitem
   Argument uebergebenen Liste entweder ueber eine Tcl/Tk-Auswahlbox oder
   aus einer Liste. Die Listenelemente sind von der Form String-Term, dabei
   wird String angezeigt und Term fuer die Rueckgabe verwendet. Die getroffene 
   Auswahl wird als drittes Argument zurueckgegeben. Das erste Argument gibt 
   die Geometry-Optionen fuer die Tcl/Tk-Box an, wird also fuer die Textauswahl
   ignoriert. */

goal_selection(Geometry, ListBoxEntries, Selection) :-
	ilf_state(tcl, on),
	!,
	tk_goal_selection(Geometry, ListBoxEntries, Selection).
goal_selection(_, ListBoxEntries, Selection) :-
	t_list_select(ListBoxEntries, Selection).

t_list_select(TL,T) :- 
	writeln("Select goal"),
	t_list_menu(TL, 1, N),
	nth_member(TL, N, _ - T),
	!.

t_list_menu([T-_|TL], N, TT) :- 
	printf("%w. %w\n",[N,T]),
	(N1 is N+1),
	t_list_menu(TL, N1, TT),!.
t_list_menu([], N, I) :- 
	printf("Select (0. aborts): ", []),
	repeat,
	read(I),
	(
		integer(I),
		0 =< I, I < N,
		!
	;
		N1 is N-1,
		printf("Enter a number between 0 and %d: ", [N1]),
		fail
	).
					
nth_member(_, 0, ""-"").
nth_member([T|_],1,T).
nth_member([_|TL],N,T) :- 
	(N1 is N-1),
	nth_member(TL,N1,T).

/* schnelle Listenumkehr aus algebra.pro */
rev(L,L1) :- rev(L,[],L1).
rev([],L,L).
rev([E|L0],L2,L1) :- rev(L0,[E|L2],L1).

/* dialog(+Title,+Text,+Bitmap,+Default,+Args,-Sel) zeigt 'Text' und 'Args' entweder in Tcl/Tk-Fenster 
   ('Text' in oberer Haelfte, die Elemente der Liste 'Args' als Labels von Buttons in unterer Haelfte,
   vgl. tk_dialog in tcltools.pl) oder im ILF-Fenster an.
   'Sel' gibt die Nummer des ausgewaehlten 'Args'-Elements zurueck. */

dialog(Title,Text,Bitmap,Default,Args,Sel) :-
	ilf_state(tcl, on),
	!,
        tk_dialog(Title,Text,Bitmap,Default,Args,Sel).
dialog(_,Text,_,_,Args,Sel) :-
	t_dialog_select(Text,Args,Sel).

t_dialog_select(Text,Args,Sel) :- 
	writeln(Text),
	t_dialog_menu(Args, 1, Sel),
	!.

t_dialog_menu([Arg|ArgL], N, Sel) :- 
	printf("%w. %w\n",[N,Arg]),
	(N1 is N+1),
	t_dialog_menu(ArgL, N1, Sel),!.
t_dialog_menu([], N, I) :- 
	printf("Select: ", []),
	repeat,
	read(I),
	(
		integer(I),
		0 =< I, I < N,
		!
	;
		N1 is N-1,
		printf("Enter a number between 0 and %d: ", [N1]),
		fail
	).

/* make_dir ueberprueft ob ein Verzeichnis da ist und legt es an, falls esnicht existiert */

make_dir(S) :- exists(S),!.
make_dir(S) :- pathname(S,P),make_dir(P),
	concat_string(["mkdir ",S],Cmd),
	system(Cmd),!.



% compile_with_failure is like compile but fails, if any syntax error occurs
% in the text to be compiled.
% The other behavior is like compile: The same error-handlers are used
% to catch the error.
%
% compile_with_failure/1 is implemented as a tool compile_with_failure_body/2
% in order to make the compile in the same module from what the predicate
% was called.


compile_with_failure_body(File, Mod):-
	set_synt_handler,
	block(call(compile(File), Mod), _ , compile_with_failure_handler),
	unset_synt_handler,
	!.

compile_with_failure_handler:-
	unset_synt_handler,
        !, fail.


% Redirecting of all error-handlers, which deals the compile-errors
% to ilf-specific error-handlers.
% The compile errors have the number-range from 110 to 132 but without 123.	

set_synt_handler:-
	assert(tmp_synt_no(110)),
	repeat,
	retract(tmp_synt_no(N)), N1 is N + 1, assert(tmp_synt_no(N1)),
	not(N = 123),
	(
	    N > 132
	;
	    set_error_handler(N, ilf_synt_handler/3),
	    fail
	),
	retract_all(tmp_synt_no(_)),
	!.

% Resetting of all error-handlers, which deals the compile-errors.

unset_synt_handler:-
	assert(tmp_synt_no(110)),
	repeat,
	retract(tmp_synt_no(N)), N1 is N + 1, assert(tmp_synt_no(N1)),
	not(N = 123),
	(
	    N > 132
	;
	    reset_error_handler(N),
	    fail
	),
	retract_all(tmp_synt_no(_)),
	!.

ilf_synt_handler(No, Goal, Mod):-
	(error(default(No), Goal, Mod) ; true),
	abort,
	!, fail.
	
% For ilf16: Analyzing terms in a proof
% lower_term(T1,T2): T2 ia a subterm of T1 with the same root
lower_term(X,X) :- var(X),!,fail.
lower_term(T,T1) :- T=..[Op|Args],lower_term_l(Args,Args1),T1=..[Op|Args1].

lower_term_l([],[]).
lower_term_l([X|L],[X|L1]) :- var(X),!,lower_term_l(L,L1).
lower_term_l([_|L],[_|L1]) :- lower_term_l(L,L1).
lower_term_l([T|L],[T1|L1]) :- lower_term(T,T1),lower_term_l(L,L1).

/* Experimental Data: */
makeJoaoSubterms:- compile("//C/Users/dahn/CloudStation/ILF/ilf16/JoaoProof4Reduced.pl"),find_subterms,listing(id_subterm_count/3).

subterm(X,X) :- var(X),!,fail.
subterm(X=Y,T) :- !,subterm_l([X,Y],T).
subterm(not(X),T) :- !,subterm(X,T).
subterm(T,T1) :- lower_term(T,T1).
subterm(T,T1) :- T=..[_Op|Args],subterm_l(Args,T1).

subterm_l([T|_],T1) :- subterm(T,T1).
subterm_l([_|L],T1) :- subterm_l(L,T1).

:- dynamic(id_subterm_count/3).
find_subterms :- setval(subterm_count,0),retract_all(id_subterm_count(_,_,_)),fail.
find_subterms :- proof(_,contents,Term),subterm(Term,Subterm),register_subterm(Subterm),fail.
find_subterms.

register_subterm(Term) :- id_subterm_count(Id,Subterm,Count),variant(Term,Subterm),!,retract(id_subterm_count(Id,_,_)),Count1 is Count+1,assert(id_subterm_count(Id,Subterm,Count1)),!.
register_subterm(Term) :- getval(subterm_count,Id),assert(id_subterm_count(Id,Term,1)),C is Id+1,setval(subterm_count,C),!.
