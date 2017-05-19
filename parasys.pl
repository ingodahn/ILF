/* @(#)parasys.pl	1.32 checked in 05/28/98
/* Author: Dahn
/*
/* Praedikate zur Systemanpassung 
*/
:- module(parasys).

:- export op(100,fy,vi).
:- export op(600,xfx,:=).
:- export op(100,fy,vi).
:- export op(600,xfx,:=).
:- export op(100,fy,edm).
:- export op(110,fy,edms).
:- export op(1200,fy,which).
:- export op(1200,fy,lst).
:- export op(1200,xfy,lst).
:- export op(1200,fy,lstall).
:- export op(110,fy,ms).
:- export op(110,fy,edt).
:- export op(700,xfx,is_string).
:- export op(600,yfx,&).

:- export 
	(:=)/2,
	(assert)/2,
	(assign)/2,
	clear_module/0,
	clear_module/1,
	edm/0,
	edms/1,
	edt/1,
	eval/2,
	get_clause/3,
	get_clause/4,
	is_string/2,
	io_module/1,
	io_module/2,
	io_ax/1,
	(lst)/1,
	(lst)/2,
	(lstall)/1,
	make_abolish/2,
	mk_all_global_except/1,
	mk_all_global_except/2,
	make_dynamic/2,
	make_exported/2,
	(match)/2,
	(move_pred)/2,
	ms/1,
	(occur)/0,
	parasys_top/0,
	(retract)/2,
	(retract_all)/2,
	safe_assert/1,
	safe_retract/1,
	textedit/1,
	top_assert/1,
	top_asserta/1,
	top_retract/1,
	top_retract_all/1,
	reconsult/1,
	vi/0,
	(which)/1.

:- export
        isdefin/3,
        user_name/1,
	mkdir_unless_exists/1,
	rm_if_exists/1,
	rm_wcfiles/1.

:- import ilfsys.

?- begin_module(parasys).

:- lib(numbervars).
numbervars(X) :- numbervars(X, 0, _). 

/* We don't use Windows specific settings
parasys_top :-
	get_flag(object_suffix, "dll"),
	!,
	get_right_file("pl/parasys_win.pl", ParasysWin),
	compile(ParasysWin).
*/
parasys_top.


/* Starten von vi bzw. vi filename.pro */

?- mode(vi(+)).
(vi) :- exec("vi",60000).
(vi(File)):- concat_strings(File,".pro",Filepro),
    concat_strings("vi ",Filepro,S),
    exec(S,_).

/* Starten von textedit bzw. textedit filename.pro */

?- mode(textedit(+)).
(textedit(File)):- concat_strings(File,".pro",Filepro),
    concat_strings("textedit ",Filepro,S),
    exec(S,_).


/* edm Module editiert Module.pro und fuehrt reconsult durch */

?-mode(edm(+)). 
(edm(Module)) :-  concat_strings(Module,".pro",File),
    concat_strings("textedit ",File,S),
    exec(S,_),
    state(output_module,Old,Module),
    reconsult(Module),
    state(output_module,_,Old).

/* edms Module editiert Module.pro, reconsults und speichert Module.prm */

?-mode(edms(+)).
(edms(Module)) :-  concat_strings(Module,".pro",File),
    concat_strings("textedit ",File,S),
    exec(S,_),
    state(output_module,Old,Module),
    reconsult(Module), concat_strings(Module,"_top",GoalS),
    atom_string(Goal,GoalS),(Goal ; true),
    concat_strings(Module,".prm",_),
    save(Module,FileM,Goal,data,readwrite),
    write("New "),write(FileM),write(" saved."),nl,
    state(output_module,_,Old).
    
/* ms Module reconsults Module.pro in Module und speichert Module.prm */

?-mode(ms(+)).
(ms(Module)) :- 
    (module(Module,_,_,_,_,_) ; create_module(Module,actual)),
    state(output_module,Old,Module),
    reconsult(Module), concat_strings(Module,"_top",GoalS),
    atom_string(Goal,GoalS),(Goal ; true),
    concat_strings(Module,".prm",FileM),
    save(Module,FileM,Goal,data,readwrite),
    write("New "),write(FileM),write(" saved."),nl,
    state(output_module,_,Old).

/* edt Predname editiert den Modul.pro wenn Modul Predname exportiert */
    
?-mode(edt(+)).
edt(Pred):- get_flag(Pred/_,definition_module,Module),
    textedit(Module).

/* lst Predname zeigt an, in welchem Module Predname liegt und listet Predname Erfasst werden nur die Praedikate, die vom Toplevelmodule aus sichtbar sind.
Durch Deklaration als Tool ist Aufruf als lst/1 moeglich */

lst(Pred,Top) :-
	atom(Pred),
	!,
	lst(Pred/_, Top).
lst(Pred/N,Top) :-
	atom(Pred), number(N),
	call(get_flag(Pred/N,definition_module,DefMod), Top),
	!,
	lst_visib(Pred/N,Top),
	(
		call(get_flag(Pred/N,stability,dynamic),Top),
		call(listing(Pred/N), DefMod),
		nl
	 	;
		listing_static(Pred/N, Top)
	),
	!.
lst(Pred/N,Top) :-
	call(current_predicate(Pred/N),Top),
	lst(Pred/N, Top),
	fail.
lst(_,_).		 

% lst_visib writes out definition-file of predicate and the visibility 
% for all other modules if the predicate is exported by the definition-module
lst_visib(Pred/N, Top):-
	call((
	      get_flag(Pred/N,definition_module,DefMod),
	      get_flag(Pred/N,visibility,Vis)
	    ), Top),
	(
		call(get_flag(Pred/N,source_file,File),Top),
		call(get_flag(Pred/N,source_line,Line),Top),
		(Vis = imported, 
		 printf("/* %q defined in file %q line %q\n  is %q from %q ",[Pred/N,File,Line,Vis,DefMod])
	        ;
		 printf("/* %q defined in file %q line %q\n  is %q in %q ",[Pred/N,File,Line,Vis,DefMod])
	        )
	;
		printf("/* %q is %q in %q ",[Pred/N,Vis,DefMod])
	), 
	(
		call(get_flag(Pred/N,stability,dynamic),Top),
		write("(dynamic) */\n\n")
	 	;
	 	write("(not dynamic) */\n")
	),%% This was the old part written by T. Honigmann

	%% If the predicate is exported, we list all modules which uses
	%% this predicate
	(
	 call(get_flag(Pred/N,visibility, exported), DefMod),
	 nl,
	 current_module(Mod),
	 not is_locked(Mod),
	 once((
	  call((
	      current_predicate(Pred/N),
	      get_flag(Pred/N, definition_module, DefMod)
	     ), Mod),  % The same predicate is also visible in Mod
	  (
	   Mod = Top
          ;
	   call(get_flag(Pred/N,visibility, VisImport), Mod), %VisImport should be always imported 
	   printf("/* %q is %q from %q in module %q */\n",[Pred/N, VisImport, DefMod, Mod])
          )
         )),
	 fail
        ;
	 nl,
	 true
        ).
	

listing_static(Pred/N, Top) :-
	call(get_flag(Pred/N, source_file, File), Top),
	call(get_flag(Pred/N, source_offset, Offset), Top),
	!,
	listing_static(Pred/N, File, Offset).
listing_static(_, _) :- nl.

listing_static(_, File, _) :-
	get_file_info(File, readable, off),
	printf("/* %w ist not readable */\n\n", [File]).
listing_static(_, File, _) :-
	once((
		current_compiled_file(File, TimeCompiled, _),
        	get_file_info(File, mtime, TimeModified)
	)), 
	TimeCompiled =\= TimeModified,
	printf("/* %w was changed after compiling */\n\n", [File]).
listing_static(Pred/N, File, Offset) :-
	open(File, read, Stream),
	seek(Stream, Offset),
	length(Args, N),
	Head =.. [Pred|Args],
	nl,
	repeat,
	read(Stream, Clause),
	numbervars(Clause),
	listing_static_clause(Clause, Head), 
	close(Stream),
	nl.

listing_static_clause(Head, Head) :-
	writeclause(Head),
	!,
	fail.
listing_static_clause(Head:-Body, Head) :-
	writeclause(Head:-Body),
	!,
	fail.
listing_static_clause(_, _).

/* lstall/1 zeigt alle (auch nicht sichtbaren) dynamischen Definitionen */

lstall(Pred) :- atomic(Pred),
	setof([Pred,N,Mod],isdefin(Pred,N,Mod),L),
	lstall_l(L).
lstall(Pred/N) :- setof([Pred,N,Mod],isdefin(Pred,N,Mod),L),
	lstall_l(L).

lstall_l([[Pred,N,Mod]|L]) :- lst((Pred/N),Mod),
	lstall_l(L),!.
lstall_l([]).

isdefin(Pred,N,Mod) :- current_module(Mod),
	not is_locked(Mod),
	call(current_predicate(Pred/N),Mod),
	call(get_flag(Pred/N,definition_module,Mod),Mod).

/* which zeigt nur die Moduln. Ist als Tool deklariert, deshalb Aufruf mit which/1 moeglich */

which(Pred, Module) :-
	atom(Pred),
	which(Pred/_, Module).
which(Pred/N,Module) :- 
	atom(Pred), number(N),
	!,
	call(get_flag(Pred/N,definition_module,Mod),Module),
	call(get_flag(Pred/N,visibility,Vis),Module),
	(Vis==imported -> In="from" ; In="in"),
	printf("%q is %q %s %q\n",[Pred/N,Vis,In,Mod]),
	!.
which(Pred/N,Module) :- 
	call((
		current_predicate(Pred/N)
		;
		current_built_in(Pred/N)
	      ),Module),
	which(Pred/N,Module),
	fail.

io_module(Mod) :- set_flag(toplevel_module,Mod).

io_module(Old,New) :- get_flag(toplevel_module,Old),
	set_flag(toplevel_module,New).
io_module(Old,_) :- set_flag(toplevel_module,Old),fail.

io_ax(Mod) :- get_flag(toplevel_module,Mod),
	set_flag(toplevel_module,axioms).

top_assert(C) :- get_flag(toplevel_module,Mod),
	call(assert(C),Mod),!.

top_asserta(C) :- get_flag(toplevel_module,Mod),
	call(asserta(C),Mod),!.

top_retract(C) :- get_flag(toplevel_module,Mod),
	call(retract(C),Mod),!.

top_retract_all(C) :- get_flag(toplevel_module,Mod),
	call(retract_all(C),Mod),!.

reconsult(File) :- open(File,read,input),fail.
reconsult(_) :- repeat,read(Term),reconsult_process(Term),Term = end_of_file,close(input),!.

reconsult_process((?- P)) :- call(P),!.
reconsult_process(end_of_file) :- !.
reconsult_process(P) :- top_assert(P).
	
safe_assert((H :- B)) :- functor(H,Op,N),
	get_flag(toplevel_module,ModTop),
	(
	call(get_flag(Op/N,definition_module,Mod),ModTop),
	call(assert((H :- B)),Mod)
	;
	call(assert((H :- B)),ModTop)
	),!.
safe_assert(H) :- functor(H,Op,N),
	get_flag(toplevel_module,ModTop),
	(
	call(get_flag(Op/N,definition_module,Mod),ModTop),
	call(assert(H),Mod)
	;
	call(assert(H),ModTop)
	),!.
	
safe_retract((H :- B)) :- functor(H,Op,N),
	get_flag(toplevel_module,ModTop),
	call(get_flag(Op/N,definition_module,Mod),ModTop),!,
	call(retract((H :- B)),Mod).
safe_retract(H) :- functor(H,Op,N),
	get_flag(toplevel_module,ModTop),
	call(get_flag(Op/N,definition_module,Mod),ModTop),!,
	call(retract(H),Mod).

get_clause(P/N,C,Nr,Mod) :- 
	functor(T,P,N),
	C1=(T :- _),
	(
	C=(_ :- _),CC=C
	;
	CC=(C :- true)
	),
	setval(clause_count,1),!,
	get_clause1(C1,CC,Nr,Mod).

get_clause1(C1,C,Nr,Mod) :- call(clause(C1),Mod),
	(
	C1=C,getval(clause_count,Nr)
	;
	incval(clause_count),
	fail
	).

make_abolish((P1,P2),Mod) :- !,make_abolish(P1,Mod),make_abolish(P2,Mod),!.
make_abolish(P,Mod) :- 
	call((
		current_predicate(P),
		get_flag(P,definition_module,Mod),
		abolish(P)
	),Mod),!.
make_abolish(_,_).

make_dynamic((D1,D2),Mod) :- !,make_dynamic(D1,Mod),make_dynamic(D2,Mod),!.
make_dynamic((P/N),Mod) :- call(current_predicate(P/N),Mod),!.
make_dynamic((P/N),Mod) :-call(dynamic(P/N),Mod).

make_exported((D1,D2),Mod) :- !,make_exported(D1,Mod),make_exported(D2,Mod),!.
make_exported((P/N),Mod) :- call(get_flag(P/N,visibility,exported),Mod),!.
make_exported((P/N),Mod) :-call(export(P/N),Mod).

/* statt assign besser setval benutzen */
?- mode(assign(+,+)).
assign(X,Y) :- 
	X=..L,
	append(L,[U],L1),
	X1=..L1,
	(safe_retract(X1);true),
	U=Y,
    	safe_assert(X1),
    	!.

/* arithmetische Operatoren fuer := */
arith_op(+).
arith_op(*).
arith_op(-).
arith_op(/).
arith_op(//).
arith_op(mod).
arith_op(float).
arith_op(fix).
arith_op(truncate).
arith_op(real_round).
arith_op(log).
arith_op(exp).
arith_op(^).
arith_op(sqrt).
arith_op(sin).
arith_op(cos).
arith_op(tan).
arith_op(asin).
arith_op(acos).
arith_op(atan).
arith_op(sinh).
arith_op(cosh).
arith_op(tanh).
arith_op(asinh).
arith_op(acosh).
arith_op(atanh).

/* := Ergibtanweisung mit Auswertung der echten Seite */
/* Falls moeglich durch setval ersetzen */

?-mode(:=(+,+)).
X := Y :- eval(Y,Z),assign(X,Z),!.

?- mode(eval_list(+,?)).
eval(X,_) :- var(X),!,fail.
eval(X,_) :- string(X),!,fail.
eval(Y,Y) :- number(Y),!.
eval(Y,Z) :- Y=..[F|L],arith_op(F),!,
   eval_list(L,L1),Z1=..[F|L1],Z is Z1.
eval_list([],[]) :- !.
eval_list([E|L],[E1|L1]) :- eval(E,E1),!,eval_list(L,L1).

/* backtrackbare Versionen von assert und retract nicht portiert*/
/* waere aufwendig portierbar, da man nur am Anfang oder Ende asserten kann */

retract_b(P,C,N,V) :- clause(P,C,N,V),clause(P,C1,N,V1),
        (retract(P,_,N,_)
        ;
        M is N-1,assert(C1,M,V1),!,fail).
assert_b(C,N,V) :- assert(C,N,V)
        ;
        M is N+1,functor(C,F,Ar),retract(F/Ar,C,M),!,fail.

/* move_pred(Predname/Stellenzahl,Modul) verschiebt Predname/Stellenzahl in Modul */

?- mode move_pred(+,+),move_pred(+,+,+).

move_pred(Pred/N,M1) :- isdefin(Pred,N,M0),
	call(get_flag(Pred/N,stability,dynamic),M0),
	get_flag(toplevel_module,Mod),
	move_pred(Pred/N,M0,M1),
	set_flag(toplevel_module,Mod),
        !.
move_pred(Pred,_) :- write(Pred),writeln(" undefined or not dynamic"),fail.

move_pred(_,M,M) :- !.
move_pred(P/N,M0,M1) :- 
	functor(H,P,N),
	call(retract(H :- B),M0),
	call(assert(H :- B),M1),
	fail.
move_pred(Pred,M0,_) :- call(abolish(Pred),M0).

assert(P,Module) :- call(assert(P),Module).

retract(P,Module) :- call(retract(P),Module).

retract_all(P,Module) :- call(retract_all(P),Module).

/* Beginn occur check */

occur :- get_flag(occur_check,on),ilf_state(occur,_,off),
	writeln("Occur check is now OFF"),!.
occur :- get_flag(occur_check,off),ilf_state(occur,_,on),
	writeln("Occur check is now ON"),!.

/* unify kann durch = ersetzt werden */
/* Ende occur check */

/* match(X,Y) matcht X mit Y wobei Variable in X nicht belegt werden */

match(X,Y) :- 
	instance(X,Y),X=Y,!.

/* Prolog 2 -> Eclipse */
/* & besser duch concat_strings ersetzen */

:- lib(cio).

?- op(700,xfx,is_string).
?- op(600,yfx,&).

A is_string B & C :- 
	B1 is_string B,
	B2 is_string C,
	concat_strings(B1,B2,A),!.
A is_string substring(B, Start, Len) :-
	B1 is_string B,
	Start1 is Start+1,
	Len1 is Len,
	substring(B1, Start1, Len1, A),
	!.
A is_string insert(B, C, Start) :-
	BB is_string B,
	CC is_string C,
	Len1 is Start,
	Start2 is Len1+1,
	Len2 is string_length(BB)-Len1,
	substring(BB, 1, Len1, B1),
	substring(BB, Start2, Len2, B2),
	concat_string([B1, CC, B2], A),
	!.
A is_string B :-
	atom(B),
	atom_string(B, A),
	!.
A is_string A.

/* Prompt so, dass nach ; Return gegeben werden muss */

answer(_,more_answers) :- !, ask_more.
answer(X, Y) :- call(sepia_answer(X, Y), sepia_kernel).

ask_more :- 
	write(toplevel_output, "     More? (;)"),
	flush(toplevel_output),
	read_string(toplevel_input, "\n", _, Input),
	(name(Input, [0';|_]) ->
		fail
		;
		writeln(toplevel_output, "\nyes.")
	).

?- (ilf_state(x,on) -> set_error_handler(156,answer/2);true).


/* Loeschen von Files  */

rm_if_exists(File) :- 
	exists(File),
	/* doesn't wor if eclipse has opened this file
	delete(File),
	*/
	!.
rm_if_exists(_).

	 
% Files ist ein String der wild-characters enthalten kann  
rm_wcfiles(Files) :-
	concat_string(["sh -c 'rm ",Files, "'"],Cmd),
	exec(Cmd,[null,null,null]).


/* Anlegen von Directories */
mkdir_unless_exists(Dir) :-
	exists(Dir),
	!.
mkdir_unless_exists(Dir) :-
	concat_string(["mkdir ", Dir], Cmd),
	exec(Cmd, _),
	!.


/* mk_all_global_except(ExceptionL,Mod) sammelt alle in Mod 
 * definierten  Praedikate ein 
 * und macht sie global ausser denen die in ExceptionL erwaehnt sind
 * Da als Tool definiert ist es auch ohne Angabe von Mod nutzbar
 * Wird in load_tac gebraucht.
 */

:- tool(mk_all_global_except/1,mk_all_global_except/2).

mk_all_global_except(ExceptionL,Mod):-
	(setof(Pred/N,isdefin1(Pred,N,Mod),PredL) ; PredL = []),!,
	(subtract(PredL,ExceptionL,PredL1) ; PredL1 = PredL),
	global_l(PredL1,Mod).
	
global_l([],_):-!.
global_l([H|T],Mod):- 
	call((get_flag(H,visibility,global) ;global(H)),Mod),
	global_l(T,Mod).

isdefin1(Pred,N,Mod) :- %current_module(Mod),
	not is_locked(Mod),
	call(current_predicate(Pred/N),Mod),
	call(get_flag(Pred/N,definition_module,Mod),Mod).


/* clear_module loescht alle im Module definierten Praedikate
 * Da als Tool definiert ist es auch ohne Angabe von Mod nutzbar
 */
	
:- tool(clear_module/0,clear_module/1).

clear_module(Mod):-
	(setof(Pred/N,isdefin1(Pred,N,Mod),PredL) ; PredL = []),!,
	retract_all_l(PredL,Mod).
	
retract_all_l([],_):-!.
retract_all_l([(Pred/Arity)|T],Mod):-
	mk_underscore_l(Arity,ArgL),
	Pred1=..[Pred|ArgL],
	(call(retract_all(Pred1),Mod) ; true),
	retract_all_l(T,Mod).
	
mk_underscore_l(0,[]):-!.
mk_underscore_l(N,[_|T]):-
	N1 is N - 1,
	mk_underscore_l(N1,T).		


user_name(User) :- getenv("USER",User),!.
user_name(User) :- getenv("LOGNAME",User),!.
user_name(User) :- exec("whoami",[null,V,null]),
	read_string(V,"\n",_,User),close(V),!.


/* Variable Name Structures */

read(Stream,Term,VarS,VarS1) :- readvar(Stream,Term,VarT),
	union(VarT,VarS,VarS1),!.

?- parasys_top.
/* Ende Parasys */

