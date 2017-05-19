/* File @(#)thman.pl	2.28 checked in 01/08/99
/* Author: Dahn
/*
/*  Theorie-Management 
*/
/* libcomm benutzen, wenn multiuser-Mechanismus von Eclipse nicht funktioniert Dann muss der ilf_state multiuser in .ilfrc auf off gesetzt sein */


:- module(thman).

/* database_kernel und kb benutzen, wenn multiuser-Mechanismus von Eclipse funktioniert */
/* Importe aus libcomm wenn multiuser-Mechanismus von Eclipse nicht funktioniert 

:- (import database_kernel),
   lib(kb).
*/

:- import ilfsys.

:- import 
	select_prompt/1,
	tree_get_handlestate/4,
	tree_read/1,
	tree_write/1,
	tree_writeq/1
		from treecomm.

:- import ((':')/2) from excomm.

:- import 
	body_list/2,
	compile_pred/1,
	list_body/2,
	prepare_dynamic/1,
	prepare_dynamic_l/1,
	strict_union/3,
	strict_remove_l/3
		from tools.

:- import treemenu/1 from treemenus.

:- import setarg/3 from sepia_kernel.

:- import 
	create_menu/1,
	xcommand/1
		from menumngr.

:- import show_block_proof/0 from proofout.

:- import
	rm_if_exists/1,
	rm_wcfiles/1
			from parasys.

:- ilf_state(tcl,off);(
	import start_genEdit/2 from tcltools
	),!.
	
:- export 
	(activate_interpretation)/2,
	(ax_name)/4,
	change_status/1,
	change_status/2,
	complete_schema/3,
	clausify/2,
%	(close_database)/0,
	define_read_macros/0,
	(definition)/3,
	(domain)/1,
	(deactivate_interpretation)/2,
	dont_replace/1,
	draw_axioms/0,
	draw_straights/0,
	edit_theory/0,
	edit_untyped_theory/0,
	erase_read_macros/0,
	expand_proof/0,
	expand_prooftree/0,
	free_vars/2,
	(forget_ax)/1,
	forget_domain/1,
	forget_domain_l/1,
	(forget_th)/0,
	(formula)/4,
	global_read_macros/0,
	hide_axioms/0,
	hide_straights/0,
	ins_proof/1,
	(learn_formula)/0,
	(let)/1,
	load_th/1,
	load_th_alw/1,
	load_tme_theory/1,
	load_tptp_problem/1,
	load_untyped_theory/1,
	make_theory_typed/1,
	make_working_domain/0,
	make_working_domain/1,
	(means)/2,
	move_fla/3,
	parse/1,
	put_in_domain/2,
	(recover_database)/0,
	(replace)/1,
	safe_transaction/1,
	set_default_theory/0,
	syntax_type/2,
	tv_proof/0,
	tv_proof/1, 
	(type)/2.

:- export (safe_transaction/1).

:- export 
	a_close/2,
	active_domain/1,
	add_types/2,
	collect_theory/2,
	complete_term/4,
	contract_abbrevs/2,
	conj2list/2,
	erase_local_type/3,
	expand_fla/2,
	extract_selected/3,
	est_type_term/0,
	gen_typed_sym/2,
	gen_typed_var/2,
	getting_active_domains/1,
	getting_domains/1,
	get_attribute/2,
	get_act_axnameL/1,
	get_act_axnameL/3,
	get_axnameL/3,
	get_pass_axnameL/1,
	get_signatureL/1,
	get_term_type/2,
	get_type/2,
	get_var_root/2,
	is_conj/1,
	is_disj/1,
	is_subtype/2,
	log_op/2,
	make_local_type/4,
	make_typed/2,
	mk_all_closure/3,
	negl_term/2,
	parse_term/1,
        posl_term/2,
	quant_op/2,
	read_typed/2,
	(renamed)/3,
	retract_all_clauses/1,
	rm_all/2,
	short_form/2,
	signature/2,
	standard_vars/2,
	trusted_fla/2,
	term_type/2,
	type_term/2,
	type_term_pl/2,
	unify_handler/2,
	var_has_typterm/2.
	
:- dynamic
	abbreviation/2,
	is_bound/2,
	last_var_name/2,
	local_type/2,
	noted_ax/3,
	noted_dom/2,
	(th_changed)/1,
	(theory_file)/1,
	(reserved_var)/3,
	active_interpretation/2,
	((mode_def)/2),
	((small_mode_def)/2),
	(struct_def/3),
	((func_def)/2),
	(pred_def/1),
	server_running_res/1,
	short_code/2,
	tmp/1,
	tmp_nested_load_th/0,
	user_type/2,
	user_widens/2,
	var_has_typterm/2,
    	typ_has_typterm/2,
	domain_def/1.

:- meta_attribute(thman,[print : print_handler/2, unify : unify_handler/2]).

?- op(1200,xfx,below).
?- op(1200,fy,end).
?- op(1200,fy,type).
?- op(1200,fy,define).
?- op(1200,fy,consider).
?- op(1199,fy,copy).
?- op(1198,fy,definitions).
?- op(1198,fy,formulae).
?- op(1200,xfy,interprets).
?- op(1198,yfx,into).
?- op(1200,yfx,by).
?- global_op(1198,fy,replace).
?- global_op(1110,xfy,as).  % wird in tactics gebraucht beim Formeln einlesen
?- op(1198,xfy,from).
?- global_op(1197,xfy,with).
?- global_op(1197,xfy,means).
?- global_op(900,fx,let).
?- op(900,xfx,<==>).
:- op(1200,fx,begin).
:- op(1150,fx,domain).
:- op(1185,fx,[reserve,definition]).
:- op(1180,fx,[mode,type,small_mode,set_type,pred,func,struct,fla,schema]).
:- op(1150,xfy,[for,is,gives]).
:- op(1100,xfx,and).
:- op(900,fy,non).
:- op(1170,xfy,':').



?- begin_module(thman).

:- export (safe_transaction/1, safe_transaction_body/2).
safe_transaction(X) :- current_module(M),safe_transaction_body(X,M).

thman_top :- 
	thman_init,
	/* not used for simplified ILF 2016
	open_ilf_kb,
	*/
	set_theory_ops.

open_ilf_kb :-
	ilf_state(kb, off),
	not(ilf_state(experts, on)),
	!.
open_ilf_kb :-
	ilf_state(kb, Old, on),
	once((
		Old = on
		;
		ilf_warning("ilf_state(experts, on) implies ilf_state(kb, on)",
		            [])
	)),
	connect_to_database,
	setval(current_domain,standard),
	setval(unify_types,on),
	make_working_domain,
	compile_pred(user_type/2),
	compile_pred(user_widens/2).

% after loading of thman.pl-code we change the priority of the
% standard prolog-Operator '->' to an value comparable the the standard
% priority in logical languages

% We set the priorities with respect to the priorities of
% standard prolog operator ';' (1100) and ',' (1000)
set_theory_ops:-
	op(1160,xfy,<->),
	op(1151,xfy,->),    % Redefinition of standard priority 1050

	% the next operators are global because of
	% setheo-outfiles contain them and the outfiles are compiled in
	% datamodules of experts
	global_op(1150,xfy,'<-'),
        global_op(1149,xf, '<-'),
	global_op(1148,fx, '<-').
:- set_theory_ops.



print_handler(S,S) :- getval(print_types,off),!,fail.
print_handler(S,A) :- get_attribute(S,A),!.

unify_handler(_,A) :- var(A),!.
unify_handler(T,A) :- syntax_type(T,A),!.

/* Simulation eines nested Transaction */
safe_transaction_body(Goal, Mod):-
	(
	 bang_register(transaction_active, 0),
	 !,
	 call(transaction(Goal), Mod)
	;
	 call(Goal, Mod)
	).


/* Initialisierung des Theorie-Menues in xilf */

thman_init :-
	ilf_state(x,on),
	once((
		create_menu('THEORY'),
		create_tptp_menu
	)),
	fail.
thman_init.

/* Arbeit mit bang_server */

connect_to_database :- 
	get_uih_file("tmp/data",DataDirS),
 	atom_string(DataDir,DataDirS),
 	est_valid_dir(DataDir), 
 	check_server(DataDir), 
	try_openkb(DataDir),
 	retract_all(server_running_res(_)).

/* try_openkb versucht, die Datenbank zu oeffnen. Wenn das fehlschlaegt, gibt
   es im Vordergrund eine Meldung mit Hinweisen zur Fehlerbeseitigung und
   die Kompilierung wird mit 'general error' abgebrochen;
   der Hintergrund wird mit einer kurzen Ausschrift beendet. */

try_openkb(DataDir) :-
	printf("ILF: openkb(%w): ", [DataDir]), flush(output),
	openkb(DataDir),
	!.
try_openkb(DataDir) :-
	current_module(exman),
	!,
	printf(" Background ILF fatal error: openkb(%s) failed.\n", [DataDir]),
	call((msg_write("\n"),
	      msg_write("!!! FATAL ERROR: OPENKB(%s) FAILED.\n", [DataDir])),
	exman),
	halt.
try_openkb(DataDir) :-
	server_running(DataDir),
	!,
	printf("\
!!! ILF fatal error: openkb(%w) failed. You should call\n\
	recover_database.\n\
!!! and restart ILF.  If that doesn't solve the problem, you should terminate\n\
!!! all bang_server for %w (by sending them signal INT),\n\
!!! remove the directory %w, and restart ILF.\n", 
	[DataDir, DataDir, DataDir]), 
	flush(output),
	error(1, openkb(DataDir)).
try_openkb(DataDir) :-
	printf("\
!!! ILF fatal error: openkb(%w) failed.\n\
!!! It seems that the database was opened in single user mode by another\n\
!!! Prolog process. Remove the files %w/bang.{usr,log}\n\
!!! if that is not the case and restart ILF.\n",
	[DataDir, DataDir]), 
	flush(output),
	error(1, openkb(DataDir)).
 	
 	
% est_valid_dir macht einfache Tests (Directory vorhanden und nicht leer),
% ob die Datenbank vorhanden ist, und versucht sie ggf. über den Aufruf von
% ilf_createkb anzulegen.
% Domains werden in domain(Name,title,TitelString) abgelegt.
% domain(Name,status,passive) ist auch moeglich
%Als properties sind in den Klauseln formula zugelassen:
% fla (speichert die Original-Formel ab),
% signature  hat Form :  [ML, PosL,NegL] 
%      wobei ML,PosL,NegL die Form
%    [[<FctSym/ArgTypeL>*],[<RelSym/ArgTypeL>*]] (bei FctSym ist 1.Element von ArgTypeL der Rueckgabetyp
%   ML ist die Liste der in der urspruengl. Formel vorkommenden Symbole, 
%   PosL, NegL kommen bei Klausifizierung, bzw. Klausifizierung
%   der negierten Formel  hinzu.
% fla_wo_types (die Formel mit den Typerganzung z.B. it(nat,succ(it(nat,X))),
% statt succ(X1 : nat) 
% clauses (Liste der Klauseln, ein Listeneintrag besteht aus [Nr, [HeadL], [BodyL]], 	
% negclauses (Liste der Klauseln der negierten Formel)
% dsccoded,dscuncoded ... hat Form: [[ EquationL ], [usedFctL]] oder [[],[]] wenn Formel nicht zugelassen
% spass hat Form: (String im Spass-Format,Liste der Typen, Liste der Operatoren)
% status kann passive sein.

est_valid_dir(DataDir):-
	not(exists(DataDir)), % noch keine Datenbank da
	ilf_createkb(DataDir).
est_valid_dir(DataDir):-
	read_directory(DataDir, '*', _, []), % Directory da, aber leer
	ilf_createkb(DataDir).
est_valid_dir(_).

ilf_createkb(DataDir) :-
 	createkb(DataDir),
 	(actskolem <==> [+ const_or_func, + number]),
	(formula <==> [+ domain, + name, properties, contents]),
	(type_term <==> [+ type, code_list]), 
	(operator <==> [+ domain, prio, asso, + op]),
	((schema) <==> [+ domain, + name, declaration, contents]),
	 ((definition) <==> [+ domain, defClause]),  % definition ist auch Operator, deshalb die Klammern
	 ((struct) <==> [+ domain, + type, + constructor, selectors]),
	 ((type) <==> [+ domain, name]),
	 ((below) <==> [+ domain,subtype,supertype]),
	 ((domain) <==> [+ domain,key,value]),
	 (reservation <==> [+ var,typ]),
	 (abbreviation <==> [+ short,+ long]),
	 insert_clause(domain(standard,title,"the standard domain")),
	insert_clause(definition(standard,user_type((_S_1{and([],set)} = _S_2{and([],set)}),and([],wff)))),
 	 closekb,
 	 sleep(5). /* sonst sagt mir bang_server knowledgebase ist noch offen */	
% check_server/1 startet ggf. Datenbankserver neu (nach Absturz bspw.)	
% Der Server wird im Vordergrund nur dann als vorhanden betrachtet, 
% wenn ein bang.pl existiert und ein bang_server unter der dort angegebenen 
% pid laeuft.  Dieser Test benoetigt aber funktionierendes (i)rsh. Wenn (i)rsh 
% nicht funktioniert (durch das "true" am Ende des Testkommandos wird irsh
% genau dann einen Rueckgabewert != 0 haben, wenn es in irsh selbst einen
% Fehler gab), aber bang.usr existiert, wird deshalb angenommen, dass
% der Server laueft. Damit schlaegt zwar evtl. spaeter das Oeffnen der KB 
% fehl, aber der Benutzer hat damit immer hoechstens einen bang_server laufen. 
% Der Hintergrund testet nur, ob bang.usr existiert. Wenn das nicht der
% Fall ist, stimmt garantiert was nicht, es wird mit einer kurzen Meldung
% abgebrochen. Wenn das File vorhanden ist, werden ggf. Fehler beim Oeffnen
% der KB bemerkt. Der Hintergrund startet nie einen bang_server, ebenfalls
% damit pro Nutzer maximal ein bang_server existiert.

check_server(DataDir):- 
	current_module(exman),
	!,
 	concat_string([DataDir, "/bang.usr"],UsrFile),
	(exists(UsrFile)
 	 ;
	 printf("Background ILF fatal error: no bang_server running.\n", []),
	 halt
	).
check_server(DataDir):- 
 	server_running(DataDir),
	!.
check_server(DataDir):-
 	concat_string([DataDir, "/bang.log"],LogFile),
 	concat_string([DataDir, "/bang.usr"],UsrFile),
 	rm_if_exists(LogFile),
 	rm_if_exists(UsrFile),
	(ilf_state(experts, off) ->
		true			% DB wird dann single user geoeffnet
		;
		get_right_exec_file("bin/start_bang_server", Bang),
		concat_string([Bang, " ", DataDir, " 5"], Cmd),
 		exec(Cmd, [null, bang_pid, null]),
		read(bang_pid, BangPid),
		close(bang_pid),
		check_server_pid(DataDir, BangPid)
	),
	!.

check_server_pid(_, -1) :-
	printf("\
!!! ILF fatal error: fork() failed while starting the bang_server.\n\
!!! Exit ILF and try again later.\n", []),
	flush(output),
	error(1, fork).
check_server_pid(DataDir, 0) :-
	printf("\
!!! ILF fatal error: Unexpected error starting bang_server.\n\
!!! You should terminate all bang_server for %s (by sending them signal INT),\n\
!!! remove the directory %s, and restart ILF.\n", 
	[DataDir, DataDir]), 
	flush(output),
	error(1, start_bang_server).
check_server_pid(DataDir, Pid) :-
	get_flag(hostname,Host),
	printf("bang_server is started under PID %w on %w.\n", [Pid, Host]),
				    % DokFile wird bei server_running eingelesen
 	concat_string([DataDir,"/bang.pl"], DokFile), 
 	rm_if_exists(DokFile),
 	tell(DokFile),
 	writeq(bang_pid(Host,Pid)), % manche Rechnernamen beginnen 
				    % mit Grossbuchstaben
 	told.

server_running(_):-  % haben schon rausgekriegt ob Server laeuft
	server_running_res(Result),
	!,
	Result == y.
server_running(DataDir):-
	concat_string([DataDir, "/bang.pl"],PidFile),
	exists(PidFile),
	open(PidFile, read, pidfilestr),
	read(pidfilestr,bang_pid(Host,Pid)),
	close(pidfilestr),
	concat_string([DataDir,"/pidtest.tmp"], Testfile), 
	rm_if_exists(Testfile),
	get_right_file("bin/ilfps", Ilfps),
	get_right_file("bin/irsh", Irsh),
	concat_string([Irsh, " ", Host," '", Ilfps, " ",Pid,
	               " | grep bang_server > ", Testfile,"; true'"
		      ], Cmd),
	exec(Cmd, [], CmdPid),
	wait(CmdPid, CmdStatus),
	!,
	(server_running(DataDir, PidFile, Testfile, CmdStatus) ->
	 	assert(server_running_res(y))
		;
	 	assert(server_running_res(n)),
		!,
		fail
	),
	!.
server_running(_):-
 	assert(server_running_res(n)), 
	!,
	fail.

server_running(_, PidFile, Testfile, 0) :-		% irsh ok
	get_file_info(Testfile, size, Size),
	rm_if_exists(Testfile),
	(Size == 0 -> 		%  d.h. kein Prozess mit der Nummer gefunden
	 	rm_if_exists(PidFile),
	 	!, 
	 	fail
		;
	 	true
	),
	!. 	
server_running(DataDir, _,  _, _) :-			% irsh-Fehler, alles
	concat_string([DataDir,"/bang.usr"],UsrFile),	% haengt von bang.usr ab
	exists(UsrFile),
	open(UsrFile, read, Usr),
	read_string(Usr, "", _, Line),
	close(Usr),
	!,
	substring(Line, "Distributed", _),
	!.
	
%% Praedikate zum Schliessen der Datenbank	

recover_database :- 
	kill_database_server,
	halt,!.

kill_database_server :- 
	get_uih_file("tmp/data/bang.pl",PidFile),
	exists(PidFile),
	open(PidFile, read, pidfilestr),
	read(pidfilestr,bang_pid(Host,Pid)),
	close(pidfilestr),
	concat_string(["rsh ",Host," kill -INT ",Pid],Cmd1),
	exec(Cmd1,[null,null,null]),
	!.	
kill_database_server.

%%%%%%%%%%%%%%%%%%%%%%
% Zugriff auf Datenbank
%%%%%%%%%%%%%%%%%%%%%%

/* retrieve_clause in transaction-context eingebettet,
  evtl. nicht noetig wenn Praedikate nur im Kontext gebraucht T.Baar */

formula(Dom,Name,Prop,Cont) :- 
	safe_transaction(retrieve_clause(formula(Dom,Name,Prop,Cont))).
all_formulas(Dom,Name,Prop,Cont) :- 
	safe_transaction(retrieve_clause((formula(Dom,Name,Prop,Cont) :- Body))),
	call(Body,thman).

schema(Dom,Name,Decl,Cont) :- 
	safe_transaction(retrieve_clause(schema(Dom,Name,Decl,Cont))).

definition(Dom,Name,Decl) :- 
	safe_transaction(retrieve_clause((definition(Dom,Name,Decl) :- Body))),
	call(Body).


type(Dom,Name) :- 
	safe_transaction(retrieve_clause((type(Dom,Name):- Body))),
	call(Body).

domain(Dom) :- 
	safe_transaction(retrieve_clause(domain(Dom,title,_))).
	
getting_domains(DomL) :-
	safe_transaction(
		setof(Dom,T^retrieve_clause(domain(Dom,title,T)),DomL)
		),
	!.	
getting_domains([]).

getting_active_domains(DomActL):-
	getting_domains(DomAllL),
	setof(Dom, DomAllL^(member(Dom, DomAllL), active_domain(Dom)), DomActL),
	!.
getting_active_domains([]).

insert_clause_l([E|L]) :- 
	safe_transaction(insert_clause(E)),
	insert_clause_l(L),!.
insert_clause_l([]).

forget_th :- 
	safe_transaction((
		setof(Dom,T^retrieve_clause(domain(Dom,title,T)),DomL),
		forgetting_domain_l(DomL),
		forgetting_reservations,
		forgetting_abbreviations,
		forgetting_typeterms,
		forgetting_actskolems
	)),fail.
forget_th :- prepare_dynamic_l([abbreviation/2,var_has_typterm/2,user_type/2,user_widens/2,local_type/2]),fail.
forget_th :- safe_transaction(forgetting_doms),
	retract_all(theory_file(_)),!.

forget_domain(Dom) :- safe_transaction(forgetting_domain(Dom)).

forget_domain_l([]):-!.
forget_domain_l([H|T]):-
	forget_domain(H),
	forget_domain_l(T).

forgetting_domain(Dom) :- retract_all_clauses((formula(Dom,_,_,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((operator(Dom,_,_,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((schema(Dom,_,_,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((definition(Dom,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((struct(Dom,_,_,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((type(Dom,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((below(Dom,_,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all_clauses((domain(Dom,_,_) :- _)),fail.
forgetting_domain(Dom) :- retract_all(active_interpretation(Dom,_)).

forgetting_domain_l([D|L]) :- forgetting_domain(D),forgetting_domain_l(L),!.
forgetting_domain_l([]).

forgetting_doms :- retract_all_clauses(domain(_,_,_)),fail.
forgetting_doms :- insert_clause(domain(standard,title,"the standard domain")),
	insert_clause(definition(standard,user_type((_S_1{and([],set)} = _S_2{and([],set)}),and([],wff)))).

forgetting_reservations :- retract_all_clauses(reservation(_,_)),fail.
forgetting_reservations.

forgetting_abbreviations :- retract_all_clauses(abbreviation(_,_)),fail.
forgetting_abbreviations.

forgetting_typeterms :- retract_all_clauses(type_term(_,_)),fail.
forgetting_typeterms.

forgetting_actskolems :- retract_all_clauses(actskolem(_,_)),fail.
forgetting_actskolems.

forget_ax(Domain-Name) :- safe_transaction((retract_all_clauses(formula(Domain,Name,_,_)),
		  fail
		  ;
		  true
		)),
		!.
forget_ax(Name) :- getval(current_domain,(Domain,_)),forget_ax(Domain-Name).

retract_all_clauses(D) :- repeat,(not (retract_clause(D))),!.


getting_from_database(X) :- retrieve_clause((X :- Body)),call(Body).

/* default theory */
set_default_theory :- collect_theory(T,[selected,unselected]),
	get_th_spec(T,T,T1),
	ilf_state(default_theory,_,T1),
	printf("Default theory set to %Dw.\n",[T1]),!.

get_th_spec([((D-_)/selected)|L],T,T1) :- member((D/selected),T),
	get_th_spec(L,T,T1),!.
get_th_spec([((D-N)/selected)|L],T,[(D-N)|T1]) :- get_th_spec(L,T,T1),!.
get_th_spec([D/selected|L],T,[D-_|T1]) :- get_th_spec(L,T,T1),!.
get_th_spec([_|L],T,T1) :- get_th_spec(L,T,T1),!.
get_th_spec([],_,[]).

/* Statusaenderungen fuer Formeln und domains */
change_status(S) :- collect_theory(L,S),change_status_l(L),!.

change_status_l([_/folded|L]) :- change_status_l(L),!.
change_status_l([_/fixed|L]) :- change_status_l(L),!.
change_status_l([(H/S)|L]) :- change_status(H,S),change_status_l(L),!.
change_status_l([]).

change_status(S,active) :- var(S),
	safe_transaction((
		retract_all_clauses(domain(_,status,_)),
		retract_all_clauses(formula(_,_,status,_))
	)),!.
change_status([I|IL],S) :- change_status(I,S),change_status(IL,S),!.
change_status([],_) :- !.
change_status(D-N,S) :- var(N),!,change_status(D,S),!.
change_status(D - N,active) :-
	safe_transaction((
		retract_all_clauses(formula(D,N,status,_))
	)),!.
change_status(D,active) :-
	safe_transaction((
		retract_all_clauses(domain(D,status,_)),
		retract_all_clauses(formula(D,_,status,_))
	)),!.

change_status(D - N,S) :- 
	safe_transaction(
		retract_all_clauses(formula(D,N,status,_))
	),
	safe_transaction((
		setof((D-N),C^retrieve_clause(formula(D,N,fla,C)),L)
		;
		L=[]
	)),
	safe_transaction(
		make_status_l(L,S)
	),!.

change_status(D,S) :- 
	safe_transaction(
		retract_all_clauses(domain(D,status,_))
	),
	safe_transaction((
		setof(D,T^retrieve_clause(domain(D,title,T)),L)
		;
		L=[]
	)),
	safe_transaction(
		make_status_l(L,S)
	),!.

make_status_l([D-N|L],S) :- insert_clause(formula(D,N,status,S)),
	make_status_l(L,S),!.
make_status_l([D|L],S) :- insert_clause(domain(D,status,S)),
	make_status_l(L,S),!.
make_status_l([],_).

active_domain(Dom):- safe_transaction(retrieve_clause(domain(Dom,status,passive))),
	!,fail.
active_domain(_).	


% Yields all active ax-names
get_act_axnameL(AxnameL):-
	safe_transaction(
		setof(ax_name(Dom, Name), active_ax(Dom, Name), AxnameL)
		),
	!.	
get_act_axnameL([]).

% Yields all passive ax-names
get_pass_axnameL(AxnameL):-
	safe_transaction(
		setof(ax_name(Dom, Name), passive_ax(Dom, Name), AxnameL)
		),
	!.	
get_pass_axnameL([]).





% get_act_axnameL/3 liefert alle Axiomennamen die matchen und activ sind
get_act_axnameL(Dom, Name, AxnameL):-
	safe_transaction(
		setof(ax_name(Dom, Name), Dom^Name^active_ax(Dom, Name), AxnameL)
	),
	!.	
get_act_axnameL(_,  _, []).


active_ax(Dom,Name) :- retrieve_clause(domain(Dom,title,_)),
	not retrieve_clause(domain(Dom,status,passive)),
	retrieve_clause(formula(Dom,Name,fla,_)).
	

passive_ax(Dom,Name) :- retrieve_clause(domain(Dom,title,_)),
	retrieve_clause(domain(Dom,status,passive)),
	retrieve_clause(formula(Dom,Name,fla,_)).


	 	
% get_axnameL/3 liefert alle Axiomennamen die matchen

get_axnameL(Dom,Name,AxnameL):-
	safe_transaction(
		setof(ax_name(Dom,Name),Dom^Name^F^retrieve_clause(formula(Dom,Name,fla,F)),AxnameL)
		),
	!.	
get_axnameL(_,_,[]).

% get_signatureL(SigL) liefert alle Signaturen zurueck
%  SigL hat die Form  [ <[[FuncSigL][RelSigL]]>*

get_signatureL(SigL):-
	safe_transaction(
	  setof(Sig,Dom^Name^Sig^retrieve_clause(formula(Dom,Name,signature,Sig)),SigL)
	),
	!.  
get_signatureL([]).

/* Einlesen von Domains, Theorien ... */
/**
 * Neuer Parser vom 25.4.96, Thomas Bauer
 **/



/*
 * Diese Makro-Praedikate sorgen dafuer, dass die Typterme
 * beim Einlesen in die gewuenschte Form (mit 'and') uebersetzt werden
 * und evtl. vorhandene Attribute sortiert werden
 */

as_trans(as(Var,and(Attributes,TypTerm)),X) :- -?->
    convert_attributlist(Attributes,AttributeList),
    sort_attributlist(AttributeList,SortedAttributeList),
    X = as(Var,and(SortedAttributeList,TypTerm)).
as_trans(as(Var,TypTerm),as(Var,and([],TypTerm))) :- !.

for_trans(for(Vars,and(Attributes,TypTerm)),X) :- -?->
    convert_attributlist(Attributes,AttributeList),
    sort_attributlist(AttributeList,SortedAttributeList),
    X = for(Vars,and(SortedAttributeList,TypTerm)).
for_trans(for(Vars,TypTerm),for(Vars,and([],TypTerm))) :- !.

is_trans(is(Term,and(Attributes,TypTerm)),X) :- -?->
    convert_attributlist(Attributes,AttributeList),
    sort_attributlist(AttributeList,SortedAttributeList),
    X = is(Term,and(SortedAttributeList,TypTerm)).
is_trans(is(Term,TypTerm),is(Term,and([],TypTerm))) :- !.

gives_trans(gives(Term,and(Attributes,TypTerm)),X) :- -?-> 
    convert_attributlist(Attributes,AttributeList),
    sort_attributlist(AttributeList,SortedAttributeList),
    X = gives(Term,and(SortedAttributeList,TypTerm)).
gives_trans(gives(Term,TypTerm),gives(Term,and([],TypTerm))) :- !.

/* Typcasting in Formeln zurueckgestellt ID 
consider_type(considering(H,as(V,and(A,T))),H1) :- -?->
    gen_typed_var(T,H,X),
    substitute(H,HH,U,U==V,[[V,X]]),
    H1=ex(X,(X=V,HH)),!.
consider_type(considering(H,as(V,T)),H1) :- 	
    consider_type(considering(H,as(V,and([],T))),H1),!.
*/


define_read_macros :-
%    (current_macro((considering/2),_,_,_),erase_macro((considering/2)) ; true),
    (current_macro((as/2),_,_,_),erase_macro((as/2)) ; true),
    (current_macro((for/2),_,_,_),erase_macro((for/2)) ; true),
    (current_macro((is/2),_,_,_),erase_macro((is/2)) ; true),
    (current_macro((gives/2),_,_,_),erase_macro((gives/2)) ; true),
%    define_macro((considering/2),consider_type/2,[]),
    define_macro((as/2),as_trans/2,[]),
    define_macro((for/2),for_trans/2,[]),
    define_macro((is/2),is_trans/2,[]),
    define_macro((gives/2),gives_trans/2,[]).

erase_read_macros :-
%    erase_macro((considering/2)),
    erase_macro((as/2)),
    erase_macro((for/2)),
    erase_macro((is/2)),
    erase_macro((gives/2)).

global_read_macros :-
%    (current_macro((considering/2),_,_,_),erase_macro((considering/2)) ; true),
    (current_macro((as/2),_,_,_),erase_macro((as/2)) ; true),
    (current_macro((for/2),_,_,_),erase_macro((for/2)) ; true),
%    (current_macro((is/2),_,_,_),erase_macro((is/2)) ; true),
    (current_macro((gives/2),_,_,_),erase_macro((gives/2)) ; true),
%    define_macro((considering/2),consider_type/2,[]),
    define_macro((as/2),as_trans/2,[global]),
    define_macro((for/2),for_trans/2,[global]),
%    define_macro((is/2),is_trans/2,[global]),
    define_macro((gives/2),gives_trans/2,[global]),
    	global_op(1110,xfy,as),
	global_op(1185,fx,[reserve,definition]),
	global_op(1180,fx,[mode,type,small_mode,set_type,pred,func,struct,fla]),
	global_op(1150,xfy,[for,gives]),
	global_op(1100,xfx,and),
	global_op(1075,xfy,<->),
	global_op(900,fy,non),
	global_op(1170,xfy,':').


replace(with(A1,B1)) :- 
	expand_fla((A1,B1),(A,B)),
	asserta(abbreviation(A,B)),
	safe_transaction(insert_clause(abbreviation(A,B))),!.

means(A1,B1) :- expand_fla((A1,B1),(A,B)),
	asserta(abbreviation(A,B)),!.
	
dont_replace(F) :-
	retract_all(abbreviation(F,_)),
	safe_transaction(retract_all_clauses(abbreviation(F,_))),!.

/* shorthands expandieren */

expand_fla(F1,F2) :- add_types(F1,F),is_shorthand(F,F2),!.

is_shorthand(X,X) :- var(X),!,
	get_attribute(X,A),
	is_shorthand(A,and(A1,M1)),
	setarg(1,A,A1),
	setarg(2,A,M1).
is_shorthand([],[]) :- !.
is_shorthand(X,Y) :- X=..[Op|Arg],is_shorthand_l(Arg,Arg1),
		XX=..[Op|Arg1],
		once(get_abbreviation(XX,Y)),!.
	
get_abbreviation(X,Y) :- abbreviation(X1,Y),instance(X,X1),X=X1.
get_abbreviation(X,X).

is_shorthand_l([F|Arg],[F1|Arg1]) :- is_shorthand(F,F1),
	is_shorthand_l(Arg,Arg1),!.
is_shorthand_l([],[]).

/* short prints */
short_form(X,Y) :- contract_abbrevs(X,Y1),contract_vars(Y1,Y),!.

contract_abbrevs(X,X) :- var(X),!.
contract_abbrevs([],[]) :- !.
contract_abbrevs(X,Y) :- 
	is_expansion(X,X1),
	X1=..[Op|Arg],
	contract_abbrevs_l(Arg,Arg1),
	Y=..[Op|Arg1],!.

contract_abbrevs_l([F|L],[F1|L1]) :- contract_abbrevs(F,F1),!,
	contract_abbrevs_l(L,L1),!.
contract_abbrevs_l([],[]).

is_expansion(X,Y) :- abbreviation(Y,X1),instance(X,X1),X=X1,!.
is_expansion(X,X).

contract_vars(X,X) :- var(X),!.
contract_vars(all(X,H),all(N,H1)) :-
	var_with_type(X,N),
	contract_vars(H,H1),!.
contract_vars(ex(X,H),ex(N,H1)) :-
	var_with_type(X,N),
	contract_vars(H,H1),!.
contract_vars(forall(XL,H),forall(N,H1)) :-
	var_with_type_l(XL,N),
	contract_vars(H,H1),!.
contract_vars(exist(XL,H),exist(N,H1)) :-
	var_with_type_l(XL,N),
	contract_vars(H,H1),!.
contract_vars(X,Y) :- X=..[Op|Arg],
	contract_vars_l(Arg,Arg1),
	Y=..[Op|Arg1],!.

contract_vars_l([F|Arg],[F1|Arg1]) :- contract_vars(F,F1),
	contract_vars_l(Arg,Arg1),!.
contract_vars_l([],[]).

var_with_type(X,X) :- get_attribute(X,Typ),
	get_var_info(X,name,Y),
	get_var_root(Y,N),
	var_has_typterm(N,Typ1),
	remove_as(Typ1,Typ),
	!.
var_with_type(X,(X as Type)) :-
	get_attribute(X,and([],Typ1)),
	contract_vars(Typ1,Type),!.

var_with_type_l([F|Arg],[F1|Arg1]) :- var_with_type(F,F1),
	var_with_type_l(Arg,Arg1),!.
var_with_type_l([],[]).

/* Explizite Definitionen */
let(_=G) :- var(G),!,ilf_warning("let: Right hand side of definition cannot be a variable."),fail.
let(F=G) :- term_variables(F,VF),term_variables(G,VG),
	not all_vars_used(VG,VF),!,
	if_warning("let: All variables of right hand side of definition must occur left."),!,fail.
let(F=_) :- F=..[_|Arg], not is_varlist(Arg),!,
	ilf_warning("let: Arguments of left hand side must be variables"),fail.
let(F=_) :- functor(F,Op,N),functor(FF,Op,N),
	(abbreviation(FF,_);user_type(FF,_);local_type(FF,_)),!,
	ilf_warning("let: %w already defined.",[FF]),fail.
let(F=G) :- 
	expand_fla(G,G1),user_type(G1,TG),
	make_working_domain,
	getval(current_domain,Dom),
	setval(current_domain,standard), % Hack fuer Benutzung in pad
	safe_transaction(make_user_type(func,F,TG,_)),
	term_variables(F,V),
	(V=[],Def=(F=G);Def=forall(V,(F=G))),!,
	functor(F,Op,N),
	safe_transaction(make_user_type(formula,let_def(Op/N),Def,_)),
	printf("Formula let_def(%w/%w) : %w added to domain %w\n",[Op,N,Def,standard]),
	make_background_user_preds,
	compile_pred(user_type/2),
	compile_pred(user_widens/2),
	setval(current_domain,Dom),!.

all_vars_used([X|V],VL) :- strict_member(X,VL),!,all_vars_used(V,VL),!.
all_vars_used([],_).

is_varlist([X|V]) :- var(X),!,is_varlist(V),!.
is_varlist([]).

/*
 * Hauptschleife des Parsing
 */

parse(File) :-
    open(File,read,Str), % kann verschachtelt auftreten -> Str als Variable
	parse_stream(Str).

parse_stream(Str) :-
    repeat,
    not(( 
	  once((read(Str,Term); exit_block(parse_error))),
	  (
	   Term = end_of_file,!,fail
	  ; 
	   parse_term(Term), write(".")
	  ;
	   exit_block(parse_error)
	  )  
	 )),

    close(Str),
    nl,!.
    

/*
 * Termabhaengige Parsing-Prozeduren
 */

parse_term(?- op(P,A,Op)) :- op(P,A,Op),
	getval(current_domain,D),
	insert_clause(operator(D,P,A,Op)),!.
parse_term(?- Directive) :- !,
    (
    call(Directive)
    ;
    printf("ILF ERROR: Directive %w failed\n",[Directive]),!,fail
    ).
parse_term(:- Directive) :- !,
    parse_term(?- Directive).


parse_term(begin Theory) :- !,
    parse_term(Theory).

parse_term(domain DomainName) :- !,
    (
     ilf_debug((writeq(domain_item(domain,DomainName,_,_)), nl)),
     (make_user_type(domain,DomainName,_,_))
     ;
     printf("ILF ERROR parsing domain %w\n",[DomainName]),fail
     ),!.


parse_term(reserve VarListAsTerm for TypTerm) :- !,
    (
     once( convert_varlist(VarListAsTerm,VarListAsList) ),
     no_keywords_in_term(TypTerm),
     is_shorthand(TypTerm,TypTerm1),
     add_as(TypTerm1,TypTermWithAs), 
     baar_unify(TypTermWithAs), % kein remove_as!
     ilf_debug((writeq(reservation(VarListAsList for TypTermWithAs)),nl)),
     assert_reservation_info(VarListAsList,TypTermWithAs)
     ;
     printf("ILF ERROR parsing reserve %w\n",[VarListAsTerm for TypTerm]),fail
     ),!.
    

parse_term(definition Definition) :- !,
    parse_term(Definition).

parse_term(end) :- !.


parse_term(mode Term is TypTerm) :- !,
    (
     once( no_keywords_in_term(Term) ), 
     no_keywords_in_term(TypTerm),
     add_types(Term is TypTerm,TermWithTypes is TypTermWithTypes),
     ilf_debug((writeq(domain_item(mode,TermWithTypes,TypTermWithTypes,_)),nl)),
     (make_user_type(mode,TermWithTypes,TypTermWithTypes,_))
     ;
     printf("ILF ERROR parsing mode %w\n",[Term is TypTerm]),fail
     ),!.
parse_term(type Term is TypTerm) :- !,
    (
     once( no_keywords_in_term(Term) ), 
     no_keywords_in_term(TypTerm),
     add_types(Term is TypTerm,TermWithTypes is TypTermWithTypes),
     ilf_debug((writeq(domain_item(mode,TermWithTypes,TypTermWithTypes,_)),nl)),
     (make_user_type(type,TermWithTypes,TypTermWithTypes,_))
     ;
     printf("ILF ERROR parsing mode %w\n",[Term is TypTerm]),fail
     ),!.
parse_term(mode Term) :- !,
    (
     no_keywords_in_term(Term),
     add_types(Term,TermWithTypes),
     ilf_debug((writeq(domain_item(mode,TermWithTypes,_,_)),nl)),
     (make_user_type(mode,TermWithTypes,_,_))
     ;
     printf("ILF ERROR parsing mode %w\n",[Term]),fail
     ),!.

parse_term(small_mode Term is TypTerm) :- !,
    (
     once( no_keywords_in_term(Term) ), 
     no_keywords_in_term(TypTerm),
     add_types(Term is TypTerm,TermWithTypes is TypTermWithTypes),
     ilf_debug((writeq(domain_item(small_mode,TermWithTypes,TypTermWithTypes,_)),nl)),
     (make_user_type(small_mode,TermWithTypes,TypTermWithTypes,_))
     ;
     printf("ILF ERROR parsing small_mode %w\n",[Term is TypTerm]),fail
     ),!.
parse_term(set_type Term is TypTerm) :- !,
    (
     once( no_keywords_in_term(Term) ), 
     no_keywords_in_term(TypTerm),
     add_types(Term is TypTerm,TermWithTypes is TypTermWithTypes),
     ilf_debug((writeq(domain_item(set_type,TermWithTypes,TypTermWithTypes,_)),nl)),
     (make_user_type(set_type,TermWithTypes,TypTermWithTypes,_))
     ;
     printf("ILF ERROR parsing set_type %w\n",[Term is TypTerm]),fail
     ),!.

parse_term(small_mode Term) :- !,
    (
     no_keywords_in_term(Term),
     add_types(Term,TermWithTypes),
     ilf_debug((writeq(domain_item(small_mode,TermWithTypes,_,_)),nl)),
     (make_user_type(small_mode,TermWithTypes,and([],set),_))
     ;
     printf("ILF ERROR parsing small_mode %w\n",[Term]),fail
     ),!.
parse_term(set_type Term) :- !,
    (
     no_keywords_in_term(Term),
     add_types(Term,TermWithTypes),
     ilf_debug((writeq(domain_item(small_mode,TermWithTypes,_,_)),nl)),
     (make_user_type(set_type,TermWithTypes,and([],set),_))
     ;
     printf("ILF ERROR parsing small_mode %w\n",[Term]),fail
     ),!.
parse_term(pred Term) :- !,
    (
     no_keywords_in_term(Term),
     add_types(Term,TermWithTypes),
     ilf_debug((writeq(domain_item(pred,TermWithTypes,_,_)),nl)),
     (make_user_type(pred,TermWithTypes,_,_))
     ;
     printf("ILF ERROR parsing predicate %w\n",[Term]),fail
     ),!.
    
parse_term(func Term gives TypTerm) :- !,
    (
     once( no_keywords_in_term(Term) ), 
     no_keywords_in_term(TypTerm),
     add_types(Term gives TypTerm,TermWithTypes gives TypTermWithTypes),
     ilf_debug((writeq(domain_item(func,TermWithTypes,TypTermWithTypes,_)),nl)),
     (make_user_type(func,TermWithTypes,TypTermWithTypes,_))
     ;
     printf("ILF ERROR parsing func %w\n",[Term gives TypTerm]),fail
     ),!.


parse_term(struct StructTerm gives TypTerm) :- !,
    (
     once( parse_structterm(StructTerm) ), 
     no_keywords_in_term(TypTerm),
     add_types(StructTerm gives TypTerm,StructTermWithTypes gives TypTermWithTypes),
     StructTermWithTypes =.. [Atom|SelectorDefList],
     ilf_debug((writeq(domain_item(struct,Atom,SelectorDefList,TypTermWithTypes)),nl)),
     (make_user_type(struct,Atom,SelectorDefList,TypTermWithTypes))
     ;
     printf("ILF ERROR parsing structure %w\n",[StructTerm gives TypTerm]),fail
     ),!	.


parse_term(fla NamedFormula) :- !,
    (
     once(( 
	   NamedFormula =.. [':',Name,Formula] ; 
	   Name = unknown, Formula = NamedFormula 
	  )),
	(var(Name) -> 
		get_var_info(Name,name,AName),
		Name=AName,
		ilf_warning("Variable formula name %w replaced by atom\n",[AName])
		;
		true),
     no_keywords_in_term(Formula),
     once(add_types(Formula,FormulaWithTypes)),
     ilf_debug((writeq(domain_item(formula,Name,FormulaWithTypes,_)),nl)),
     make_user_type(formula,Name,FormulaWithTypes,_)
    ;
    	printf("ILF ERROR parsing formula %w\n",[NamedFormula]),!,fail
    ),!	.

parse_term(schema NamedSchema) :- !,
	(
     once(( 
	   NamedSchema =.. [':',Name,Schema] ; 
	   Name = unknown, Schema = NamedSchema
	  )),
	 Schema=schema(_,Fla),
     no_keywords_in_term(Fla),
     once(add_types(Schema,SchemaWithTypes)),
     ilf_debug((writeq(domain_item(schema,Name,SchemaWithTypes,_)),nl)),
     make_user_type(schema,Name,SchemaWithTypes,_)
    ;
    	printf("ILF ERROR parsing schema %w\n",[NamedSchema]),!,fail
    ),!	.
parse_term(Term) :- !,
    printf("ILF Warning: %w unknown for parser.\n",[Term]).



/*
 * Jede Struktur enthaelt mindestens einen Selektor
 */

parse_structterm(StructTerm) :-
    StructTerm =.. [_|SelectorDefList],
    parse_selectordeflist(SelectorDefList).

parse_selectordeflist([(Atom gives TypTerm)|L]) :- 
    !,
    atom(Atom),
    no_keywords_in_term(TypTerm),
    !,parse_selectordeflist(L).
parse_selectordeflist([]) :- !.
parse_selectordeflist([E|_]) :-
	printf(toplevel_output,"ILF ERROR: Illegal selector declaration %w\n",[E]),
	flush(toplevel_output),fail.


/*
 * no_keywords_in_term/1 ueberprueft, ob ein Term einen 
 * in der Liste 'Keywords' enthaltenen Operator enthaelt
 */

no_keywords_in_term(Term) :-
    Keywords = [for, is, gives],
    term_is_correct(Term, Keywords).

term_is_correct(Term,_) :-
    var(Term).
term_is_correct(Term,_) :-
    atomic(Term).
term_is_correct(Term,Keywords) :-
    compound(Term),!,
    Term =.. [Functor|Args],
    not( member(Functor,Keywords) ),!,
    terms_are_correct(Args,Keywords).

terms_are_correct([],_).
terms_are_correct([Term|Terms],Keywords) :-
    term_is_correct(Term,Keywords),
    terms_are_correct(Terms,Keywords).





/*
 * Prozeduren zur Typterm-Ergaenzung bei Variablen:
 *   'add_as' fuegt noch fehlende Typterme gemaess 
 *      a) Quantifizierungen oder
 *      b) Reservierungen ein
 *   'baar_unify' unifiziert Vars mit gleichen Bezeichnern und Typtermen
 *   'remove_as' ersetzt Terme mit 'as' durch Metaterme
 */

:- dynamic is_expl_decl/2.


add_types(Term,TermWithTypes) :-
    add_as(Term,TermWithAs),!,
    retract_all(is_expl_decl(_,_)),!,
    baar_unify(TermWithAs),!,
    remove_as(TermWithAs,TermWithTypes),!.

add_as(Var,Var as TypTermWithTypes) :- get_attribute(Var,TypTerm),!,
	add_as(TypTerm,TypTermWithTypes),
	get_var_info(Var,name,VarId),
	assert(is_expl_decl(VarId,TypTermWithTypes)),!.
add_as(Var,Var as TypTerm) :-
    var(Var),!,
    get_var_info(Var,name,VarId),
    (is_expl_decl(VarId,TypTerm) ;
     get_var_root(VarId,BaseVarId),var_has_typterm(BaseVarId,TypTerm) ;
     printf("ILF Warning: Variable %w has no type, is assumed to be set.\n",[VarId]),TypTerm=and([],set)
     ),!.

add_as(Var as TypTerm,Var as TypTermWithTypes) :- !,
    add_as(TypTerm,TypTermWithTypes),
    get_var_info(Var,name,VarId),
    assert(is_expl_decl(VarId,TypTermWithTypes)).

add_as(all(Var,Formula),all(Var as TypTerm,FormulaWithTypes)) :-
    var(Var),!,
    get_var_info(Var,name,VarId),
    (is_expl_decl(VarId,TypTerm) ;
     get_var_root(VarId,BaseVarId),var_has_typterm(BaseVarId,TypTerm) ;
     printf("ILF Warning: Variable %w has no type, is assumed to be set.\n",[VarId]),TypTerm = and([],set)
     ),
    add_as(Formula,FormulaWithTypes).
    
add_as(all(Var as TypTerm,Formula),all(Var as TypTermWithTypes,FormulaWithTypes)) :- !,
    add_as(Var as TypTerm,Var as TypTermWithTypes),
    add_as(Formula,FormulaWithTypes).

add_as(ex(Var,Formula),ex(Var as TypTerm,FormulaWithTypes)) :-
    var(Var),!,
    get_var_info(Var,name,VarId),
    (is_expl_decl(VarId,TypTerm) ;
     get_var_root(VarId,BaseVarId),var_has_typterm(BaseVarId,TypTerm) ;
     printf("ILF Warning: Variable %w has no type, is assumed to be set.\n",[VarId]),TypTerm = and([],set)
     ),
    add_as(Formula,FormulaWithTypes).

add_as(ex(Var as TypTerm,Formula),ex(Var as TypTermWithTypes,FormulaWithTypes)) :- !,
    add_as(Var as TypTerm,Var as TypTermWithTypes),
    add_as(Formula,FormulaWithTypes).

add_as(CompoundTerm,CompoundTermWithTypes) :-
    CompoundTerm =.. [Functor|Args],
    add_asl(Args,ArgsWithTypes),
    CompoundTermWithTypes =.. [Functor|ArgsWithTypes].

add_asl([],[]).
add_asl([Term|Terml],[TermWithTypes|TermlWithTypes]) :-
    add_as(Term,TermWithTypes),
    add_asl(Terml,TermlWithTypes).


/*
 * Enthaelt ein Term nach 'add_as' Variablen, die die gleichen Bezeichner
 * und Typterme besitzen, so werden diese unifiziert.
 * Variablen mit gleichen Bezeichnern und verschiedenen Typtermen 
 * erzeugen eine Fehlermeldung (check_consistency/1).
 * (auf Wunsch von Thomas Baar)
 *
 */

baar_unify(Term) :-
    get_varlist(Term,VarList),!,
    check_consistency(VarList),!,
    unify_vars(Term,VarList).

get_varlist(Term,[]) :-
    atom(Term),!.
get_varlist(Var as TypTerm,[[Var,VarId,TypTerm]|VarList]) :- !,
    get_var_info(Var,name,VarId),
    get_varlist(TypTerm,VarList),!.
get_varlist(CompoundTerm,VarList) :-
    CompoundTerm =.. [_|Args],
    get_varlistl(Args,VarList),!.

get_varlistl([],[]).
get_varlistl([Term|Terms],VarList) :-
    get_varlist(Term,TermVarList),
    get_varlistl(Terms,TermsVarList),
    append(TermVarList,TermsVarList,VarList),!.


check_consistency([]) :- !.
check_consistency([[_,VarId,TypTerm]|VarList]) :- !,
    check_varid([VarId,TypTerm],VarList),
    check_consistency(VarList).

check_varid(_,[]) :- !.
check_varid([VarId1,TypTerm1],[[_,VarId2,_]|VarList]) :-
    VarId1 \== VarId2,!,
    check_varid([VarId1,TypTerm1],VarList),!.
check_varid([VarId1,TypTerm1],[[_,VarId2,TypTerm2]|VarList]) :-
    ( VarId1 == VarId2, 
      variant(TypTerm1,TypTerm2),
      check_varid([VarId1,TypTerm1],VarList)
    ) ;
    ( printf("ILF ERROR Identifier %w has different typeterms %w and %w.\n",[VarId1,TypTerm1,TypTerm2]),!,fail
    ).
       
    

unify_vars(Term,_) :-
    atom(Term).
unify_vars(Var as TypTerm,VarList) :- !,
    get_var_info(Var,name,VarId),
    member([Var,VarId,TypTerm],VarList),
    unify_vars(TypTerm,VarList).
unify_vars(CompoundTerm,VarList) :-
    CompoundTerm =.. [_|Args],
    unify_varsl(Args,VarList).

unify_varsl([],_).
unify_varsl([Term|Terms],VarList) :-
    unify_vars(Term,VarList),
    unify_varsl(Terms,VarList).


remove_as(Term,Term) :-
    atom(Term).
remove_as(Var as TypTerm,Var) :- !,
    remove_as(TypTerm,TypTermWithoutAs),
    ( free(Var) -> add_attribute(Var,TypTermWithoutAs) ; true ). 
remove_as(CompoundTerm,CompoundTermWithoutAs) :-
    CompoundTerm =.. [Functor|Args],
    remove_asl(Args,ArgsWithoutAs),
    CompoundTermWithoutAs =.. [Functor|ArgsWithoutAs].

remove_asl([],[]).
remove_asl([Term|Terms],[TermWithoutAs|TermsWithoutAs]) :-
    remove_as(Term,TermWithoutAs),
    remove_asl(Terms,TermsWithoutAs).
    
/*
 * Hilfsprozeduren
 */


assert_reservation_info([],_).
assert_reservation_info([Var|RestOfVarList],TypTerm) :-
    get_var_info(Var,name,VarId),
    retract_all(var_has_typterm(VarId,_)),
    assert(var_has_typterm(VarId,TypTerm)),
    assert_reservation_info(RestOfVarList,TypTerm).


convert_varlist(Var,[Var]) :-
    var(Var).
convert_varlist(VarListAsTerm,VarListAsList) :-
    VarListAsTerm =.. [',',Var,SubVarListAsTerm],
    convert_varlist(SubVarListAsTerm,SubVarListAsList),
    append([Var],SubVarListAsList,VarListAsList).

    
convert_attributlist([],[]).
convert_attributlist(AttributListAsTerm,AttributListAsList) :-
    AttributListAsTerm =.. [',',Attribut,SubAttributListAsTerm],
    convert_attributlist(SubAttributListAsTerm,SubAttributListAsList),
    append([Attribut],SubAttributListAsList,AttributListAsList).
convert_attributlist(Attribut,[Attribut]).

sort_attributlist(AttributList,SortedAttributList) :-
    make_list_to_sort(AttributList,ListToSort),
    keysort(ListToSort,SortedListToSort),
    make_sorted_attribut_list(SortedListToSort,SortedAttributList).

make_list_to_sort([],[]) :- !.
make_list_to_sort([non(Attr)|Rest1],[(Attr,b)-non(Attr)|Rest2]) :- !,
    make_list_to_sort(Rest1,Rest2).
make_list_to_sort([Attr|Rest1],[(Attr,a)-Attr|Rest2]) :- !,
    make_list_to_sort(Rest1,Rest2).

make_sorted_attribut_list([(Attr,b)-non(Attr)|Rest1],[non(Attr)|Rest2]) :- !,
    make_sorted_attribut_list(Rest1,Rest2).
make_sorted_attribut_list([(Attr,a)-Attr|Rest1],[Attr|Rest2]) :- !,
    make_sorted_attribut_list(Rest1,Rest2).
make_sorted_attribut_list([],[]) :- !.


get_var_root(Name,Root) :-
	term_string(Name,NameS),
	last_underscore_pos(NameS,Pos),
	(Len is Pos-1),
	substring(NameS,1,Len,RootS),
	concat_strings(RootS,"'",RootS1),
	term_string(Root,RootS1),!.
get_var_root(Name,Name).
	
last_underscore_pos(String,Pos) :- 
	string_length(String,LString),
	substring(String,Pos,1,"_"),
	(L is LString - Pos),
	(Pos1 is Pos+1),
	substring(String,Pos1,L,String1),
	not substring(String1,"_",_),!.

make_typed(X,Y) :- open("",string,Stream),
	printf(Stream,"%Dw",[X]),
	define_read_macros,
	seek(Stream,0),
	read(Stream,YY),
	erase_read_macros,
	close(Stream),!,
	add_types(YY,Y),!.

read_typed(X) :- read(Y),make_typed(Y,X),!.

/**
 * Ende des neuen Parsers
 **/

/* verschachteltes load_th(T) wird zu load_th(uncomp,T) bei dem die
 * Praedikate nicht kompiliert werden, sonst zu load_th(comp,T).
 * bei load_th(comp,T) werden im Vergleich zu uncomp-Variante zusaetzlich
 * macros gesetzt und zum Schluss kompiliert
 */
 
load_th(T):- 
	tmp_nested_load_th,!,
	load_th(uncomp,T),!.
load_th(T):- asserta(theory_file(ilf_th_file_bottom)),
	block(load_th(comp,T),parse_error,load_th_err_hdl),!.

load_th_err_hdl:-
	kb_reservations,
	erase_read_macros,
	compile_pred(user_type/2),
	compile_pred(user_widens/2),
	retract_theory_file,
	retract_all(tmp_nested_load_th).

retract_theory_file :- retract(theory_file(X)),X=ilf_th_file_bottom,!.
retract_theory_file.

load_th(Fl,T0) :- atom(T0),!,
	concat_string(["th/", T0, ".th"],S),
	get_right_file(S,TS),
	load_th(Fl,TS),!.

load_th(_,F) :- theory_file(F),
	write(F),write(" already loaded."),nl,!.
load_th(Fl,TS) :-
	asserta(theory_file(TS)),
	learn_from(Fl,TS),
	!.


learn_from(comp,TS) :- 
	assert(tmp_nested_load_th),
	make_working_domain,
	define_read_macros,
	learn_from(uncomp,TS),
	erase_read_macros,
	compile_pred(user_type/2),
	compile_pred(user_widens/2),
	make_background_user_preds,
	retract(tmp_nested_load_th),
	!.
	
learn_from(uncomp,TS) :- bang_register(transaction_active,1),!,
	parse(TS),!.
	
learn_from(uncomp,TS) :- transaction(learn_from(uncomp,TS)),kb_reservations.

make_background_user_preds :- ilf_state(experts,off),!.
make_background_user_preds :- (0 : database_changed), !.



% load_th_alw/1 ist wie load_th, nur dass Theoriefile schon mal
% geladen sein kann
% keine Ahnung, ob was schlimmes passieren kann    T.Baar
% dafuer ist z.Z. der Nutzer verantwortlich
load_th_alw(F) :-
	(
	 theory_file(F) , retract_all(theory_file(F))
	;
	 true
	),
	load_th(F).
	 

/* unify_by_name(VarList,Varstruct) unifiziert Variable in Varlist mit denen mit gleichem Namen in Varstruct */
unify_by_name(_,[]).
unify_by_name([X|L],V) :- get_attribute(X,A),!,
	term_variables(A,AV),
	get_var_info(X,name,Name),
	(member([Name|X],V);true),
	unify_by_name(AV,V),
	unify_by_name(L,V),!.
unify_by_name([X|L],V) :- get_var_info(X,name,Name),
	member([Name|X],V),unify_by_name(L,V),!.
unify_by_name([_|L],V) :- unify_by_name(L,V),!.
unify_by_name([],_).

put_in_domain(_,end_of_file) :- !.
put_in_domain(_,X) :- ilf_debug(writeln(X)),fail.
put_in_domain(_,end(domain)) :- !.
put_in_domain(_,?-(X)) :- !,X,!,fail.
put_in_domain(Name,':'(FName,all(X,F))) :- not var(X),
	insert_schema(Name,FName,all(X,F)),!,fail.
put_in_domain(Name,':'(FName,Fla)) :- !,extend_types(Name,Fla),
	insert_clause(formula(Name,FName,fla,Fla)),!,fail.
put_in_domain(Name,type(X)) :- 
	insert_clause(type(Name,X)),!,fail.
put_in_domain(Name,below(P,Q)) :- insert_clause(below(Name,P,Q)),!,fail.
put_in_domain(Domain,reserve(for(X,Type))) :- get_var_info(X,name,XName),
	retract_all(reserved_var(_,XName,_)),
	assert(reserved_var(Domain,XName,Type)),!,fail.
put_in_domain(Domain,reserve(for(X,Type))) :- 
	retract_all(reserved_var(_,X,_)),
	assert(reserved_var(Domain,X,Type)),!,fail.
put_in_domain(Name,define(':'(Symbols,Decl))) :- 
	definition_list(Symbols,Decl,L),
	insert_definitions(Name,L),
	!,fail.
put_in_domain(Name,interprets(Int,from(Old,with(Source,Ren)))) :- 
	make_interpret(Name,Int,Source,Old,Ren),!,fail.
put_in_domain(Name,Term) :- write("Don't know what to do with "),display(Term),
	write(" in "),write(Name),nl,!,fail.

extend_types(Domain,F) :- term_variables(F,VL),
	add_vartype_l(Domain,VL),!.

add_vartype(Domain,X) :- free(X),get_var_info(X,name,XName),
	get_reserved_type(Domain,XName,T),
	add_attribute(X,T),!.
add_vartype(_,_).

add_vartype_l(Domain,[X|V]) :- add_vartype(Domain,X),add_vartype_l(Domain,V),!.
add_vartype_l(_,[]).

get_reserved_type(Domain,Name,Typ) :- 
	get_var_root(Name,Root),
	reserved_var(Domain,Root,Typ),!.
	
	
get_attribute(_{thman : At},A) :- -?-> A=At.


schema(all(F,_)) :- not var(F),!.

insert_schema(_,_,all(':'(X,_),_)) :- var(X),!,fail.
insert_schema(Name,FName,F) :- schema_cont(Name,F,C,Subst),
	extend_types(Name,C),
	insert_clause(schema(Name,FName,C,Subst)),!.

schema_cont(Domain,F,C,Subst) :-
	schema_fla(F,SF,Types),
	schema_clause(Domain,SF,Types,C,Subst).

schema_fla(all(X,F),all(X,F),[]) :- var(X),!.
schema_fla(all((X : T),F),all((X : T),F),[]) :- var(X),!.
schema_fla(all(D,F),SF,[D|DL]) :- schema_fla(F,SF,DL),!.
schema_fla(F,F,[]).

schema_clause(_,X,_,X,[]) :- var(X),!.
schema_clause(Domain,F,Types,A,[(A,Op,Arg,ArgT)]) :- F=..[Op|Arg],
	length(Arg,N),
	length(ArgT,N),
	schema_type(Domain,Types,Op,ArgT,T),
	add_attribute(A,T),!.
schema_clause(Domain,F,Types,C,Subst) :-
	F=..[Op|Arg],
	schema_clause_l(Domain,Arg,Types,CL,Subst),
	C=..[Op|CL],!.

schema_clause_l(Domain,[F|FL],Types,[C|CL],Subst) :-
	schema_clause(Domain,F,Types,C,SubstF),
	schema_clause_l(Domain,FL,Types,CL,SubstL),
	append(SubstF,SubstL,Subst),!.
schema_clause_l(_,[],_,[],[]).

schema_type(_,Types,Op,ArgT,T) :- member(':'(Op,(ArgT -> T)),Types),!.
schema_type(_,Types,Op,[],T) :- member(':'(Op,T),Types),!.
schema_type(Domain,_,Op,[],T) :- !,get_var_root(Op,Root),
	reserved_var(Domain,Root,T),!.
schema_type(Domain,_,Op,ArgT,T) :- get_var_root(Op,Root),
	reserved_var(Domain,Root,(ArgT -> T)),!.

copy(from(Cp,into(Source,with(Dest,Ren)))) :-!,
	copy(Cp,Source,Dest,Ren),!.
copy(from(Cp,with(Source,Ren))) :- !,
	getval(current_domain,(Dest,VDest)),
	term_variables((Dest,Source,Ren),VS),
	unify_by_name(VS,VDest),
	copy(Cp,Source,Dest,Ren),
	!.
copy(from(Cp,into(Source,Dest))) :- !,
	copy(Cp,Source,Dest,true),!.
copy(from(Cp,Source)) :- !,getval(current_domain,(Dest,VDest)),
	term_variables((Dest,Source),VS),
	unify_by_name(VS,VDest),
	copy(Cp,Source,Dest,true),!.

copy(all,Source,Dest,Ren) :- !,
	copy(types,Source,Dest,Ren),
	copy(definitions,Source,Dest,Ren),
	copy(formulae,Source,Dest,Ren),!.
copy(Cp,Source,Dest,Ren) :- !,
	Cp=..[Kat|Imps],
	(Imps=[Imps1] -> body_list(Imps1,ImpsL);ImpsL=[]),
	copy(Kat,ImpsL,Source,Dest,Ren),!.

copy(types,[],Source,Dest,Ren) :- !,
	(
	setof(T,type(Source,T),TL),
	types_and_vars(TL,TTL),
	renamed(TTL,TTL1,Ren),
	types_and_vars(TL1,TTL1),
	insert_types(Dest,TL1)
	;
	true
	),!.
copy(types,ImpsL,Source,Dest,Ren) :- !,
	(
	setof(T,(type(Source,T),member(T,ImpsL)),TL),
	types_and_vars(TL,TTL),
	renamed(TTL,TTL1,Ren),
	types_and_vars(TL1,TTL1),
	insert_types(Dest,TL1)
	;
	true
	),!.

copy(definitions,[],Source,Dest,Ren) :- !,
	(
	setof((N,C),definition(Source,N,C),TL),
	definitions_and_vars(TL,TTL),
	renamed(TTL,TTL1,Ren),
	definitions_and_vars(TL1,TTL1),
	insert_definitions(Dest,TL1)
	;
	true
	),!.
copy(types,ImpsL,Source,Dest,Ren) :- !,
	(
	setof((N,C),(definition(Source,N,C),member(N,ImpsL)),TL),
	renamed(TL,TL1,Ren),
	insert_definitions(Dest,TL1)
	;
	true
	),!.

copy(formulae,[],Source,Dest,Ren) :- !,
	(
	setof((N,C),formula(Source,N,fla,C),TL),
	copy_formula_l(TL,Dest,Ren)
	;
	true
	),!.
copy(formulae,ImpsL,Source,Dest,Ren) :- !,
	(
	setof((N,C),(formula(Source,N,fla,C),member(N,ImpsL)),TL),
	copy_formula_l(TL,Dest,Ren)
	;
	true
	),!.

make_interpret(Name,Int,Source,all,Ren) :- !,
	insert_clause((
	formula(Name,FName,fla,F) :- active_interpretation(Name,Int),
		formula(Source,FName1,F1),
		translate_formula(FName1,FName,Ren),
		translate_formula(F1,F,Ren)
	)),!.
make_interpret(Name,Int,Source,B,Ren) :-
	body_list(B,BL),
	insert_clause((
	formula(Name,FName,fla,F) :- active_interpretation(Name,Int),
		formula(Source,FName1,fla,F1),
		member(FName1,BL),
		translate_formula(FName1,FName,Ren),
		translate_formula(F1,F,Ren)
	)),!.


activate_interpretation(Dom,I) :- assert(active_interpretation(Dom,I)),!.

deactivate_interpretation(Dom,I) :- retract_all(active_interpretation(Dom,I)),!.

insert_types(Dest,[T|TL]) :- type(Dest,T),!,insert_types(Dest,TL),!.
insert_types(Dest,[T|TL]) :- insert_clause(type(Dest,T)),!,
	insert_types(Dest,TL),!.
insert_types(_,[]).

types_and_vars([T|TL],[(_ : T)|VL]) :- types_and_vars(TL,VL),!.
types_and_vars([],[]).

definitions_and_vars([D|DL],[V|VL]) :- definition_clause(D,V),
	definitions_and_vars(DL,VL),!.
definitions_and_vars([],[]).

definition_clause((Op,(ArgT ->T)),((F : T) :- B)) :-
	definition_body(ArgT,B,V),
	F=..[Op|V],!.
definition_clause((Op,T),(Op : T)).

definition_body([T],(X : T),[X]) :- !.
definition_body([T|TL],((X : T),B),[X|L]) :- definition_body(TL,B,L),!.

definition_list((S1,S2),Decl,L) :- 
	definition_list(S1,Decl,L1),
	definition_list(S2,Decl,L2),
	append(L1,L2,L),!.
definition_list(S,Decl,[(S,Decl)]).

insert_definitions(Dest,[(N,C)|TL]) :- insert_1_definition(Dest,N,C),
	insert_definitions(Dest,TL),!.
insert_definitions(_,[]).

insert_1_definition(Dest,(S1,S2),C) :- !,insert_1_definition(Dest,S1,C),
	insert_1_definition(Dest,S2,C),!.
insert_1_definition(Dest,S,D) :- check_definition(Dest,S,D),
	insert_clause(definition(Dest,S,D)),!.

check_definition(Dest,S,D) :- definition(Dest,S,D1),incompatible_def(D,D1),
	printf("ILF ERROR: Definitions %w and %w for %w in %w incompatible!\n", [D1,D,S,Dest]),!,fail.
check_definition(_,_,_).

incompatible_def((A1 -> B1),(A1 -> B2)) :- not B1 ==B2,!.

copy_formula(N,F,Dest,Ren) :- renamed(N,N1,Ren),
	translate_formula(F,F1,Ren),
	(retract_clause(formula(Dest,N1,_,_));true),!,
	insert_clause(formula(Dest,N1,fla,F1)),!.

translate_formula(F,F2,Ren) :- renamed(F,F1,Ren),
	term_variables(F1,V1),
	copy_term((F1,V1),(F2,V2)),
	rename_types(V1,V2,Ren),!.

rename_types([X|V],[U|V1],Ren) :- get_attribute(X,A),renamed(A,A1,Ren),
	add_attribute(U,A1),
	rename_types(V,V1,Ren),!.
rename_types([_|V],[_|V1],Ren) :- rename_types(V,V1,Ren),!.
rename_types([],[],_).

copy_formula_l([(N,F)|FL],Dest,Ren) :- copy_formula(N,F,Dest,Ren),
	copy_formula_l(FL,Dest,Ren),!.
copy_formula_l([],_,_).


make_type_clauses(Name,[],Dom,Ren,CL) :- 
	make_type_clauses(Name,[_],Dom,Ren,CL),!.
make_type_clauses(Name,[T|L],Dom,[],
	[(type(Name,T) :- type(Dom,T))|CL]
	) :- (L=[] -> CL=[];make_type_clause(Name,L,Dom,[],CL)),!.
make_type_clauses(Name,[T|L],Dom,Ren,
	[
	(type(Name,T) :- type(Dom,T1),renamed(T1,T,Ren))
	|CL]
	) :- (L=[] -> CL=[];make_type_clauses(Name,L,Dom,Ren,CL)),!.

make_definitions_clauses(Name,[],Dom,Ren,CL) :- 
	make_definitions_clauses(Name,[_],Dom,Ren,CL),!.
make_definitions_clauses(Name,[T|L],Dom,[],
	[(definition(Name,T,D) :- definition(Dom,T,D))|CL]
	) :- (L=[] -> CL=[];make_definitions_clause(Name,L,Dom,[],CL)),!.
make_definitions_clauses(Name,[T|L],Dom,Ren,
	[
	(definition(Name,T,D) :- definition(Dom,T1,D1),
		renamed(T1,T,Ren),
		renamed(D1,D,Ren))
	|CL]
	) :- (L=[] -> CL=[];make_definitions_clauses(Name,L,Dom,Ren,CL)),!.

make_formulae_clauses(Name,[],Dom,Ren,CL) :- 
	make_formulae_clauses(Name,[_],Dom,Ren,CL),!.
make_formulae_clauses(Name,[T|L],Dom,[],
	[(formula(Name,T,D) :- formula(Dom,T,D))|CL]
	) :- (L=[] -> CL=[];make_formulae_clause(Name,L,Dom,[],CL)),!.
make_formulae_clauses(Name,[T|L],Dom,Ren,
	[
	(formula(Name,T,D) :- formula(Dom,T1,D1),
		renamed(T1,T,Ren),
		renamed(D1,D,Ren))
	|CL]
	) :- (L=[] -> CL=[];make_formulae_clauses(Name,L,Dom,Ren,CL)),!.

/* renamed(T1,T2,L) ueberfuehrt T1 in T2 mit Renaming Ren. T1 oder T2 muss Variable sein */

renamed(X,Y,_) :- var(X),var(Y),!,X=Y.
renamed(X,Y,Ren) :- var(X),!,reverse_ren(Ren,Ren1),renamed(Y,X,Ren1),!.
renamed(X,Y,Ren) :- 
	in_body(as(X,Y1),Ren),!,
	do_rename(X,Y1,Ren,Y).

do_rename(_,failed,_,_) :- !,fail.
do_rename(X,unchanged,_,X) :- var(X),!.
do_rename(X,unchanged,Ren,Y) :- X=..[Op|Arg],
	renamed_l(Arg,Arg1,Ren),Y=..[Op|Arg1],!.
do_rename(_,Y1,Ren,Y) :-
	specials2vars(Y1,Y,{},TL,VL),
	renamed_l(TL,TL1,Ren),
	VL=TL1,!.


renamed_l([E1|L1],[E2|L2],Ren) :- renamed(E1,E2,Ren),renamed_l(L1,L2,Ren),!.
renamed_l([],[],_).

reverse_ren([[S1,S2]|L],[[S2,S1]|LL]) :- reverse_ren(L,LL),!.
reverse_ren([],[]).

in_body(X,B) :- term_variables(B,VB),copy_term((B,VB),(B1,VB1)),
	transfer_attributes(VB,VB1),
	!,in_body1(X,B1).
	
in_body1(X,(X,_)).
in_body1(X,(_,Y)) :- in_body1(X,Y).
in_body1(X,X).

/******   Anfang Erzeugung der Codierung fuer die Typen  ***/

:- dynamic
	attrib_par/3,
	is_leaf/1,
	is_node/2,
	is_mode/1,
	is_below/2,
	leafs_below/2,
	m_term/2,
	mg_attribute/2,
	node_fan/2,
	type_attribute/2,
	type_term/2.


 
 /* Termrepraesentation von Mengen nach Mellish */

:- dynamic(r/2).

/* Das Praedikat est_type_term baut aus den Eintragen in der Wissensbasis sich
 * dynamisch eine Typhierarchie auf bzw. die Termrepraesentation dieser
 * Typhierarchie
 * Gespeichert werden diese Erkenntnisse in type_term/2 in der Datenbank
 * Achtung: type_term(Var,_) kann fehlschlagen, deshalb besser current_predicate
 *          zum Testen verwenden!!!
 *
 * Zusaetzlich wird zu jedem type_term-Fakt der symmetrische Fakt
 * term_type abgespeichert
 * sowie ein fakt type_term_pl der mit type_term uebereinstimmt aber
 * in dem Variablen keine Metaterme mehr sind   T.Baar
 */
 /* Oberster Typ ist set. 
 * Darunter gibt es auf jeden Fall small und darunter element_of.
 * Alle small_types liegen unter small so dass gesichert werden kann, dass
 * Variable vom Typ small_type nur mit solchen Termen belegt werden koennen.
 * element_of ist ein vorbeugend vorgesehener small_type. Es ist der Werttyp
 * aller Typwertigen Skolemfunktionen.
 * Da nur Typvariable mit kleinstem Typ small_type auftreten duerfen, 
 * reicht das. Andere Typkonstruktoren koennen z.Z. nicht codiert werden
 */


est_type_term :- safe_transaction(type_attributes),fail.
/* Sonderfall: Wenn is_below fehlschlaegt, gibt es nur einen Typ, da die Hierarchie als zusammenhaengend vorausgesetzt wird */
est_type_term :- not is_below(_,_),!,
	type_attribute(P,_), 
	P=..[_|Arg],
	retract_all(type_term(_,_)),
	(Arg=[],ilf_state(typed_mode,typed) -> ilf_warning("Working with untyped theory in typed mode!?",[]),TT=_;TT=([]-Arg)),
	safe_transaction(forgetting_typeterms),
	safe_transaction(insert_clause(type_term(P,TT))),
	assert(type_term(P,TT)),
	(Arg=[] -> 
		assert(type_term_pl(P,_))
		;
		copy_term(dum(P,Arg),dum(Ppl,Argpl)),
		assert(type_term_pl(Ppl,[] - Argpl))
	),
	assert(term_type(TT,P)),!.
est_type_term :- top_sort(is_below(X,Y),X,Y),fail.
est_type_term :- make_leafs_below(is_below(X,Y),X,Y),fail.
est_type_term :- make_separable(is_below(X,Y),X,Y),fail.
est_type_term :- make_short_codes,fail.
est_type_term :- retract_all(type_term(_,_)),
	safe_transaction(forgetting_typeterms),
	fail.
est_type_term :- max_list_length(LN,VN),
	length(LT,LN),
	length(VT,VN),
	type_attribute(T,A),
	mg_attribute(A,N),    
	short_code(N,LT-_),
	attrib_par(A,N,VT),
	assert(type_term(T,(LT-VT))),
	fail.
est_type_term :- simplify_type_term,fail.
est_type_term :- type_term(T,U),
	safe_transaction(insert_clause(type_term(T,U))),
	assert(term_type(U,T)),
	copy_term(dum(T,U),dum(Tpl,Upl)),
	assert(type_term_pl(Tpl,Upl)),
	fail.
est_type_term :- asserta((type_term(V,T) :- var(V),!,type_term(element_of(V),T),!)),
	asserta((type_term_pl(V,T) :- var(V),!,type_term_pl(element_of(V),T),!)),
	fail.
/*est_type_term :-
	max_list_length(LN,VN),
	length(LT,LN),
	length(VT,VN),
	type_attribute(T,A),
	mg_attribute(A,N),    
	short_code(N,LT-_),
	attrib_par(A,N,VT),
	safe_transaction(insert_clause(type_term(T,(LT-VT)))),
	assert(type_term(T,(LT-VT))),
	copy_term(dum(T,LT,VT),dum(Tpl,Lpl,Vpl)),
	assert(type_term_pl(Tpl,(Lpl-Vpl))),
	assert(term_type((LT-VT),T)),
	fail.
*/est_type_term :-
	assert((type_term(Skol,T) :- not functor(Skol,element_of,_), type_term(element_of(Skol),T),!)),
	assert((type_term_pl(Skol,T) :- not functor(Skol,element_of,_), type_term_pl(element_of(Skol),T),!)),
	assert((type_term(Type,_) :- term_string(Type,TypeS), ilf_error(["type_term: failed for Type ", TypeS]))),
	assert((type_term_pl(Type,_) :- term_string(Type,TypeS), ilf_error(["type_term_pl: failed for Type ", TypeS]))).


simplify_type_term :-
	simplify_hierarchy,simplify_nopars.

simplify_nopars :- type_term(_,(_ - [_|_])),!.
simplify_nopars :- retract(type_term(U,V-_)),assert(type_term(U,V)),fail.
simplify_nopars.

simplify_hierarchy :- type_term(_,U - _),not var(U),U=[_,_|_],!.
simplify_hierarchy :- retract(type_term(T,[X] - P)),
	assert(type_term(T,X-P)),fail.
simplify_hierarchy.


list_term(X,_,X) :- var(X),!.
list_term([X|L],Op,T) :- list_term(L,Op,TL),T=..[Op,X,TL],!.

max_list_length(_,_) :- new_hierarchy,attrib_par([],Top,_),
	rebuild_below(Top),
	setval(lcL,0),
	setval(lcV,0),
	fail.
max_list_length(_,_) :- attrib_par(_,N,LV),
	short_code(N,LL-[]),
	length(LL,NL),
	once(length(LV,NV)),
	getval(lcL,NNL),
	(NNL < NL -> setval(lcL,NL);true),
	getval(lcV,NNV),
	(NNV < NV -> setval(lcV,NV);true),
	fail.
max_list_length(NL,NV) :- getval(lcL,NL),getval(lcV,NV),!.

type_attributes :- retract_all(type_attribute(_,_)),fail.
type_attributes :- assert(type_attribute(set,[])),
	small_attributes,
	fail.
type_attributes :- user_widens(M,_),make_var_attrib(and([],M)),fail.
type_attributes :- retract_all(mg_attribute(_,_)),setval(mg,0),fail.
type_attributes :- type_attribute(_,A),
	not (type_attribute(_,A1),instance(A,A1),
		not variant(A1,A)
	),
	not (mg_attribute(A2,_),variant(A2,A)),
	getval(mg,N),
	assert(mg_attribute(A,N)),
	incval(mg),fail.
type_attributes :- not mg_attribute([],_),getval(mg,N),
	assert(mg_attribute([],N)),
	incval(mg),fail.
type_attributes :- retract_all(is_below(_,_)),fail.
type_attributes :- mg_attribute(A1,N1),
		mg_attribute(A2,N2),
		immediate_below(A1,A2),	
		make_note(is_below(N1,N2)),fail.
type_attributes.

small_attributes :- not uses_small_types,!.
small_attributes :- assert(type_attribute(small,[small])),
	assert(type_attribute(element_of(X),[in(X)])).

uses_small_types :- user_type(_,and([],small_type)),!.
uses_small_types :- user_type(T,_),term_variables(T,Arg),
	with_type_l(Arg,and(_,small_type)),!.

with_type_l([T|_],Typ) :- get_attribute(T,Typ),!.
with_type_l([T|_],Typ) :- get_attribute(T,TypT),
	term_variables(TypT,TL),
	with_type_l(TL,Typ),!.
with_type_l([_|TL],Typ):- with_type_l(TL,Typ),!.


make_var_attrib(and([],wff)) :- !.
make_var_attrib(and([],T)) :- type_attribute(T,_),!.
make_var_attrib(and([],T)) :- functor(T,Op,N),
	functor(TT,Op,N),
	find_attributes(and([],TT),[],AL),
	assert(type_attribute(TT,AL)),!.
make_var_attrib(T) :- printf("ILF ERROR: No attributes for type %w\n",[T]),!.

/*find_attributes(and([in(A)|AA],T),L,AL) :- 
	find_attributes(and(AA,T),[A|L],AL),!.
*/
find_attributes(and([A|AA],T),L,AL) :- find_attributes(and(AA,T),[A|L],AL),!.
find_attributes(and([],set),L,AL) :- msort(L,AL),!.
find_attributes(and([],M),L,AL) :- user_widens(M,T),find_attributes(T,L,AL),!.

immediate_below(A1,A1) :- !,fail.
immediate_below(A1,A2) :- not subset(A2,A1),!,fail.
immediate_below(A1,A2) :- subset(A2,A1),not (
	mg_attribute(A,_),subset(A,A1),subset(A2,A),
	A \= A1, A \= A2
	).
	
/* topologische Sortierung von R(X,Y) */

inc_fan(X) :- retract(node_fan(X,N)),(N1 is N+1),assert(node_fan(X,N1)),!.
dec_fan(X) :- retract(node_fan(X,N)),(N1 is N-1),assert(node_fan(X,N1)),!.

top_sort(_,_,_) :- retract_all(is_leaf(_)),
	retract_all(is_node(_,_)),
	retract_all(node_fan(_,_)),
	setval(top_sort,1),fail.
top_sort(R,X,Y) :- R,make_note(node_fan(X,0)),
	make_note(node_fan(Y,0)),fail.
top_sort(R,_,Y) :- R,inc_fan(Y),fail.
top_sort(_,_,_) :- node_fan(X,0),assert(is_leaf(X)),fail.
top_sort(R,X,Y) :- repeat,
	not((
		getval(top_sort,N),
		retract(node_fan(X,0)),
		assert(is_node(X,N)),
		incval(top_sort),
		dec_father_fans(R,Y)
	)),!.

dec_father_fans(R,Y) :-
		R,dec_fan(Y),fail.
dec_father_fans(_,_).

/* make_leafs_below ordnet Knoten Mengen zu, setzt is_node in topologischer Sortierung voraus*/

make_leafs_below(_,_,_) :- retract_all(leafs_below(_,_)),fail.
make_leafs_below(R,X,Y) :- is_node(Y,_),make_the_leafs_below(R,X,Y),fail.
make_leafs_below(_,_,_).

make_the_leafs_below(R,X,Y) :- setof(LX,X^(R,leafs_below(X,LX)),LP),
	s_union(LP,LY),
	assert(leafs_below(Y,LY)),!.
make_the_leafs_below(_,_,Y) :- assert(leafs_below(Y,[Y])),!.

make_note(R) :- R,!.
make_note(R) :- assert(R),!.

make_all_leafs(R,_,Y) :- is_node(Y,_),(not R),make_note(is_leaf(Y)),fail.
make_all_leafs(_,_,_).

make_separable(R,X,Y) :- copy_term(R,R1),
	R,
	once((
		leafs_below(X,L),
		leafs_below(Y,L),
		add_leaf_below(Y,R1)
	)),
	fail.
make_separable(_,_,_).

add_leaf_below(X,R) :- is_node(_,N),(N1 is N-1),
	Y=sep(X),
	asserta(is_node(Y,N1)),
	assert(is_leaf(Y)),
	not not (R=..[_,Y,X|_],assert(R)),
	assert(leafs_below(Y,[Y])),
	extend_leafs_above(X,Y,R),!.

/* Wenn Y schon da, so nicht weiter hochgehen */
extend_leafs_above(type([],relation,2),_,_) :- fail.
extend_leafs_above(X,Y,_) :- leafs_below(X,L),member(Y,L),!.
extend_leafs_above(X,Y,_) :- 
	once((
		retract(leafs_below(X,L)),
		s_union([Y],L,L1),
		assert(leafs_below(X,L1))
	)),fail.
extend_leafs_above(X,Y,R) :- 
	copy_term(R,R1),
	R1=..[_,X,X1|_],
	R1,
	extend_leafs_above(X1,Y,R),fail.
extend_leafs_above(_,_,_).

s_union([E|L],L1) :- s_union(L,LU),s_union(E,LU,L1),!.
s_union([],[]).

s_union([A|LA],[A|LB],[A|LC]) :- s_union(LA,LB,LC).
s_union([A|LA],[B|LB],[B|LC]) :- B @< A,s_union([A|LA],LB,LC),!.
s_union([A|LA],LB,[A|LC]) :- s_union(LA,LB,LC),!.
s_union([],L,L).

/* make_short_codes/0 verkuerzt Codierung. 
* Benutzt is_below,leafs_below und is_leaf die bei est_type_term 
* hergestellt werden. 
* Methode: Es wird von oben her nach einem Baum gesucht.
* Knoten dieses Baumes werden durch Differenzlisten codiert.
* Laesst sich ein Knoten nicht disjunkt zerlegen, so wird das Mellish-Verfahren
* nur fuer diesen Teil separat angewandt und die Mellishterme werden
* als ein Element angefuegt.
*/

make_short_codes :- retract_all(short_code(_,_)),
	retract_all(attrib_par(_,_,_)),
	dupli(is_below(_,_)),
	dupli(is_leaf(_)),dupli(leafs_below(_,_)),
	fail.
make_short_codes :- is_max(Max),
	mg_attribute(A,Max),
	assert(attrib_par(A,Max,_)),
	make_short_max([Max]),!.

make_short_max([Max]) :- new_hierarchy,rebuild_below(Max),
	get_pars(Max,_),
	setof(U,is_below(U,Max),MaxList),
	make_short_max(MaxList),
	assert(short_code(Max,X-X)),!.
make_short_max([Max]) :- get_pars(Max,_),
	assert(short_code(Max,X-X)),!.
make_short_max(MaxList) :- dis_classes(MaxList,DisCl),
	make_short_dis(DisCl),!.

dis_classes(L,DL) :- singleton_list(L,L1),
	connect_classes(L1,DL),!.

singleton_list([E|L],[[E]|L1]) :- singleton_list(L,L1),!.
singleton_list([],[]).

connect_classes([C],[C]) :- !.
connect_classes([C1|CL],DL) :- test_connect(C1,CL,CL1),
	connect_classes(CL1,DL),!.
connect_classes([C1|CL],[C1|DL]) :- connect_classes(CL,DL),!.

test_connect(C,[C1|CL],[C2|CL]) :- member(X,C),leafs_below(X,XL),
	member(Y,C1),leafs_below(Y,YL),
	member(U,XL),member(U,YL),
	append(C,C1,C2),!.
test_connect(C,[C1|CL],[C1|DL]) :- test_connect(C,CL,DL),!.

make_short_dis([C|DisCl]) :- length(DisCl,N),
	make_cl_typeterm(C,N),make_short_dis(DisCl),!.
make_short_dis([]).

make_cl_typeterm([Max],N) :- make_short_max([Max]),
	new_hierarchy,
	rebuild_below(Max),
	add_const(Max,N),!.
make_cl_typeterm(C,N) :- new_hierarchy,
	rebuild_below_l(C),
	add_top(C),
	make_m_terms,
	add_parameter(top),
	m2sh(N),!.

add_const(Max,N) :- retract(leafs_below(Max,_)),
	retract(short_code(Max,L-R)),
	assert(short_code(Max,[N|L]-R)),
	(
	setof(U,is_below(U,Max),UL),
	add_const_l(UL,N)
	;
	true
	),!.

add_top([E|_]) :- 
/* Da die Argumentliste eine nicht separierbare Klasse moeglichst weit oben ist, muessen alle Elemente den selben Vorgaenger haben */
	once((
		retract_all(attrib_par(_,top,_)),
		tmp(is_below(E,Top)),
		attrib_par(A,Top,P),
		assert(attrib_par(A,top,P)),
		length(P,N),
		setval(vcnt,N)
	)),fail.
add_top([E|L]) :- assert(is_below(E,top)),
	add_top(L),!.
add_top([]) :- setof(U,is_leaf(U),L),assert(leafs_below(top,L)),!.

add_const_l([M|L],N) :- add_const(M,N),add_const_l(L,N),!.
add_const_l([],_).

m2sh(N) :- retract(m_term(A,T)),
	assert(short_code(A,[N,T|X]-X)),fail.
m2sh(_).

/* Ende neues make_short_codes */


is_max(N) :- is_below(_,N),not is_below(N,_),!.

get_sep(N,L) :- bagof(N1,is_below(N1,N),LB),
	get_sep(LB,[],L),!.

get_sep([N|LB],LR,LC) :- is_disjoint_l(N,LR),!,get_sep(LB,[N|LR],LC),!.
get_sep([_|LB],LR,LC) :- get_sep(LB,LR,LC),!.
get_sep([],L,L).

is_disjoint_l(N,L) :- leafs_below(N,LN),member(NL,L),leafs_below(NL,LNL),
	member(X,LN),member(X,LNL),!,fail.
is_disjoint_l(_,_).

dupli(X) :- X,assert(tmp(X)),fail.
dupli(_).

new_hierarchy :- retract_all(is_below(_,_)),
	retract_all(leafs_below(_,_)),
	retract_all(is_leaf(_)),
	!.

rebuild_below(N) :- leafs_below(N,_),!.
rebuild_below(N) :- tmp(leafs_below(N,NL)),assert(leafs_below(N,NL)),fail.
rebuild_below(N) :- tmp(is_leaf(N)),assert(is_leaf(N)),fail.
rebuild_below(N) :- tmp(is_below(N1,N)),
	assert(is_below(N1,N)),
	rebuild_below(N1),
	fail.
rebuild_below(_).

rebuild_below_l([N|L]) :- rebuild_below(N),rebuild_below_l(L),!.
rebuild_below_l([]).

ass_short_codes(N,[N1|L]) :- short_code(N,L1-[N1|R]),
	assert(short_code(N1,L1-R)),
	make_short_codes(N1),
	ass_short_codes(N,L),!.
ass_short_codes(_,[]).

ass_m_terms(N) :- short_code(N,L-[M|R]),m_term(K,M),
	assert(short_code(K,L-R)),fail.
ass_m_terms(N) :- short_code(N,L-[]),
	length([_|L],LN),
	getval(max_path,LP),
	(LN =< LP;setval(max_path,LN)),!.



/* Herstellen der Mellish-Terme */

make_m_terms :- retract_all(m_term(_,_)),fail.
make_m_terms :- setof(L,is_leaf(L),LL),
	make_m_terms(LL),!.

make_m_terms(LL) :- is_node(X,_),
	once(leafs_below(X,LX)),
	a_term(LL,LX,T,0),
	assert(m_term(X,T)),
	fail.
make_m_terms(_).

m_term(A,X,M) :- a_term(A,X,M,0).
/* a_term(Liste,Teilliste,Ergebnis,letztes benutztes Element) */
a_term([A],[A],[],_) :- !.
a_term([_],[],[],1).
/* Neuer Wert, wenn Element in Liste */
a_term([A|AL],[A|X],[U|UL],_) :- a_term(AL,X,UL,U),!.
/* Sonst Wert uebernehmen */
a_term([_|AL],X,[U|UL],U) :- a_term(AL,X,UL,U),!.
a_term([],X,_,_) :- printf("ILF ERROR: Unknown attributes %w\n",[X]).


get_pars(Max,AMax) :- attrib_par(_,Max,AMax),!.
get_pars(Max,KPar) :- tmp(is_below(Max,K)),!,
	attrib_par(AK,K,KPar),
	(
	mg_attribute(AMax,Max),
	subset(AK,AMax),
	var_pars(AMax,KPar)
	;
	AMax=AK
	),
	assert(attrib_par(AMax,Max,KPar)),!.
get_pars(_,X-X).
	
var_pars([T|L],V1) :- T=..[_|Arg],term_pars(Arg,V1),var_pars(L,V1),!.
var_pars([],_).

term_pars([X|Arg],V1) :- var(X),ins_var(X,V1),term_pars(Arg,V1),!.
term_pars([_|Arg],V1) :- term_pars(Arg,V1),!.
term_pars([],_).

ins_var(X,V) :- var(V),V=[X|_],!.
ins_var(X,[Y|_]) :- X==Y,!.
ins_var(X,[_|V]) :- ins_var(X,V),!.

/* Das selbe, es wird aber erst nach vcnt Parametern eingefuegt */ 
var_pars_cnt([T|L],V1) :- T=..[_|Arg],term_pars_cnt(Arg,V1),
	var_pars_cnt(L,V1),!.
var_pars_cnt([],_).

term_pars_cnt([X|Arg],V1) :- var(X),getval(vcnt,Vcnt),
	ins_var_cnt(X,V1,Vcnt,0),term_pars_cnt(Arg,V1),!.
term_pars_cnt([_|Arg],V1) :- term_pars_cnt(Arg,V1),!.
term_pars_cnt([],_).

ins_var_cnt(X,V,N,N) :- var(V),V=[X|_],incval(vcnt),!.
ins_var_cnt(X,V,N,I) :- var(V),V=[_|V1],(I1 is I+1),ins_var_cnt(X,V1,N,I1),!.
ins_var_cnt(X,[Y|_],_,_) :- X==Y,!.
ins_var_cnt(X,[_|V],N,I) :- (I1 is I+1),ins_var_cnt(X,V,N,I1),!.

/* Suchen der Parameter fuer Knoten NA */
add_parameter(NA) :- is_below(N,NA),
	add_the_parameter(N),fail.
add_parameter(_).

/* Schon da, so fertig */
add_the_parameter(N) :- attrib_par(_,N,_),!.
/* Obere Parameter aufsammeln und instantiieren */
add_the_parameter(N) :- mg_attribute(A,N),
	upper_parameter(A,N,P),
	assert(attrib_par(A,N,P)),!,
/* Wenn ein Knoten fertig ist, die darunterliegenden versuchen */
	add_parameter(N).

upper_parameter(A,N,P) :- setof(NN,is_below(N,NN),NL),
	collect_parameters(NL,A,P),!.

/* Wenn fuer einen darueberliegenden Knoten noch nicht fertig, so Versuch abbrechen */
collect_parameters([N|NL],A,P) :- attrib_par(AN,N,P),
	subset(AN,A),!,
	collect_parameters(NL,A,P),!.
collect_parameters([],A,P) :- var_pars_cnt(A,P).


var2par([X|V],Par) :- term_variables(Par,Par1),
	strict_member(X,Par1),!,
	var2par(V,Par),!.
var2par([X|V],Par) :- getval(vcnt,N),
	var2par(X,Par,N),
	var2par(V,Par),!.
var2par([],_).

var2par(X,[X|_],0) :- incval(vcnt),!.
var2par(X,[_|Par],N) :- (N1 is N-1),var2par(X,Par,N1),!.
var2par(_,_,_) :- writeln("ILF ERROR in var2par").


% get_term_type(Term,Type) ermittelt entsprechenden Typ fuer gegebenen Term 

get_term_type((L-Par),Type):-
	term_type((L1-Par1),Type1),
	variant(L,L1),
	Par1 = Par,     % Annahme: Par1 ist immer allgemeiner (WB-Eintrag)
			% dadurch wird auch Type1 gebunden
	Type1 = Type,
	!.
get_term_type((L-Par),_):-
	term_string(L,LS),
	term_string(Par,ParS),
	ilf_error(["get_term_type: not found term_type for [",LS,"-",ParS,"]"]),
	!.	


/******   Ende Erzeugung der Codierung fuer die Typen  ***/


/*******   Anfang   Trusted Domains           ************/


trusted_fla(X,DL) :- get_attribute(X,T),!,trusted_type(T,DL),!.
trusted_fla(contradiction,_) :- !,fail.
trusted_fla(F,DL) :- log_op(F,_),F=..[_|Arg],trusted_fla_l(Arg,DL),!.
trusted_fla(F,DL) :- F=..[_|Arg],functor(F,Op,N),
	trusted_op(Op,N,D),
	trusted_fla_l(Arg,DA),
	union(D,DA,DL),!.

trusted_fla_l([F|FL],DL) :- trusted_fla(F,DF),trusted_fla_l(FL,DFL),
	union(DF,DFL,DL),!.
trusted_fla_l([],[]).

trusted_op(Op,N,[D]) :- functor(F,Op,N),
	safe_transaction(retrieve_clause(definition(D,user_type(F,_)))),
	trusted_domain(D),!.

trusted_type(T,[D]) :- 
	safe_transaction(retrieve_clause(definition(D,user_type(T,and([],type))))),
	trusted_domain(D),!.

trusted_domain(D) :- ilf_state(trusted_domains,DL),member(D,DL),!.


/*******   Ende   Trusted Domains           ************/





transfer_attributes([X|XL],[Y|YL]) :- get_attribute(X,A),!,
	add_attribute(Y,A),
	transfer_attributes(XL,YL),!.
transfer_attributes([_|XL],[_|YL]) :- transfer_attributes(XL,YL),!.
transfer_attributes([],[]).

/* specials2vars(T,T1,Op,TL,VL) erzeugt T1 aus T indem alle Teilterme der form Op(U) durch Variable ersetzt werden. Die ersetzten Terme U bzw. die eingesetzten Variablen werden in TL bzw. VL gesammelt */
specials2vars(X,X,_,[],[]) :- var(X),!.
specials2vars(T,X,Op,[T1],[X]) :- T=..[Op,T1],!.
specials2vars(T,T1,Op,TL,VL) :- T=..[OpT|Arg],
	specials2vars_l(Arg,Arg1,Op,TL,VL),
	T1=..[OpT|Arg1],!.

specials2vars_l([T|Arg],[T1|Arg1],Op,TL,VL) :- 
	specials2vars(T,T1,Op,TL0,VL0),
	specials2vars_l(Arg,Arg1,Op,TL1,VL1),
	append(TL0,TL1,TL),
	append(VL0,VL1,VL),!.
specials2vars_l([],[],_,[],[]).

	
/* Syntax-Typ */
/* wenn log_op geaendert wird, dann muss auch transform_ilf_nftsource/2
 * aus knowman geaendert werden (gibt den Operatoren eine Semantik) 
 */

log_op((_,_),[]) :- !.
log_op((_;_),[]) :- !.
log_op(not(_),[]) :- !.
log_op(^(_),[]) :- !.
log_op((_ :- _),[]) :- !.
log_op((_ -> _),[]) :- !.
log_op('<-'(_ , _),[]) :- !.
log_op(&(_),[]) :- !.
log_op(#(_),[]) :- !.
log_op((_ <-> _),[]) :- !.
log_op(contradiction,[]) :- !.
% log_op(true,[]) :- !.
log_op(all(X,_),[X]) :- var(X),!.
log_op(forall([X|L],_),[X|L]) :- !.
log_op(ex(X,_),[X]) :- var(X),!.
log_op(exists([X|L],_),[X|L]) :- !.
log_op(exl1(X,_),[X]) :- !.
log_op(ex1(X,_),[X]) :- !.


quant_op(all(X,_),[X]) :- var(X),!.
quant_op(forall([X|L],_),[X|L]) :- !.
quant_op(ex(X,_),[X]) :- var(X),!.
quant_op(exists([X|L],_),[X|L]) :- !.
quant_op(exl1(X,_),[X]) :- !.
quant_op(ex1(X,_),[X]) :- !.

free_vars(X,[X|V]) :- get_attribute(X,T),term_variables(T,V),!.
free_vars(X,[X]) :- var(X),!.
free_vars(F,V) :- log_op(F,VF),
	F=..[_|Arg],
	free_vars_l(Arg,VArg),
	strict_remove_l(VF,VArg,V),!.
free_vars(F,V) :- term_variables(F,V).

free_vars_l([F|FL],V) :- free_vars(F,VF),free_vars_l(FL,VL),
	strict_union(VF,VL,V),!.
free_vars_l([],[]).

a_close(schema(D,F),schema(D,F1)) :- a_close(F,F1),!.
a_close(F1,F2) :- free_vars(F1,V),
	sort_var_by_name(V,V1),
	a_close(F1,V1,F2),!.

a_close(F1,[],F1).
a_close(F1,[X],all(X,F1)).
a_close(F1,[X|L],all(X,F2)) :- a_close(F1,L,F2),!.
a_close(F1,V,forall(V,F1)).

sort_var_by_name(V,V1) :- var_name_list(V,VN),sort(VN,VN1), % hier muesste noch beruecksichtigt werden, dass Variable die in Typen von Variablen vorkommen, zuerst quantifiziert werden ID
	rm_var_names(VN1,V1),!.

var_name_list([X|XL],[(N/X)|NL]) :- get_var_info(X,name,N),
	var_name_list(XL,NL),!.
var_name_list([X|XL],[(N/X)|NL]) :- gensym("ZZ_ILF",N),
	var_name_list(XL,NL),!.
var_name_list([],[]).

rm_var_names([(_/X)|NL],[X|XL]) :- rm_var_names(NL,XL),!.
rm_var_names([],[]).

%% mk_all_closure( RootFla, VarL, Fla)

mk_all_closure(Fla, [], Fla) :- !.
mk_all_closure(Fla, [VarH|VarT], all(VarH, Fla1)):-
	mk_all_closure(Fla, VarT, Fla1),
	!.
mk_all_closure(_,_,_):-
	ilf_error("mk_all_closure in unexpected situation").


% Aus mathlib_db uebernommen

% signature(Fla,Sig) yields the used symbol for a formula
% Sig has the format : [ [ < FctSymb/Arity >* ], [ < PredSymb/Arity >* ]]
% and is different from database-entries

%signature(all(_,C),S) :- signature(C,S),!.
%signature(ex(_,C),S) :- signature(C,S),!.
%signature(and(L),S) :- signature_l(L,S),!.
%signature(given(_,C),S) :- !,signature(C,S).
%signature(take_term(_),[]) :- !.
%signature(=(L),[Func,[(=)/2|Pred]]) :- !,signature_l(L,[Func,Pred]).
%signature(set(:(_,T)),S) :- !,signature(T,S).
signature(C,S) :- log_op(C,_),!,
	C=..[_|L],signature_l(L,S),!.
%signature(schema(SP,F),S) :- signature(F,SF),
%	remove_predeclared(SP,SF,S),!.
%signature(let(_),[[],[]]) :- !.
signature(C,[ArgF,SR]) :- C=..[Op|Arg],length(Arg,N),
	fsignature_l(Arg,[ArgF,ArgR]),strict_union([Op/N],ArgR,SR),!.

signature_l([E|L],[SF,SR]) :- signature(E,[EF,ER]),signature_l(L,[LF,LR]),
	strict_union(EF,LF,SF),
	strict_union(ER,LR,SR),!.
signature_l([],[[],[]]).

fsignature(X,[[],[]]) :- var(X),!.
fsignature(X,[[],[]]) :- atom(X),
	atom_string(X,XS),string_list(XS,[99|L]),
	string_list(NS,L),
	number_string(_,NS),!.
fsignature(X,[SF,ArgR]) :- X=..[Op|Arg],
	length(Arg,N),
	fsignature_l(Arg,[ArgF,ArgR]),
	strict_union([Op/N],ArgF,SF),!.

fsignature_l([E|L],[SF,SR]) :- fsignature(E,[EF,ER]),fsignature_l(L,[LF,LR]),
	strict_union(EF,LF,SF),
	strict_union(ER,LR,SR),!.
fsignature_l([],[[],[]]).



% is_conj/1, is_disj/1 ueberpruefen, ob Argument Konjunktion oder Disjunktion

is_conj(','(A,B)):-
	is_conj(A),
	is_conj(B),
	!.
is_conj(A):-log_op(A,_),!,fail.
is_conj(_).


is_disj(';'(A,B)):-
	is_disj(A),
	is_disj(B),
	!.
is_disj(A):-log_op(A,_),!,fail.
is_disj(_).

% conj2list verwandelt Konjunktion in Liste
% conj2list ist effizienter implementierbar wenn Assoziativiaet vom ','
% gesichert   T.Baar

conj2list(','(A,B),L):-
	conj2list(A,L1),
	conj2list(B,L2),
	append(L1,L2,L).
conj2list(A,[A]).
	

negl_term([], true):- !.
negl_term(L, T) :- list2conj(L,T).
posl_term([], false):- !.
posl_term(L, T) :- list2disj(L,T).

/* list_konj macht aus einer Liste die Konjunktion ihrer Elemente */
list2conj([H],H).       	
list2conj([H1,H2], Conj):- Conj =..[',',H1,H2],!.
list2conj([H|T], Conj) :- 
	Conj =..[',',H,KT],
	list2conj(T,KT),!.	
list2disj([H],H).       	
list2disj([H1,H2], Disj):- Disj =..[';',H1,H2],!.
list2disj([H|T], Disj) :- 
	Disj =..[';',H,KT],
	list2disj(T,KT),!.		
	







/* Lokale Typen werden nur asserted, ohne user_type im Speicher zu veraendern.
Wird es im Vordergrund aufgerufen, so wird es auch im Hintergrund aufgerufen. Wird es im Hintergrund augerufen, so wird die Deklaration auch in der Wissensbasis abgespeichert.
Zur Unterscheidung ob Vorder- oder Hintergrund wird der Modul exman benutzt. exman ist nur im Hintergrund vorhanden*/

make_local_type(_,R,C,B) :- asserta((local_type(R,C) :- B)),fail.
make_local_type(D,R,C,B) :- ilf_state(experts,off),
	safe_transaction(insert_clause(definition(D,(user_type(R,C) :- B)))),!.
make_local_type(D,R,C,B) :-
	current_module(exman),
	safe_transaction(insert_clause(definition(D,(user_type(R,C) :- B)))),!.
make_local_type(D,R,C,B) :- ':'(0,make_local_type(D,R,C,B)),!.

erase_local_type(_,X,Y) :- retract_all(local_type(X,Y)),fail.
erase_local_type(D,X,Y) :- ilf_state(experts,off),
	safe_transaction(retract_all_clauses(definition(D,(user_type(X,Y) :- _)))),!.
erase_local_type(D,X,Y) :-
	current_module(exman),
	safe_transaction(retract_all_clauses(definition(D,(user_type(X,Y) :- _)))),!.
erase_local_type(D,X,Y) :-
	':'(0,erase_local_type(D,X,Y)),
	!.

test_local_type([D|L]) :- make_untyped_decl(D,B,F,T),
	asserta((local_type(F,T) :- B)),
	test_local_type(L).
test_local_type([D -> T|_]) :- retract((local_type(D,T) :- _)),fail.
test_local_type([]).

make_untyped_decl(D,B,F,T) :- term_variables(D,V0),
	copy_term((D,V0),(gives(F,T),V)),
	type_test(V0,V,B),!.

type_test([X0|V0],[X|V],(syntax_type(X,T),B)) :- get_attribute(X0,T),
	type_test(V0,V,B),!.
type_test([],[],true).

erase_test_local_type([gives(D,T)|L]) :- retract((local_type(D,T) :- _)),
	erase_test_local_type(L),!.
erase_test_local_type([]).

% get_type(X,T) bestimmt den kleinsten Typ T von X

get_type(X,T) :- get_attribute(X,T),!.
get_type(X,T) :- user_type(X,T),!.
get_type(X,T) :- local_type(X,T),!.


syntax_type(T,M) :- get_attribute(T,MT),!,
	is_subtype(MT,M),!.
syntax_type(X,T) :- free(X),!,T=and([],set),
	printf("ILF Warning: Untyped Variable %w typed 'set'.\n",[X]),
	add_attribute(X,and([],set)),!.
syntax_type(X,and([],element_of(P))) :- -?-> syntax_type(X,P),!.
syntax_type(all(X,A),and([],wff)) :- !,var(X),
	syntax_type(A,and([],wff)),
	!.
syntax_type(ex(X,A),and([],wff)) :- !,var(X),
	syntax_type(A,and([],wff)),
	!.
syntax_type(forall(X,A),and([],wff)) :- !,varlist(X),
	syntax_type(A,and([],wff)),!.
syntax_type(exists(X,A),and([],wff)) :- !,varlist(X),
	syntax_type(A,and([],wff)),!.
syntax_type(ex1(X,A),and([],wff)) :- !,var(X),
	syntax_type(A,and([],wff)),!.
syntax_type(is(Term,Typ),and([],wff)) :- !,syntax_type(Typ,and([],type)),
	syntax_type(Term,Typ).
syntax_type(and(_,set),and([],type)).
syntax_type(schema(Decl,Fla),and([],schema)) :- test_local_type(Decl),
	syntax_type(Fla,and([],wff)),erase_test_local_type(Decl),!.
syntax_type(setof(VL,T,H),and([],set)) :- !,varlist(VL),
	syntax_type(T,and([],set)),
	syntax_type(H,and([],wff)).
syntax_type(H,T) :- 
	log_op(H,_),
	T=and([],wff), % verhindert Unifikation von 2. Argument mit and([],wff) wenn kein logischer Ausdruck
	H=..[_|Arg],
	syntax_type_l(Arg,and([],wff)),!.
syntax_type(H,TT) :- local_type(H,TH),
	is_subtype(TH,TT),!.
syntax_type(and(A,M),and([],type)) :- user_type(and(A,M),and([],type)),!.
syntax_type(H,TT) :- 
	user_type(H,TH),
	is_subtype(TH,TT),!.
syntax_type(H,T) :- ilf_debug(printf("ILF Warning: %w does not have type %w\n",[H,T])),fail.

syntax_type_l([H|HL],[S|SL]) :- syntax_type(H,S),
	syntax_type_l(HL,SL),!.
syntax_type_l([H|HL],S) :- syntax_type(H,S),
	syntax_type_l(HL,S),!.
syntax_type_l([],_).

is_subtype(T1,and([A|AL],M)) :- has_attribute(T1,A),!,
	is_subtype(T1,and(AL,M)),!.
/* Wenn der Obertyp Variable ist, so bezeichnet er eine Menge */
/* Der Untertyp muss dann auch eine Menge sein */
/* Beide Typen sind also klein */
is_subtype(and([],element_of(T)),T) :- var(T),!.
is_subtype(and([],S),S1) :- var(S1),S=S1.
is_subtype(and([],P),and([],element_of(Q))) :- -?-> 
	is_subtype(and([],P),and([],Q)).
/* Ausser Typen und wffs ist alles Untertyp von set - dieser Test belegt nichts */
is_subtype(X,and([],set)) :- -?-> 
	not (X=and(_,Y),strict_member(Y,[wff,type])),!.
is_subtype(T,T) :- !.
is_subtype(T1,and([],M)) :- user_widens(M,T2),
	is_subtype(T1,T2).

clause_pool(occur,[
	(is_subtype(T1,and([A|AL],M)) :- has_attribute(T1,A),!,
		is_subtype(T1,and(AL,M)),!),
	(is_subtype(and([],S),S1) :- var(S1),S=S1),
	(is_subtype(_,and([],set)) :- -?-> true),
	(is_subtype(T,T) :- !),
	(is_subtype(T1,and([],M)) :- user_widens(M,T2)),
	is_subtype(T1,T2)
	]).

	
has_attribute(and([AA|_],_),AA) :- !.
has_attribute(and([_|AL],T),AA) :- has_attribute(and(AL,T),AA),!.
has_attribute(and([],M),AA) :- user_widens(M,T),has_attribute(T,AA),!.

varlist(X) :- var(X),!,fail.
varlist([X|L]) :- var(X),varlist(L),!.
varlist([X]) :- var(X),!.

canonic_vars(T1,T2) :- 
	open("",string,S),
	write_canonical(S,T1),
	seek(S,0),
	read(S,T2),
	close(S).

make_working_domain :- safe_transaction((
	make_working_ops,
	make_working_definitions,
	make_working_reservations,
	make_working_abbreviations
	)),!.


make_working_ops :- retrieve_clause(operator(_,P,A,O)),
	global_op(P,A,O),
	fail.
make_working_ops.

make_working_definitions :- prepare_dynamic_l([user_type/2,user_widens/2]),fail.
make_working_definitions :- retrieve_clause(definition(_,Clause)),
	asserta(Clause),fail. % Reihenfolge muss umgekehrt werden, da in KB beim Einlesen nur hinten angefuegt werden kann
make_working_definitions.

make_working_reservations :- prepare_dynamic(var_has_typterm/2),fail.
make_working_reservations :-
	retrieve_clause(reservation(V,T)),
	assert(var_has_typterm(V,T)),
	fail.
make_working_reservations.

make_working_abbreviations :- prepare_dynamic(abbreviation/2),fail.
make_working_abbreviations :-
	retrieve_clause(abbreviation(V,T)),
	asserta(abbreviation(V,T)),
	fail.
make_working_abbreviations.



kb_reservations :- var_has_typterm(V,_),
	transaction(retract_clause(reservation(V,_))),fail.
kb_reservations :- var_has_typterm(V,T),
	transaction(insert_clause(reservation(V,T))),fail.
kb_reservations.

decl_clause(D,C) :- definition(D,Op,Decl),
	make_decl_clause(Op,Decl,C).

make_decl_clause(Op,(L -> S),(user_type(X,S,V) :- syntax_type_l(Var,L,V))) :-
	length(L,N),
	length(Var,N),
	X=..[Op|Var],!.
make_decl_clause(Op,S,user_type(Op,S,[])).

check_domain(D) :- printf("Checking domain %mw\n",[D]),fail.
check_domain(D) :- make_working_domain(D),
	formula(D,N,fla,F),
	check_formula(N,F),
	fail.
check_domain(D) :- printf("Domain %w checked\n",[D]).

check_formula(_,F) :- syntax_type(F,and([],wff),_),!.
check_formula(N,_) :- printf("*** %mw not wellformed ***\n",[N]).

check_domains :- domain(D),check_domain(D),fail.
check_domains.

/* Typberechnung */
widens(M,set,[]) :- get_attribute(M,and(_,MM)),!,widens(MM,set,_).
widens(M,M,[]) :- !.
widens(M1,M2,A) :- user_widens(M1,and(A1,M)),
	widens(M,M2,AA),
	union(A1,AA,A).

/* Erzeugen der Voraussetzungen fuer Syntaxtests mit user_type/2 */
make_user_type(Key,(C11,C12),C2,C3) :- !,
	make_user_type(Key,C11,C2,C3),
	make_user_type(Key,C12,C2,C3),!.
make_user_type(domain,D,_,_) :- 
	once((
		atom(D),DD=D,T=D
		;
		D=..[DD,T]
	)),
	insert_clause(domain(DD,title,T)),
	setval(current_domain,DD),!.
make_user_type(mode,M1,Type,_) :- user_widens(M1,_),
	ilf_warning("Redeclaration of type %w as %w ignored.",[M1,Type]),!.
make_user_type(mode,M1,TypeS,_) :- !,
	is_shorthand(TypeS,Type),
	syntax_type(Type,and([],type)),
	asserta((
		user_widens(M1,Type)
	)),
	getval(current_domain,D),
	insert_clause(definition(D,user_widens(M1,Type))),
	asserta(user_type(and(_,M1),and([],type))),
	insert_clause(definition(D,user_type(and(_,M1),and([],type)))),
	(
	Type=and(_,MType),syntax_type(MType,and([],set)),
	make_user_type(func,M1,and([],nonempty_set),_)
	;
	true
	),!.
make_user_type(type,M1,Type,_) :- user_widens(M1,_),
	ilf_warning("Redeclaration of type %w as %w ignored.",[M1,Type]),!.
make_user_type(type,M1,TypeS,_) :- !,
	is_shorthand(TypeS,Type),
	syntax_type(Type,and([],type)),
	Type=and(A,MType),
	Type1=and([M1|A],MType),
	asserta((
		user_widens(M1,Type1)
	)),
	getval(current_domain,D),
	insert_clause(definition(D,user_widens(M1,Type1))),
	asserta(user_type(and(_,M1),and([],type))),
	insert_clause(definition(D,user_type(and(_,M1),and([],type)))),
	(
	Type1=and(_,MType),syntax_type(MType,and([],set)),
	make_user_type(func,M1,and([],nonempty_set),_)
	;
	true
	),!.
make_user_type(small_mode,M1,and(A,T),_) :- !,
	make_user_type(mode,M1,and([in(M1)|A],T),_),
	syntax_type(and([],M1),and([],type)),
	asserta(user_type(M1,and([],small_type))),
	getval(current_domain,D),
	insert_clause(definition(D,user_type(M1,and([],small_type)))),!.
make_user_type(set_type,M1,and(A,T),_) :- !,
	make_user_type(type,M1,and(A,T),_),
	syntax_type(and([],M1),and([],type)),
	asserta(user_type(M1,and([],small_type))),
	getval(current_domain,D),
	insert_clause(definition(D,user_type(M1,and([],small_type)))),!.
make_user_type(struct,Constr,SelS,and(A,Mode)) :- !,
	is_shorthand(SelS,Sel),
	make_user_type(mode,Mode,and([Mode|A],set),_),
	make_sel_decl(Sel,and([],Mode),Vars),
	canonic_vars(Vars,Vars1),
	M=..[Constr|Vars1],
	make_user_type(func,M,and([],Mode),_),
	(
	set_valued(Sel),!,
	make_user_type(func,Mode,and([],small_type),_)
	;
	true
	),
	getval(current_domain,D),
	insert_clause(struct(D,and(A,Mode),M,Sel)),!.
make_user_type(pred,Term,_,_) :- functor(Term,Op,N),
	functor(F,Op,N),
	user_type(F,_),!,
	ilf_warning("Redeclaration of %w-ary predicate %w ignored.",[N,Op]).
make_user_type(pred,Term,_,_) :- asserta(user_type(Term,and([],wff))),
	getval(current_domain,D),
	insert_clause(definition(D,user_type(Term,and([],wff)))),!.
make_user_type(func,Term,TypTerm,_) :- functor(Term,Op,N),
	functor(F,Op,N),
	user_type(F,_),!,
	ilf_warning("Redeclaration of %w-ary functor %w with values of type %w ignored.",[N,Op,TypTerm]).
make_user_type(func,Term,TypTerm,_) :- 
	is_shorthand((Term,TypTerm),(Term1,TypTerm1)),
	get_hidden_variables(Term1,TypTerm1,TTerm),
	asserta(user_type(TTerm,TypTerm1)),
	getval(current_domain,D),
	insert_clause(definition(D,user_type(TTerm,TypTerm1))),!.
make_user_type(formula,Name,Formel,_) :- printf("Checking %w:\n",[Name]),
	ilf_state(debug,D),!,
	(ilf_state(debug,_,on);ilf_state(debug,_,D),fail),
	is_shorthand(Formel,Formel1),	
	syntax_type(Formel1,and([],wff)),
	a_close(Formel1,Formel2),
	getval(current_domain,Dom),
	(retract_clause(formula(Dom,Name,fla,_)) ->
		ilf_warning("Replacing formula with name %w in domain %w",[Name,Dom]),
		retract_all_clauses(formula(Dom,Name,fla,_))
		;
		true
	),
	insert_clause(formula(Dom,Name,fla,Formel2)),
	ilf_state(debug,_,D),
	writeln(ok),!.
make_user_type(schema,Name,schema(Decl,H),_) :- printf("Checking %w:\n",[Name]),
	ilf_state(debug,D),!,
	(ilf_state(debug,_,on);ilf_state(debug,_,D),fail),
	is_shorthand(Decl,Decl1),
	test_local_type(Decl1),
	is_shorthand(H,H1),	
	syntax_type(H1,and([],wff)),
	erase_test_local_type(Decl1),
	a_close(H1,H2),
	getval(current_domain,Dom),
	insert_clause(formula(Dom,Name,schema,schema(Decl1,H2))),
	ilf_state(debug,_,D),
	writeln(ok),!.
make_user_type(Key,Cont,_,_) :- 
	printf("ILF ERROR in %w %w.\n",[Key,Cont]),fail.
	
make_sel_decl([gives(F,T)|L],Typ,[X|Var]) :-
	add_attribute(X,T),
	FF=..[F,Y],
	add_attribute(Y,Typ),
	make_user_type(func,FF,T,_),
	make_sel_decl(L,Typ,Var),!.
make_sel_decl([],_,[]).

set_valued([gives(_,and(_,M))|L]) :-
	syntax_type(M,and([],set)),!,
	set_valued(L),!.
set_valued([]).

get_hidden_variables(Term,Typ,ETerm) :-
	term_variables(Typ,TL),
	complete_parameters(TL,TL1),
	Term=..[Op|Arg],
	hidden_variables(TL1,Arg,Hidden),
	append(Hidden,Arg,Arg1),
	ETerm=..[Op|Arg1],
	(
	Hidden=[]
	;
	printf("ILF Warning: Hidden parameters %w in declaration of %w.\nI will replace %w with %w.\n",[Hidden,Term,Term,ETerm]),
	replace(with(Term,ETerm))
	),!.

complete_parameters([X|XL],LL) :- get_attribute(X,and(_,T)),
	term_variables(T,TL),
	complete_parameters(TL,TTL),
	complete_parameters(XL,XXL),
	strict_union([X],XXL,XX),
	strict_union(TTL,XX,LL),!.
complete_parameters([],[]).

hidden_variables(TL,[X|TVis],THid) :- strict_remove(X,TL,TL1),
	hidden_variables(TL1,TVis,THid),!.
hidden_variables(TL1,[],TL1).

/* Ende Syntax-Typ */

learn_formula :- getval(current_domain,Domain),
	write("Name:"),
	read(Name),
	write("Contents: "),
	read(Contents),
	safe_transaction(insert_clause(formula(Domain,Name,fla,Contents))),!.

/* ------ Beweisdarstellung ---------- */


gen_typed_sym(F,T) :- safe_transaction(retrieve_clause(reservation(V,T))),
	concat_string(["c_",V,"_"],RootString),!,
	repeat,
	gensym(RootString,F),
	not safe_transaction((
		retrieve_clause(definition(_,user_type(F,_)))
		;
		retrieve_clause(definition(_,(user_type(F,_) :- _)))
	)),!.
gen_typed_sym(F,and(_,M)) :- functor(M,OpM,_),
	concat_string([OpM,"_"],OpS),
	repeat,
	gensym(OpS,F),
	not safe_transaction((
		retrieve_clause(definition(_,user_type(F,_)))
		;
		retrieve_clause(definition(_,(user_type(F,_) :- _)))
	)),!.

gen_typed_var(F,T) :- safe_transaction(retrieve_clause(reservation(V,T))),
	concat_string([V,"_"],RootString),!,
	repeat,
	gensym(RootString,F),
	not safe_transaction((
		retrieve_clause(definition(_,user_type(F,_)))
		;
		retrieve_clause(definition(_,(user_type(F,_) :- _)))
	)),!.
gen_typed_var(F,and(_,M)) :- functor(M,OpM,_),
	concat_string(["X_",OpM,"_"],OpS),
	repeat,
	gensym(OpS,F),
	not safe_transaction((
		retrieve_clause(definition(_,user_type(F,_)))
		;
		retrieve_clause(definition(_,(user_type(F,_) :- _)))
	)),!.

standard_vars(T,TT) :- term_variables(T,V),
	copy_term((T,V),(TT,VV)),
	retract_all(last_var_name(_,_)),
	gen_standard_vars(V,VVV),
	open("",string,S),
	write(S,VVV),
	seek(S,0),
	read(S,VV),
	close(S),
	!.
	
gen_standard_vars([X|V],[XX|VV]) :- 
	gen_standard_vars(V,VV),
	standard_var(X,XX),!.
gen_standard_vars([],[]).

standard_var(X,XX) :- get_attribute(X,and(A,M)),
	(
	var_has_typterm(OpA,and(A,M))
	;
	M=..[Op|_],concat_string(["X_",Op],OpA)
	),
	(retract(last_var_name(OpA,N));N=0),
	(N1 is N+1),
	concat_string([OpA,"_",N1],XX),
	assert(last_var_name(OpA,N1)),!.
standard_var(_,XX) :-
	(retract(last_var_name(unknown,NL));NL=[]),
	next_var_name_l(NL,NL1),
	string_list(XX,NL1),
	assert(last_var_name(unknown,NL1)),
	!.

next_var_name_l([],[65]) :- !.
next_var_name_l([90],[90,65]) :- !.
next_var_name_l([N],[N1]) :- N1 is N+1,!.
next_var_name_l([N|L],[N|L1]) :- next_var_name_l(L,L1),!.
	
/* Interaktive Konstruktion von Objekten */
complete_schema(schema([],F),F,[]) :- !.
complete_schema(schema(Decl,F),F1,[T/X|TL]) :-
	test_local_type(Decl),
	Decl=[gives(T,Typ)|Decl1],
	complete_decl_schema(T,Typ,F,X),
	erase_test_local_type(Decl),
	S1=schema(Decl1,F),
	substitute_op(S1,S2,T,X),
	complete_schema(S2,F1,TL),
	!.

complete_schema(schema(Decl,F),F1,TL) :-
	is_shorthand(Decl,Decl1),
	test_local_type(Decl1),
	is_shorthand(F,FF),	
	show_fla(FF,S,text),
	printf("Complete schema %w\n",[S]),
	get_schema_pars(Decl,TL),
	erase_test_local_type(Decl1),
	replace_schema_pars(F,TL,F1),!.

complete_decl_schema(T,Typ,F,X) :-
	term_variables(T,V),
	copy_term((T,Typ,V),(T1,Typ1,V1)),
	(length(V,0),Subst=[];
	printf("Assume that\n",[]),
	print_typed_args(V,V1,Subst,1)),
	(Typ1=and([],Typ2);Typ2=Typ1),
	show_fla(F,FF,text),
	printf("Supply value of type %w for %w such that we have\n%w\n",[Typ2,T1,FF]),
	read(X1),
	substitute(X1,X2,U,atom(U),Subst),
	expand_fla(X2,X),!.

substitute_op(X,X,T,V) :- get_attribute(X,Typ),!,
	Typ=and(A,M),
	substitute_op(A,A1,T,V),substitute_op(M,M1,T,V),
	setarg(1,Typ,A1),
	setarg(2,Typ,M1),!.
substitute_op(X,X,_,_) :- var(X),!.
substitute_op(F,F1,T,V) :- not not F=T,!,
	copy_term(T,TT),
	TT=..[_|TTV],
	TT=F,
	substitute_op_l(TTV,VVV,T,V),
	copy_term((T,V),(T1,F1)),
	T1=..[_|VVV],!.
substitute_op(F,F1,T,V) :- F=..[Op|Arg],
	substitute_op_l(Arg,Arg1,T,V),
	F1=..[Op|Arg1],!.

substitute_op_l([E|L],[E1|L1],T,V) :- substitute_op(E,E1,T,V),
	substitute_op_l(L,L1,T,V).
substitute_op_l([],[],_,_).


get_schema_pars([gives(T,Typ)|Decl],[T/X|TL]) :-
	term_variables(T,V),
	copy_term((T,Typ,V),(T1,Typ1,V1)),
	(length(V,0),Subst=[];
	printf("Assume that\n",[]),
	print_typed_args(V,V1,Subst,1)),
	(Typ1=and([],Typ2);Typ2=Typ1),
	printf("Supply value of type %w for %w\n",[Typ2,T1]),
	read(X1),
	expand_fla(X1,X2),
	substitute(X2,X,U,atom(U),Subst),
	get_schema_pars(Decl,TL),!.
get_schema_pars([],[]).

print_typed_args([X|XL],[V|VL],[[V,X]|SL],N) :-
	concat_atom(['x_',N],V),
	get_attribute(X,A),
	printf("%w has type %w\n",[V,A]),
	(N1 is N+1),
	print_typed_args(XL,VL,SL,N1),!.
print_typed_args([],[],[],_).

replace_schema_pars(X,_,X) :- var(X),!.
replace_schema_pars(F,TL,F1) :- copy_term(TL,TL1),
	member(F/FF,TL1),!,
	FF=..[Op|Arg],
	replace_schema_pars_l(Arg,TL,Arg1),
	F1=..[Op|Arg1],!.
replace_schema_pars(F,TL,F1) :-
	F=..[Op|Arg],
	replace_schema_pars_l(Arg,TL,Arg1),
	F1=..[Op|Arg1],!.

replace_schema_pars_l([E|L],TL,[E1|L1]) :-
	replace_schema_pars(E,TL,E1),replace_schema_pars_l(L,TL,L1),!.
replace_schema_pars_l([],_,[]).


complete_term(X,T,Offen,V) :- repeat,
        write("Submit value from "),
        (T = and([],T1) -> write(T1);write(T)),
        nl,
        write("1. directly\n2. with TreeViewer\n"),
        write("3. interactively\n"),
        read(A),integer(A),!,complete_term(X,T,A,Offen,V),!.

complete_term(FF,C,1,OffenQ,V) :- read(F),expand_fla(F,F1),
	substitute(F1,FF,U,(atomic(U),member([U,_],V)),V),
	open_type_condition(F1,C,Offen),
	quantify_open(Offen,V,OffenQ),!.
complete_term(F,C,2,Offen,_V) :-
        show_proof,
        select_prompt(subterm),!,
        get_pad_term_tv(F),
        expand_fla(F,F1),
        open_type_condition(F1,C,Offen),!.
complete_term(F,C,3,Offen,_V) :- 
	constructor(F,C,Offen).

open_type_condition(F,C,[]) :- syntax_type(F,C),!.
open_type_condition(F,C,[(F is C)/unproved]) :- syntax_type(C,and([],type)),!.
open_type_condition(F,C,[in(F,C)/unproved]).

diff_type_condition(_,T,T,[]) :- !.
diff_type_condition(T,and(A0,M),and(A1,M),C) :- 
	make_diff_pred(T,A0,A1,C),!.
diff_type_condition(F,T1,_,[(F is T1)/unproved]) :- 
	syntax_type(T1,and([],type)),!.
diff_type_condition(F,C,_,[in(F,C)/unproved]).

make_diff_pred(T,[non(A)|AL],[not(P)/unproved|C]) :- 
	A=..[Op|Arg],P=..[Op,T|Arg],
	make_diff_pred(T,AL,C),!.
make_diff_pred(T,[A|AL],[P/unproved|C]) :-
	A=..[Op|Arg],P=..[Op,T|Arg],
	make_diff_pred(T,AL,C),!.
make_diff_pred(_,[],[]).

constructor(X,Typ,Offen) :- 
	printf("Constructing an object from %w as\n",[Typ]),
	supertypes(Typ,TL),
	list_select(TL,T),
	construction(X,Typ,T,Offen),!.

supertypes(T,[T|TL]) :- T=and(_,M),user_widens(M,T1),
	supertypes(T1,TL),!.
supertypes(T,[T]).

list_select(TL,T) :- list_menu(TL,1,N),nth_member(TL,N,T).

list_menu([T|TL],N,TT) :- printf("%w. %w\n",[N,T]),(N1 is N+1),
	list_menu(TL,N1,TT),!.
list_menu([],N,I) :- writeln("Select! (0 aborts)"),read(I),integer(I),
	0 < I, I =< N,!.
	
nth_member([T|_],1,T) :- !.
nth_member([_|TL],N,T) :- (N1 is N-1),nth_member(TL,N1,T),!.

construction(Str,Typ,STyp,Offen) :-
	STyp=and(_,MS),
	safe_transaction(retrieve_clause(struct(_,and(B,MS),Constr,Selectors))),
	gen_typed_sym(StrS,STyp),
	printf("Building a structure %w from %w\n",[StrS,STyp]),
	assert(local_type(StrS,Typ)),
	Str=StrS,
	construct_components(Str,Selectors,Comp,OffenSel),
	diff_type_condition(Str,Typ,and(B,MS),OffenX),
	Constr=..[_|Comp],
	append(OffenSel,[
		((Str is and(B,MS))/rule([constructor(MS)],[])),
		((Str = Constr)/rule([constructor(MS)],[]))
		|OffenX],Offen),
	printf("Structure %w = %w of type %w constructed.\n",[Str,Constr,and(B,MS)]),
	!.

construct_components(Str,[gives(S,T)|Sel],[C|Comp],OffenSel) :-
	printf("Building component %w of %w\n",[S,Str]),
	complete_term(C,T,OffenC),
	construct_components(Str,Sel,Comp,OffenR),
	append(OffenC,OffenR,OffenSel),!.
construct_components(_,[],[],[]).

quantify_open([F/R|L],V,[F1/R|LQ]) :- term_variables(F,FV),
	quantify_open_fla(F,V,FV,F1),
	quantify_open(L,V,LQ),!.
quantify_open([],_,[]).

quantify_open_fla(F,[[_,Y]|V],FV,all(Y,F1)) :-
	strict_member(Y,FV),
	quantify_open_fla(F,V,FV,F1),!.
quantify_open_fla(F,[_|V],FV,F1) :- quantify_open_fla(F,V,FV,F1),!.
quantify_open_fla(F,[],_,F).

rm_all(all(_,F),F1) :- rm_all(F,F1),!.
rm_all(forall(_,F),F1) :- rm_all(F,F1),!.
rm_all(F,F).

/* Theorie mit dem TreeViewer aufsammeln */

collect_theory(L,Prop) :- not Prop=[_|_],!,collect_theory(L,[Prop]).
collect_theory(_,_) :- 
	not(ilf_state(treeviewer, active); ilf_state(treeviewer, on)),
	ilf_warning("ilf_state treeviewer must be on\n", []),!,fail.
collect_theory(_,[_|Props]) :- length(Props,N),6 < N,
	ilf_warning("You can specify at most 7 properties.\n", []),!,fail.
collect_theory(_,_) :- retract_all(noted_ax(_,_,_)),retract_all(noted_dom(_,_)),fail.
collect_theory(_,Props) :- display_domains(Props),fail.
collect_theory(L,_) :- setof(H/S,displayed_ax(H,S),L),!.
collect_theory([],_).

display_domains(Props) :- print_prop_colors(Props),fail.
display_domains(_) :- transaction(display_the_domains),fail.
display_domains(_) :- write("Unfold domains or change property by clicking with right mouse button"),
	nl,
	write("Click root to continue"),nl,fail.
display_domains(Props) :- repeat,
	tree_write(get_handle),
	tree_read(Node),
	not change_node_prop(Node,Props),!.

print_prop_colors(Prop) :-
	write("We use the following colors:\nWhite: Folded or fixed\n"),
	print_prop_colors1(Prop),fail.

print_prop_colors1([]) :- !.
print_prop_colors1([P|PL]) :- length(PL,N),
	color_code(N,_,C),
	printf("%w: %w\n",[C,P]),
	print_prop_colors1(PL),!.

color_code(0,yellow,"Yellow: ").
color_code(1,magenta,"Magenta:").
color_code(2,red,"Red:    ").
color_code(3,cyan,"Cyan:   ").
color_code(4,green,"Green:  ").
color_code(5,blue,"Blue:   ").
color_code(6,black,"Black:  ").

display_the_domains :- tree_write(root(continue)),
	tree_write(set_info(continue,continue)),
	fail.
display_the_domains :- retrieve_clause(domain(Dom,title,T)),
	tree_write(new_edge(continue,Dom)),
	tree_write(set_info(Dom,Dom)),
	tree_write(set_contents(Dom,T)),
	tree_write(set_shape(Dom,1)),
	assert(noted_dom(Dom,folded)),
	fail.
display_the_domains :- tree_write("call(GeometryRootRight,[])"),
	tree_write(update),!.

change_node_prop(continue,_) :- !,fail.
change_node_prop(Dom,Prop) :- retract(noted_dom(Dom,folded)),!,
	safe_transaction(ax_to_tv(Prop,Dom)),
	tree_write(set_shape(Dom,2)),
	get_prop_dom_color(Dom,Prop,Col,Status),
	tree_write(set_color(Dom,Col)),
	tree_write(update),
	assert(noted_dom(Dom,Status)),!.
change_node_prop(Dom,Prop) :- retract(noted_dom(Dom,Status)),
	get_next_prop_color(Prop,Status,Color1,Status1),
	tree_write(set_color(Dom,Color1)),
	tree_write(update),
	assert(noted_dom(Dom,Status1)),!.
change_node_prop(Dom-Name,Prop) :- retract(noted_ax(Dom,Name,Status)),
	get_next_prop_color(Prop,Status,Color1,Status1),
	tree_write(set_color(Dom - Name,Color1)),
	tree_write(update),
	assert(noted_ax(Dom,Name,Status1)),!.
	
get_prop_dom_color(Dom,Prop,Col,Status) :-
	(
	safe_transaction(retrieve_clause(domain(Dom,status,Status)))
	;
	Status=active
	),
	get_status_color(Prop,Status,Col),!.

get_status_color([P|L],P,Col) :- length(L,N),color_code(N,Col,_),!.
get_status_color([_|L],P,Col) :- get_status_color(L,P,Col),!.
get_status_color(_,_,white).

get_next_prop_color([P|L],fixed,Col,P) :- length(L,N),color_code(N,Col,_),!.
get_next_prop_color([P,Q|L],P,Col,Q) :- length(L,N),color_code(N,Col,_),!.
get_next_prop_color([_|L],P,Col,P1) :- 
	get_next_prop_color(L,P,Col,P1),!.
get_next_prop_color([],_,white,fixed).
	
ax_to_tv(Prop,Dom) :- 
	setof(Name/Cont/Status,ax_cont_stat(Dom,Name,Cont,Status),NCL),
	ax_to_tv(Prop,Dom,NCL),!.
ax_to_tv(_,_).

ax_to_tv(Prop,Dom,[Name/Cont/Status|NCL]) :-
	tree_write(new_edge(Dom,(Dom - Name))),
	tree_write(set_info(Dom - Name,Name)),
	tree_write(set_contents(Dom - Name,Cont)),
	get_status_color(Prop,Status,Col),
	tree_write(set_color(Dom - Name,Col)),
	assert(noted_ax(Dom,Name,Status)),
	ax_to_tv(Prop,Dom,NCL),!.
ax_to_tv(_,_,[]).

ax_cont_stat(Dom,Name,Cont,Status) :- 
	retrieve_clause(formula(Dom,Name,fla,Cont)),
	once((retrieve_clause(formula(Dom,Name,status,Status));Status=active)).


displayed_ax(Dom - Name,S) :- noted_ax(Dom,Name,S).
displayed_ax(Dom,S) :- noted_dom(Dom,S).

extract_selected([(H/S)|L],SL,[H|L1]) :- member(S,SL),
	extract_selected(L,SL,L1),!.
extract_selected([_|L],SL,L1) :- extract_selected(L,SL,L1),!.
extract_selected([],_,[]).

/* Verschieben von Formeln */

move_fla(X,_,X) :- ilf_warning("Source and target domain must be different.\nNo formula moved.",[]),!,fail.
move_fla(_,Name,X) :- transaction(retrieve_clause(formula(X,Name,fla,C))),
	ilf_warning("%w: %w\nexists in domain %w.\nOverwrite it? (y.n.)",[Name,C,X]),not read(y),!,fail.
move_fla(_,_,D) :- not domain(D),
	ilf_warning("Domain %w does not exist.\nCreate new? (y.n.)",[D]),
	not (read(y),transaction(make_user_type(domain,D,_,_))),
	writeln("Nothing changed."),!,fail.
move_fla(SourceDomain,Name,TargetDomain) :- 
	transaction(get_formula_cdom(SourceDomain,Name,TargetDomain,L)),
	insert_clause_l(L),!.

get_formula_cdom(Dom,Name,Dom1,L) :- 
	bagof(formula(Dom1,Name,W,X),retract_clause(formula(Dom,Name,W,X)),L),!.


/* Ende Verschieben von Formeln */
/* Ungetypte Theorien */

load_untyped_theory(F) :- atom(F),!,
	concat_string(["th/",F,".t"],FiletS),
	get_uih_file(FiletS,Filet),
	concat_string(["th/",F,".th"],FilethS),
	get_uih_file(FilethS,Fileth),
	load_untyped_theory(Filet,Fileth),!.
load_untyped_theory(Filet) :-
	concat_string([Filet,"h"],Fileth),
	load_untyped_theory(Filet,Fileth),!.

load_untyped_theory(Filet,_) :- not exists(Filet),!,
	ilf_error("File %w not found\n",[Filet]),fail.
load_untyped_theory(Filet,Fileth) :- exists(Fileth),
	up_to_date(Fileth,Filet),!,
	load_th(Fileth),!.
load_untyped_theory(Filet,Fileth) :-
	make_theory_typed(Filet),
	load_th(Fileth),!.

up_to_date(Fileth,Filet) :-
	get_file_info(Filet, mtime, Datet),
	get_file_info(Fileth, mtime, Dateth),
	Datet < Dateth,!.

make_theory_typed(F) :- make_theory_typed(F,set).

make_theory_typed(F,Typ) :- atom(F),
	concat_string(["th/",F,".t"],FileS),
	get_uih_file(FileS,File),
	make_theory_typed(File,Typ),!.
make_theory_typed(File,Typ) :- 
	once((
		exists(File)
		;
		ilf_warning("File %w not found",[File]),fail
	)),
	once((
		atom(Typ)
		;
		ilf_warning("Type %w is not an atom",[Typ]),fail
	)),
	see(File),
	read_untyped_theory,
	seen,
	write_typed_theory(File,Typ),!.

read_untyped_theory :- retract_all(tmp(_)),fail.
read_untyped_theory :- repeat,read(X),not read_untyped_ax(X),!.

read_untyped_ax(end_of_file) :- !,fail.
read_untyped_ax(?-(X)) :- assert(tmp(ax('?-',X))),(call(X);true),!.
read_untyped_ax(:-(X)) :- assert(tmp(ax('?-',X))),(call(X);true),!.
read_untyped_ax(domain(Name)) :- assert(tmp(ax(ilf_domain,Name))),!.
read_untyped_ax((Name : Ax)) :- get_ax_decl(Ax,Ax1),assert(tmp(ax(Name,Ax1))),!.
read_untyped_ax(fla(':'(Name,Ax))) :- read_untyped_ax(':'(Name,Ax)),!.
read_untyped_ax(Ax) :- get_ax_decl(Ax,Ax1),assert(tmp(ax(unknown,Ax1))),!.

get_ax_decl(Ax,Ax1) :- get_ax_decl(Ax,[],V),
	(
	V=[],Ax1=Ax
	;
	V=[X],Ax1=all(X,Ax)
	;
	Ax1=forall(V,Ax)
	),!.

get_ax_decl(X,_,[]) :- var(X),ilf_warning("Axiom expected, Variable %w found",[X]),!,fail.
get_ax_decl(all(X,Ax),V,Free) :- get_ax_decl(Ax,[X|V],Free),!.
get_ax_decl(ex(X,Ax),V,Free) :- get_ax_decl(Ax,[X|V],Free),!.
get_ax_decl(forall(XL,Ax),V,Free) :- strict_union(XL,V,V1),
	get_ax_decl(Ax,V1,Free),!.
get_ax_decl(exists(XL,Ax),V,Free) :- strict_union(XL,V,V1),
	get_ax_decl(Ax,V1,Free),!.
get_ax_decl(Ax,V,Free) :- log_op(Ax,_),!,
	Ax=..[_|Arg],
	get_ax_decl_l(Arg,V,Free),!.
get_ax_decl(Ax,V,Free) :- Ax=..[_|Arg],functor(Ax,Op,N),
	assert(tmp(pred(Op,N))),
	get_tm_decl_l(Arg,V,Free),!.

get_ax_decl_l([A|Arg],V,Free) :- get_ax_decl(A,V,FreeA),
	get_ax_decl_l(Arg,V,FreeL),
	strict_union(FreeA,FreeL,Free),!.
get_ax_decl_l([],_,[]).

get_tm_decl(X,V,[]) :- var(X),strict_member(X,V),note_used_var(X),!.
get_tm_decl(X,_,[X]) :- var(X),note_used_var(X),!.
get_tm_decl(Ax,V,Free) :- Ax=..[_|Arg],functor(Ax,Op,N),
	assert(tmp(op(Op,N))),
	get_tm_decl_l(Arg,V,Free),!.

get_tm_decl_l([A|Arg],V,Free) :- get_tm_decl(A,V,FreeA),
	get_tm_decl_l(Arg,V,FreeL),
	strict_union(FreeA,FreeL,Free),!.
get_tm_decl_l([],_,[]).

note_used_var(X) :- get_var_info(X,name,N),
	get_var_root(N,R),
	assert(tmp(var(R))),!.

write_typed_theory(F,Typ) :- concat_string([F,"h"],File),
	open(File,write,typed_theory),
	pathname(F,_,Nameth),
	string_length(Nameth,NameL),
	(NameL1 is NameL - 2),
	substring(Nameth,1,NameL1,Name),
	atom_string(Domain,Name),
	atom_string(Fa, F),
	Domainstruct=..[Domain,Fa],
	printf(typed_theory,"domain %QDw.\n\n",[Domainstruct]),
	setval(ax_cnt,1),
	write_typed_theory(Typ),
	close(typed_theory),
	printf("File %w written.\n",[File]),!.

write_typed_theory(Typ) :- not Typ=set,printf(typed_theory,"mode %QDw is set.\n\n",[Typ]),fail.
write_typed_theory(Typ) :- 
	once((
		(setof(V,tmp(var(V)),VL);VL=[]),
		strict_union(['X'],VL,VL1),
		list_body(VL1,VB),
		printf(typed_theory,"reserve %Dw for %QDw.\n\n",[VB,Typ])
	)),fail.
write_typed_theory(_) :- setof(Op/N,tmp(pred(Op,N)),OpL),
	make_typed_pred(OpL),fail.
write_typed_theory(Typ) :- setof(Op/N,tmp(op(Op,N)),OpL),
	make_typed_func(OpL,Typ),fail.
write_typed_theory(_) :- tmp(ax(Name,Ax)),write_typed_ax(Name,Ax),fail.
write_typed_theory(_).

write_typed_ax(unknown,Ax) :- getval(ax_cnt,N),
	write_typed_ax(axiom(N),Ax),!.
write_typed_ax('?-',Ax) :- printf(typed_theory,"\n?- %QDw.\n\n",[Ax]),!.
write_typed_ax(ilf_domain,Name) :- printf(typed_theory,"\n domain %w.\n\n",[Name]),!.
write_typed_ax(Name,Ax) :- 
	printf(typed_theory,"fla %QDw : %QDw.\n\n",[Name,Ax]),
	incval(ax_cnt),!.

make_typed_pred([((=)/2)|OpL]) :- make_typed_pred(OpL),!.
make_typed_pred([Op/N|OpL]) :- 
	get_literal(Op,N,"X",S),
	printf(typed_theory,"pred %Dw.\n",[S]),
	make_typed_pred(OpL),!.
make_typed_pred([]) :- printf(typed_theory,"\n",[]).

make_typed_func([Op/N|OpL],Typ) :- 
	get_literal(Op,N,"X",S),
	printf(typed_theory,"func %Dw gives %QDw.\n",[S,Typ]),
	make_typed_func(OpL,Typ),!.
make_typed_func([],_) :- printf(typed_theory,"\n",[]).

get_literal(Op,0,_,S) :- term_string(Op,S),!.
get_literal(Op,N,Root,S) :- get_lit_argS(N,Root,1,SArg),
	term_string(Op,OpS),
	concat_string([OpS,"(",SArg,")"],S),!.

get_lit_argS(N,Root,N,S) :- concat_string([Root,"_",N],S),!.
get_lit_argS(N,Root,I,S) :- (I1 is I+1),
	get_lit_argS(N,Root,I1,S1),
	concat_string([Root,"_",I,",",S1],S),!.
	
			
/* Ende ungetypte Theorien */

/* Protein-Theorien */
load_tme_theory(F) :- get_right_file("dedsys/protein/tme2t",Exe),
	get_tme_t_file(F,Ft),
	concat_string([Exe," ",F," ",Ft],Cmd),
	system(Cmd),
	load_untyped_theory(Ft),!.

get_tme_t_file(F,Ft) :- last_slash_pos(F,Pos),
	string_length(F,NF),
	(L is NF-Pos-1),
	substring(F,Pos,L,F1),
	concat_string(["th",F1],F2),
	get_uih_file(F2,Ft),!.

last_slash_pos(String,Pos) :- 
	string_length(String,LString),
	substring(String,Pos,1,"/"),
	(L is LString - Pos),
	(Pos1 is Pos+1),
	substring(String,Pos1,L,String1),
	not substring(String1,"/",_),!.


/* Theorien editieren */
edit_theory :- ilf_state(tcl,off),!,
	ilf_warning("Sorry, the editor needs Tcl/Tk\n"),fail.
edit_theory :- get_uih_file("th",Dir),
	start_genEdit(Dir,"*.th"),!.

edit_untyped_theory :- ilf_state(tcl,off),!,
	ilf_warning("Sorry, the editor needs Tcl/Tk\n"),fail.
edit_untyped_theory :- get_uih_file("th",Dir),
	start_genEdit(Dir,"*.t"),!.

/* Unterstuetzung fuer TPTP */
  
create_tptp_menu :-
	getenv('TPTPHOME', TPTP_Home),
	concat_string([TPTP_Home, "/Problems"], TPTP_Problems),
	get_file_info(TPTP_Problems, mode, Mode),
	(8'40000 is Mode /\ 8'170000), 
	concat_string([TPTP_Home, "/TPTP2X/format.ilf"], TPTP_format_ilf),
	exists(TPTP_format_ilf),
	!,
	concat_string(["add_pulldown(THEORY_File, [[fileselect, ",
		"Load TPTP Problem, Select TPTP problem, ",
		TPTP_Problems, ", *, load_tptp_problem(#)]])\n"], XCmd),
	xcommand(XCmd).
create_tptp_menu.

load_tptp_problem(TPTP_File):-
	tptp_name(TPTP_File, Domain, Name),
	get_uih_file("th", ThPath),
	concat_string([ThPath, "/", Name, ".t"], Th_File),	
	(
		exists(Th_File),
		up_to_date(Th_File, TPTP_File)
		;
		tptp_transform(TPTP_File, Th_File, Name, Domain)
	),
	forget_th,
	load_untyped_theory(Th_File),
	!.

tptp_transform(TPTP_File, Th_File, Name, Domain) :-
	get_uih_file("tmp", Tmp_Path),
	concat_string([Tmp_Path, "/", Domain, "/", Name, ".t"], Tmp_File),
	concat_string([
		"$TPTPHOME/TPTP2X/tptp2X -filf -q2 -d", 
		Tmp_Path, " ", TPTP_File], Command),
	write("Calling tptp2X ... "), flush(stdout),
	sh(Command),
	exists(Tmp_File),
	writeln("Done.\n"), flush(stdout),
	concat_string(["mv -f ", Tmp_File, " ", Th_File], Command1),
	sh(Command1),
	concat_string([Tmp_Path, "/", Domain], Tmp_Dir),
	concat_string(["rm -rf ", Tmp_Dir], Command2),
	sh(Command2),
	!.
tptp_transform(TPTP_File, _, _, _) :-
	ilf_error("Translation of %w \n\
into ILF format failed. Please make sure, that format.ilf (this file can\n\
be found in $ILFHOME/doc) is installed properly.\n\
Write to ilf-serv-request@mathematik.hu-berlin.de if you need assistance.", 
	[TPTP_File]),
	fail.

?- make_local_array(tptp_slash_pos).

tptp_name(Path, _, _):-
	setval(tptp_slash_pos, [0, 0]),
	substring(Path, Pos, 1, "/"),
	once((
		getval(tptp_slash_pos, [_, Pos0]),
		setval(tptp_slash_pos, [Pos0, Pos])
	)),
	fail.
tptp_name(Path, Domain, Name):-
	getval(tptp_slash_pos, [Pos0, Pos1]),
	Pos0 > 0,
	Pos1 > 0,
	(DomainPos is Pos0 + 1),	% in thman.pl ist prec(is) > pred(,)!
	(DomainLength is Pos1 - DomainPos),
	substring(Path, DomainPos, DomainLength, Domain),
	(NamePos is Pos1 + 1),
	(NameLength is string_length(Path) - Pos1),
	substring(Path, NamePos, NameLength, Name1),
	append_strings(Name, ".p", Name1),
	!.

?- thman_top.
/* Ende File thman.pl */
