/* ilf_serv.pl 1.5 (09/15/97) based on
 * @(#)ilf_serv.pro	1.41 (12/6/95)
 *
 * Hauptmodul fuer den Ilf-Mailserver.
 * Dieser Modul ersetzt ilfsys/exman. Um eine Benutzung der normalen 
 * Ilf-Moduln fuer den Serverbetrieb zu ermoeglichen, wird er auch im
 * normalen Ilf-Betrieb geladen.
 *
 * Es werden nur die Teile benutzt, die innerhalb von ILF ohne Mailbetrieb
 * relevant sind.
 *
 */
 
:- module(ilf_serv).

?- export
	(ilf_serv_top/0),
	(ilf_serv_error/4),
	(ilf_serv_error/1),
	(ilf_serv_log/1),
	(ilf_serv_only/1),
	(ilf_serv_do/0),
	(msg_write/1),
	nth_ax/5,
	(translit/2),
	(check_me_proof/0),
	(fix_me_status/0),
	(fix_handle/0),
	(refix_handle/0).

:- dynamic 
	transliteration/2,
	(contra_list/3),
	(instance_list/4),
	(used_contra/2),
	(used_ax/2),
	(contra_dummy/4),
	lop_name/2,
	(me_proof_error/1),
	(me_proof_error/4),
	(me_log_counter/1),
	(me_root/3),
	(me_proof_sign/1),
	(me_last_nr/1),
	sproof/3.

:- import parasys.
:- import ilfsys.
	
:- export ini_system/2.

% :- tool(search_results/3).

?- begin_module(ilf_serv).

/***********               Initalisierung              *************/

/* ilf_serv_top/0 stellt fest, ob der Modul ilfsys existiert.
   Falls nicht, erfolgt der Aufruf vom Ilf-Mailserver aus, d.h. 
   alle normalerweise von ilfsys erledigten Aufgaben (Einlesen der
   ilf_state's, der Signature und Oeffnen der notwendigen Moduln)
   muessen von diesem Modul durchgefuehrt werden. */

ilf_serv_top :-
	ilf_serv_ini.

ilf_serv_ini :-
	ilf_state(syntax,Renaming),
	ini_translit(Renaming).
ilf_serv_ini :-
	ilf_debug((write("Ilf-Server 1.5 (09/15/97) installed."), nl)).


/* get_ilf_states_env/0 liest die ilf_states, die von ilf_serv.exe in der
   Environment-Variable ILF_STATE uebermittelt werden. Dadurch kann
   schon vor dem Einlesen von ilf_state.pro das log-File initialisiert
   und Syntax-Fehler in signature.pro/ilf_state.pro korrekt protokolliert
   werden. Ausserdem werden alle ilf_states gesetzt, die durch Environment-
   Variablen defininiert werden*/

get_ilf_states_env :-
	make_ilf_state(ilf_serv,on),
	get_string("USERILFHOME",UIH),
	make_ilf_state(userilfhome,UIH),
	get_string("ILFHOME",IH),
	make_ilf_state(ilfhome,IH),
	get_string("PROLOGHOME",PH),
	make_ilf_state(prologhome,PH),
	get_string("ILF_STATE",IS),
	decode(IS,ISCall),
	call(ISCall),
	!.
get_ilf_states_env :-
	ilf_serv_sys_error(get_ilf_states_env).


/* get_ilf_states_file/0 liest ilf_state.pro ein. */

get_ilf_states_file :-
	get_right_file("ilf-serv/tmp/ilf_state.pro",Fullname),
   	consult(Fullname).

/* set_proof_author/0 setzt ggf. den ilf_state proof_author auf den
   Namen aus der Email-Adresse. */

set_proof_author :- 
	ilf_state(proof_author,_),
	!.
set_proof_author :-
	ilf_state(ilf_serv_address,OrgEmail),
	format_email(OrgEmail,Email),
	set_proof_system(Email,Author),
	make_ilf_state(proof_author,Author),
	!.
set_proof_author.

set_proof_system(Email,Author) :-
	ilf_state(ilf_serv_prover,setheo),
	Author is_string "Setheo \\\\" & Email,
	!.
set_proof_system(Email,Author) :-
	ilf_state(ilf_serv_prover,komet),
	Author is_string "Komet \\\\" & Email,
	!.
set_proof_system(Email,Email).

format_email(OrgEmail,Email) :-
	I is index(OrgEmail,"@",0),
	Temp is_string delete(OrgEmail,I,length(OrgEmail)-I),
	firstup(Temp,Email).
	
/* ini_logfile/0 haengt an ein vorhandenes log-File an oder oeffnet es neu */

ini_logfile :-
	ilf_state(ilf_serv_outname,Name),
	LogName is_string Name & ".log",
	create_stream(ilf_serv_log,readwrite,ascii,file(LogName)),
	(exists(LogName),
	 open(ilf_serv_log,readwrite),
	 seek(ilf_serv_log,end_of_file)
	 ;
	 tell(ilf_serv_log),
	 state(output,_,glass_tty)
	),
	!.




/* get_signature/0 liest signature.pro ein */


get_signature :-
	once(( 
		ilf_state(ilf_serv_prover,otter), 
		add_user_ops(otter)
	)),
	fail.
get_signature :-
	get_right_file("ilf-serv/tmp/signature.pro",Sigfile),
        compile(Sigfile,axioms).


/* add_user_ops/1 ergaenzt die Operator-Deklarationen, die vom Benutzer
   im Otter-Eingabe-File angegeben werden (diese wurden von o2proof.exe
   in das File <ilf_serv_name>.op kopiert). */

add_user_ops(otter) :-
	module(new_ops),
	ilf_state(ilf_serv_name,Name),
	OpIn is_string Name & ".op",
        compile(OpIn,new_ops),
	get_right_file("ilf-serv/tmp/signature.pro",Sigfile),
	tell_append(Sigfile),
	write_user_ops,
	erase_module(new_ops).

write_user_ops :-
	new_op(B,A,O),
	once( write_op_list(B,A,O) ),
	fail.
write_user_ops.

write_op_list(B,A,[H|T]) :-
	printf("?-make_op(%w,%w,'%w').\n",[B,A,H]),
	write_op_list(B,A,T).
write_op_list(B,A,Op) :-
	printf("?-make_op(%w,%w,'%w').\n",[B,A,Op]).



/* create_ilfmodules/0, initialize_ilfmodules legt an bzw. oeffnet die
   Ilf-Moduln, die von ilf_serv benoetigt werden */

create_ilfmodules :-
	create_module(ilfsys,actual),
        create_module(situation,actual),
        create_module(tactics,actual),
	create_module(axioms,actual),
	state(output_module,_,axioms),
	hash(ax_name/4,128).

initialize_ilfmodules :-
        open_right_module("pl/sunpro.pl"),
	open_right_module("pl/parasys.pl"),
	open_right_module("pl/tools.pl"),
	open_right_module("pl/thman.prm"), /* fuer se2bl */
        open_right_module("pl/ptex.pl"),
	open_right_module("pl/proof.pl"),
	open_right_module("pl/block.pl"),
        !.

/* translit/2 gibt fuer das als erstes Argument uebergebene Standard-Symbol
   ein evtl. ueber den ilf_state syntax User-definiertes Symbol zurueck. 
   ini_translit/1 legt die dafuer notwendigen Fakten transliteration/2
   an */

translit(Symbol,UserSymbol) :- transliteration(Symbol,UserSymbol), !.
translit(Symbol,Symbol).

ini_translit([]).
ini_translit([[Symbol,UserSymbol]|R]) :-
	assert(transliteration(Symbol,UserSymbol)),
	ini_translit(R).

 
/*
 * Routinen zum Einlesen von signature.pro
 */

make_op(B,A,O):-
        global_op(B,A,O),
        call((
        	retract_all(signature(_,_,O)),
        	assert(signature(B,A,O))
        ),axioms),
        !.
 
		


/***********    exman-Unterstuetzung fuer Setheo/KoMeT      *************/

/* port/1 und port/2 werden durch ein einfaches call/1 ersetzt.
   output_write/2 und msg_write/1 werden ignoriert.
   nth_ax/5 kann stark vereinfacht werden, da es fuer ilf_serv keine
   versteckten Axiome geben kann. Die fuer nth_ax/5 notwendigen 
   Praedikate werden ebenso wie ilf_serv_goal/2 von get_ax_name/2 angelegt. */

port(S,X) :- call(X,S).
port(X) :- call(X).

port_setheo(X) :- call(X,setheo).

port_komet(X) :- call(X,komet).

port_otter(X) :- call(X,otter).

port_discount(X) :- call(X,discount).

mark_actual(Nr) :- assert(actual(Nr)).

output_write(_,_).

msg_write(_).

nth_ax(_,Nr,Name,Head,Body) :-
	not formula_number(Nr,goal),
	!,
	get_flag(toplevel_module,Top),
	get_clause(ax_name/4,ax_name(Name,Head,Body,_),Nr,Top),
	!.


komet_goal(Goal,komet_goal,1,komet_goal_status,1) :-
	ilf_serv_goal(_,Goal).
otter_goal(Goal,otter_goal,1,otter_goal_status,1) :-
	ilf_serv_goal(_,Goal).


/* set_goal_no/1 bestimmt die proof/3-Zeile, deren negierter Inhalt das
   Otter-Ziel definiert, gemaess der Konvention, dass als Ziel-Klausel
   die negierte letzte Input-Klausel verwendet wird. */
 
set_goal_no :-
	once((
		assert(goal_ln(0)), assert(ln_no(0)), assert(ax_max(0))
	)),
	clause_info1(_,CI),
	once((
		retract(ln_no(N)), NN is N + 1, assert(ln_no(NN)),
		ax_max(AxMax)
	)),
	once((
		CI = [clausify,AxNo|_],
		(AxNo > AxMax) ->  
			( retract(ax_max(_)), assert(ax_max(AxNo)),
		  	retract(goal_ln(_)), assert(goal_ln(NN)) )
	)),
	fail.
set_goal_no :-
	once(( 
		retract(ln_no(_)), assert(ln_no(0))
	)),
	clause_info2(AxNo,CI),
	once((
		retract(ln_no(N)), NN is N + 1, assert(ln_no(NN)),
		goal_ln(GoalLn)
	)),
	once((
		(NN =:= GoalLn) -> 
			( CI = [copy,No|_] -> assert(goal_no(No));
						assert(goal_no(AxNo)) )
	)),
	fail.
set_goal_no :-
	retract(goal_ln(_)), retract(ln_no(_)), retract(ax_max(_)).


 

/* get_ax_name/2 ist das Frontend fuer get_lop_name/1, get_ax_name/1.
   get_lop_name/1 liest aus dem als Argument erhaltenen File Terme ein und
   assertet sie als lop_name/2.
   get_ax_name/1 erhaelt als Argument ein .lopp-File (.lop-File mit einigen
   sed-Kommandos so angepasst, dass es von Prolog gelesen werden kann). 
   Aus dem Inhalt dieses Files wird ax_name/4 (mit den durch aus get_lop/1
   erhaltenen Namen oder mit kanonischen Axiomennamen xa_vres_fli(N)) sowie
   ilf_serv_goal/1 und formula_number(N,goal) (als Goal wird die letzte 
   allnegative Klausel betrachtet), erzeugt. 
   BEI UMSTELLUNG AUF MULTIUSERDATADBASE ax_name/4 ersetzen!!!*/

get_ax_name(_,NameFile) :-
	get_lop_name(NameFile),
	fail.
get_ax_name(LoppFile,_) :-
	get_ax_name(LoppFile).

get_lop_name(File) :-
	exists(File),
	setval(ax_nr,0),
	see(File),
	repeat,
	read(X),
	incval(ax_nr),
	assert_lop_name(X),
	!.
	
assert_lop_name(end_of_file).
assert_lop_name(Name) :-
	getval(ax_nr,Nr),
	assert(lop_name(Nr,Name)),
	!,
	fail.

get_ax_name(File) :-
	setval(ax_nr,0),
	see(File),
	repeat,
	read(X),
	incval(ax_nr),
	assert_ax_name(X),!.

assert_ax_name(end_of_file) :- end_assert_ax_name.
assert_ax_name((Head :- Body)) :-
	get_flag(toplevel_module,Top),
	once((
		getval(ax_nr,Nr),
		ax_name_is(Nr,Name),
		call(assert(ax_name(Name,Head,Body,[])),Top)
	)),
	!,
	Head=false,
	call(retract_all(ilf_serv_goal(_,_)),Top),
	call(assert(ilf_serv_goal(Name,Body)),Top),
	!,
	fail.
assert_ax_name(Head) :-
	assert_ax_name((Head :- true)).

end_assert_ax_name :-
	seen,
	goal_name_is(Name),
	get_flag(toplevel_module,Top),
	get_clause(ax_name/4,ax_name(Name,_,_,_),Nr,Top),
	call(assert(formula_number(Nr,goal),Top)),
	!.

goal_name_is(goal) :-
	ax_name(goal,Head,Body,_),
	(Head=false
	 ;
	 ilf_serv_error((
	 	writeln("goal must be all-negative."), 
	 	printf("%w <- %w cannot be the goal",[Head,Body])
	 ))
	),
	top_retract_all(ilf_serv_goal(_,_)),
	assert(ilf_serv_goal(goal,Body)),
	!.
goal_name_is(Name) :-
	ilf_serv_goal(Name,_),
	!.
goal_name_is(_) :-
	ilf_serv_error(writeln("No all-negative clause in lopfile")).

ax_name_is(Nr,Name) :-
	lop_name(Nr,Name),
	!.
ax_name_is(Nr,xa_vres_fli(Nr)).

/* remove_ax_names ersetzt in einem Blockbeweis alle kanonischen Axiomennamen 
   xa_vres_fli(N) durch []. Das Gegenstueck fix_me_ax_names ersetzt alle
   Axiomennamen [] in einem ME-Beweis durch kanonische.  */
/* Falls der kanonische Name als Name des Ziels gebraucht wird, wird er in new_goal(N) umbenannt und bleibt erhalten */

remove_ax_names :- 
	top_retract(proof([Pf,global],control,goal_name(xa_vres_fli(N)))),
	top_retract(proof(H,control,axiom(xa_vres_fli(N)))),
	top_assert(proof([Pf,global],control,goal_name(new_goal(N)))),
	top_assert(proof(H,control,axiom(new_goal(N)))),
	fail.
remove_ax_names :-
	top_retract(proof(H,control,axiom(xa_vres_fli(_)))),
	top_assert(proof(H,control,axiom([]))),
	fail.
remove_ax_names.

fix_me_ax_names :- setval(i,0),fail.
fix_me_ax_names :-
	top_retract(proof(H,status,axiom([]))),
	getval(i,Pos),
	incval(i),
	top_assert(proof(H,status,axiom(xa_vres_fli(Pos)))),
	fail.
fix_me_ax_names.

/******  Routinen zur Anpassung/Fehlerkennung in den Eingabefiles   *****/

/* check_for_query/0 testet, ob ein ME-Beweis mit not query__ im  Wurzelknoten
   oder mit einer leeren root vorliegt. Im zweiten Fall werden die fuer
   me2bl notwendige query-Konstruktion erzeugt (noch nicht implementiert) */

check_for_query :-
	proof(H,contents,query__),
	(proof(H,status,none),
	 proof(H,predecessors,[Root]),
	 proof(Root,contents,not query__),
	 proof(Root,status,ext)
	 ;
	 ilf_serv_error((
	 	writeln("query__ has a special meaning for model elimination proofs."),
	 	writeln("Your proof with query__ as contents of node % is syntactically incorrect."),
	 	help_contact
	 ))
	),!.
check_for_query.

/* fix_me_status/0 testet in einem als proof/3 vorliegenden Beweis alle
   Statusangaben und ersetzt ggf. "alte" durch "neue". Dazu werden alle 
   proof(_,status,_)-Fakten zunaechst als sproof/3 zwischengespeichert 
   und dann ggf. konvertiert. */

fix_me_status :-
	proof(H,status,Status),
	assert(sproof(H,status,Status)),
	fail.
fix_me_status :-
	retract(sproof(H,status,Status)),
	once(me_status(H,Status,SetheoStatus)),
	retract(proof(H,status,Status)),
	assert(proof(H,status,SetheoStatus)),
	fail.
fix_me_status.

/* Diese sind ok: */
me_status(_,none,_) :- !,fail.
me_status(_,ext,_) :- !,fail.
me_status([PH,_],red([PH,_]),_) :- !,fail.
me_status([PH,_],fac([PH,_]),_) :- !,fail.
me_status(_,axiom(_),_) :- !, fail.
me_status(_,contra,_) :- !, fail.
/* Diese kann man mit kosmetischen Veraenderungen durchgehen lassen: */
me_status(_,ext(_,_),ext).
me_status(_,[_,ext(_,_)],ext).
me_status([PH,_],red(NH),red([PH,NH])).
me_status([PH,_],[_,red(NH)],red([PH,NH])).
me_status([PH,_],fac(NH),fac([PH,NH])).
me_status([PH,_],[_,fac(NH)],fac([PH,NH])).
me_status(_,contra(_,_),contra).
/* Alle anderen sind schlicht und einfach verboten: */
me_status(H,Stat,_) :-
	ilf_serv_error(writeln("Node % has illegal status %.",[H,Stat])).

/* fix_handle/0 setzt Handle mit einem von Nutzer angegebenen 
   handle_separator in den ILF-Standard [PH,NH] um, refix_handle/0
   macht diese Umwandlung rueckgaengig. */

fix_handle :-
	ilf_state(handle_separator,UserSeparator), 
	ilf_state(ilf_serv_type,Type),
	fix_handle(Type,UserSeparator,[]), !.
fix_handle.

refix_handle :-
	ilf_state(handle_separator,UserSeparator), 
	ilf_state(ilf_serv_type,Type),
	fix_handle(Type,[],UserSeparator), !.
refix_handle.

/* fix_handle/3 ersetzt User-definierte Handle durch den ILF-Standard 
   bzw. umgekehrt. Ersetzt werden immer die Handle in der ersten Stelle
   von proof/3 sowie die Handle der Liste von predecessors. Weitere
   Umwandlungen erfolgen typspezifisch mit fix_handle/6.  */

fix_handle(Type,Old,New) :-
	repeat(N),
	N1 is N+1,
	fix_handle(Type,Old,New,N,N1).

fix_handle(Type,OldSep,NewSep,N,N1) :-
	retract(proof/3,proof(H,Arg2,Arg3),N1),
	fix_handle(OldSep,NewSep,H,FixedH),
	fix_handle(Type,OldSep,NewSep,Arg2,Arg3,FixedArg3),
	assert(proof(FixedH,Arg2,FixedArg3),N),
	!, fail.
fix_handle(_,_,_,_,_).

fix_handle(_,OldSep,NewSep,predecessors,HList,FixedHList) :-
	fix_handle_list(OldSep,NewSep,HList,FixedHList).

fix_handle(me,OldSep,NewSep,status,red(H),red(FixedH)) :-
	fix_handle(OldSep,NewSep,H,FixedH).

fix_handle(me,OldSep,NewSep,status,fac(H),fac(FixedH)) :-
	fix_handle(OldSep,NewSep,H,FixedH).

fix_handle(block,OldSep,NewSep,control,rule(Arg1,HList),rule(Arg1,FixedHList)) :-
	fix_handle_list(OldSep,NewSep,HList,FixedHList).

fix_handle(_,_,_,_,Arg,Arg).

/* fix_handle/4 ersetzt genau ein Handle. fix_handle_list/4 ersetzt
   jedes Handle einer uebergebenen Liste */

fix_handle(Separator,[],H,[PH,NH]) :-
	(H =.. [Separator,PH,NH]
	 ;
	 ilf_serv_error(writeln("Illegal handle %.",[H]))
	).
fix_handle([],Separator,[PH,NH],H) :-
	H =.. [Separator,PH,NH].
fix_handle(_,_,H,H).

fix_handle_list(_,_,[],[]).
fix_handle_list(_,_,Var,Var) :- var(Var).
fix_handle_list(OldSep,NewSep,[H|R],[FixedH|FixedR]) :-
	fix_handle(OldSep,NewSep,H,FixedH),
	fix_handle_list(OldSep,NewSep,R,FixedR).

/************                check_me_proof                 **************/

/* check_me_proof/0 ueberprueft einen Beweis, der als proof/3 vorliegt,
   darauf, ob er einen korrekten ME-Beweis widerspiegelt. Ausserdem 
   wird eine Anpassung an das von me2bl geforderte Format vorgenommen */

check_me_proof :-
	check_me_ini,
	check_me_root,
	analyze_me_proof,
	check_me_ext,
	check_me_red,
	check_me_fac,
	!, check_me_result,
	fix_me_ax_names,
	fix_me_root,
	fix_me_proof,
	fix_me_contra.

check_me_ini :-
	check_me_clear,
	get_flag(toplevel_module,Top),
	(
	get_flag(proof/3,definition_module,Top)
	;
	(import proof/3 from Top)
	),
	assert(me_last_nr(0)),!.

check_me_clear :-
	retract_all(contra_list(_,_,_)),
	retract_all(instance_list(_,_,_,_)),
	retract_all(used_contra(_,_)),
	retract_all(used_ax(_,_)),
	retract_all(contra_dummy(_,_,_,_)),
	retract_all(me_proof_error(_)),
	retract_all(me_proof_error(_,_,_,_)),
	retract_all(me_log_counter(_)),
	retract_all(me_root(_,_,_)),
	retract_all(me_proof_sign(_)),
	retract_all(me_last_nr(_)).

check_me_result :-
	me_proof_error(N),
	ilf_serv_log(printf("PROOF CHECK SUMMARY:  %w error(s) detected.\nIf you don't understand any of the above messages or disagree with a\nparticular message please contact ilf-serv-request@mathematik.hu-berlin.de.\n",
	[N])),
	!, fail.
check_me_result :-
	ilf_serv_log(writeln("me proof check passed")).
	
/* check_me_root/0 findet die Wurzel des Beweisbaumes als denjenigen Knoten,
   der einen Status ext hat und als einzigen Vorgaenger eine Kontraposition
   bzw. ein Axiom (werden mehrere solcher Knoten gefunden, fuehrt das zu einer 
   Fehlermeldung). Das Handle der Wurzel, das Handle des zugehoerigen Axioms
   und das Handle der verwendeten  Kontraposition wird als me_root/3 
   gespeichert. */
   
check_me_root :-
	proof(H,status,ext),
	proof(H,predecessors,[Father]),
	once((
		proof(Father,status,contra), 
		note_root_contra(H,Father)
		; 
		proof(Father,status,axiom(_)),
		note_root_axiom(H,Father)
	)),
	fail.
check_me_root :-
	me_root(_,_,_), !.
check_me_root :-
	me_proof_error(no_root,[]).

note_root_contra(H,_) :-
	me_root(R,_,_),
	me_proof_error(double_root,H,R), !.
note_root_contra(H,Contra) :-
	proof(Contra,predecessors,[Axiom]),
	proof(Axiom,status,axiom(_)),
	assert(me_root(H,Axiom,Contra)), !.
note_root_contra(H,Contra) :-
	me_proof_error(root_ax,H,Contra).

note_root_axiom(H,_) :-
	me_root(R,_,_),
	me_proof_error(double_root,H,R), !.
note_root_axiom(H,Axiom) :-
	assert(me_root(H,Axiom,[])), !.

/* fix_me_root/0 sammelt alle benutzten Instanzen des Goals (das ist entweder
   das Axiom mit dem Namen `goal' oder das an der root angewandte) und 
   speichert sie im global control used_goal. Die gefundene root wird
   fuer me2bl angepasst,  d.h. als contents  wird 'not query__' und als 
   Status 'ext' eingetragen. */

fix_me_root :-
	note_goal(Name),
	proof([PH,_],status,axiom(Name)),
	top_assert(proof([PH,global],control,goal_name(Name))),
	me_root(R,_,_),
	proof(R,contents,Cont),
	note_translit_query(Cont),
	fail.
fix_me_root :-
	me_root(R,_,_),
	top_retract_all(proof(R,status,_)),
	top_assert(proof(R,status,ext)),
	top_retract_all(proof(R,contents,_)),
	top_assert(proof(R,contents,not query__)),
	!.

note_translit_query(NotQuery) :-
	me_proof_sign(-),
	translit(not,Not),
	NotQuery =.. [Not,Query],
	call(assert(transliteration(query__,Query)),ilfsys),
	!.
note_translit_query(Query) :-
	me_proof_sign(+),
	atomic(Query),
	call(assert(transliteration(query__,Query)),ilfsys),
	!.
note_translit_query(Query) :-
	me_root(R,_,_),
	me_proof_error(root_contents,R,Query), !.

note_goal(goal) :-
	proof(H,status,axiom(goal)),
	note_used_goal(H),
	!.
note_goal(Name) :-
	me_root(_,Axiom,_),
	proof(Axiom,status,axiom(Name)),
	note_used_goal(Axiom),
	!.
	
note_used_goal(Axiom) :-
	used_ax(H,Axiom),
	proof(H,status,ext),
	note_goal_instance(H),
	fail.
note_used_goal(Axiom) :-
	used_ax(Contra,Axiom),
	used_contra(H,Contra),
	note_goal_instance(H),
	fail.
note_used_goal(_).
	
note_goal_instance(H) :-
	(proof(H,contents,Head) ; Head=[]),
	instance_list(H,Body,_,_),
	me_negation(Head,NotHead),
	make_goal([NotHead|Body],Goal),
	(top_retract(proof([PH,global],control,used_goal(OldGoal))),
	 top_assert(proof([PH,global],control,used_goal((OldGoal;Goal))))
	 ;
	 [PH1,_] = H,
	 top_assert(proof([PH1,global],control,used_goal(Goal)))
	), !.

make_goal([],_).
make_goal([Lit|R],Goal) :-
	make_goal(R,RGoal),
	me_proof_sign(Flag),
	make_goal_lit(Flag,Lit,GoalLit),
	append_lit(RGoal,GoalLit,Goal).

append_lit(Goal,Lit,Goal) :- var(Lit).
append_lit(Goal,Lit,Lit) :- var(Goal).
append_lit(Goal,[],Goal).
append_lit(Goal,Lit,(Lit,Goal)).

make_goal_lit(+,NotQuery,[]) :-
	translit(query__,Query),
	translit(not,Not),
	NotQuery =.. [Not,Query].
make_goal_lit(-,Query,[]) :-
	translit(query__,Query).
make_goal_lit(+,Lit,Lit).
make_goal_lit(-,Lit,NegLit) :-
	me_negation(Lit,NegLit).
	
/* analyze_me_proof/0 durchwandert den Baum und speichert die gewonnenen
   Information durch analyze_proof/3 */

analyze_me_proof :-
	proof(H,predecessors,L),
	once((
		(proof(H,status,Stat) ;  Stat=empty), 
		note_nr(H),
		analyze_me_proof(H,L,Stat)
	)),
	fail.
analyze_me_proof.

/* analyze_me_proof/3 wird aufgerufen mit einem Handle, der Liste der
   Vorgaenger und dem Status. Es ueberprueft, ob alles stimmig ist und
   legt contra_list/3, instance_list/4 sowie used_contra/2 fuer die 
   weitere Auswertung an. Dabei ist
   contra_list(H,Head,BodyList)   
   	H        - Handle
   	Head     - Kopfliteral
   	BodyList - Liste der Koerperliterale 
   instance_list(H,UsedBody,FirstSon,SonList)
   	H        - Handle
   	UsedBody - Liste der tatsaechlich benutzten Koerperliterale
   	FirstSon - Handle des "ersten Sohns", d.h. des Sohnes, dessen
   		   Inhalt der Komplement des Inhalts des Vaters ist
        SonList  - Liste der Handle der uebrigen, "echten" Soehne
   used_contra(H,Contra)
	H 	 - Handle
	Contra	 - Handle der benutzten Kontraposition	  */

analyze_me_proof(H,_,VarStat) :-
	var(VarStat),
	me_proof_error(var_status,H), !.
analyze_me_proof(_,[],axiom(_)) :- !.
analyze_me_proof(H,L,axiom(_)) :- 
	me_proof_error(predecessors(axiom),H,L), !.
analyze_me_proof(H,[Axiom],contra) :-
	proof(Axiom,status,axiom(_)),
	assert(used_ax(H,Axiom)),
	(proof(H,contents,C), 
	 note_contra(H,C)
	 ;
	 me_proof_error(empty_contents,H)
	), !.
analyze_me_proof(H,[Axiom],contra) :-
	me_proof_error(no_ax,H,[Axiom]), !.
analyze_me_proof(_,L,contra) :- 
	me_proof_error(predecessors(contra),L), !.
analyze_me_proof(H,[Contra],ext) :-
	me_root(H,_,Contra),
	note_ext(H,Contra), !.
analyze_me_proof(H,[Axiom],ext) :-
	me_root(H,Axiom,[]),
	note_ext(H,Axiom,[]), !.
analyze_me_proof(H,[Contra,Father],ext) :-
	proof(Contra,status,contra),
	note_ext(H,Contra),
	note_contents(H,Father), !.
analyze_me_proof(H,[Father,Contra],ext) :-
	proof(Contra,status,contra),
	note_ext(H,Contra),
	note_contents(H,Father), !.
analyze_me_proof(H,[Axiom,Father],ext) :-
	proof(Axiom,status,axiom(_)),
	note_ext(H,Axiom,[Father]),
	note_contents(H,Father), !.
analyze_me_proof(H,[Father,Axiom],ext) :-
	proof(Axiom,status,axiom(_)),
	note_ext(H,Axiom,[Father]),
	note_contents(H,Father), !.
analyze_me_proof(H,[H1,H2],ext) :-
	me_proof_error(no_contra,H,[H1,H2]), !.
analyze_me_proof(H,L,ext) :-
	me_proof_error(predecessors(ext),H,L), !.
analyze_me_proof(H,[Father],none) :-
	proof(Father,status,ext),
	note_used_head(Father,H), !.
analyze_me_proof(H,L,none) :-
	me_proof_error(predecessors(none),H,L), !.
analyze_me_proof(H,[Father],fac(_)) :-
	proof(Father,status,ext),
	note_contents(H,Father), !.
analyze_me_proof(H,L,fac(_)) :-
	me_proof_error(predecessors(fac),H,L), !.
analyze_me_proof(H,[Father],red(_)) :-
	proof(Father,status,ext),
	note_contents(H,Father), !.
analyze_me_proof(H,L,red(_)) :-
	me_proof_error(predecessors(red),H,L), !.
analyze_me_proof(H,_,empty) :-
	me_proof_error(empty_status,H), !.
analyze_me_proof(H,_,Stat) :-
	me_proof_error(unknown_status,H,[Stat]), !.

/* note_nr/1 sorgt dafuer, dass die groesste im Beweis verwendete Nummer
   als me_last_nr/1 gespeichert wird.
   me_nnr/1 gibt eine bisher noch nicht als Handle verwendete Zahl zurueck,
   sollte aber erst nach dem kompletten Durchlaufen des Baums mittels
   analyze_me_proof benutzt werden */

note_nr([_,NH]) :-
	number(NH),
	once((me_last_nr(Nr) ; Nr=0)),
	NH > Nr,
	retract_all(me_last_nr(_)),
	assert(me_last_nr(NH)).
note_nr(_).

me_nnr(Nr) :-
	retract(me_last_nr(Nr0)),
	Nr is Nr0+1,
	assert(me_last_nr(Nr)).

/* note_contents/2 ermittelt den contents eines Knoten und traegt ihn
   in die Liste der fuer den Vater benutzten Body-Literale ein. */

note_contents(_,[]) :- !.
note_contents(H,Father) :-
	(proof(H,contents,Lit),
	 note_used_body(Father,H,Lit)
	 ;
	 me_proof_error(empty_contents,H)
	).

/* note_contra/2 erzeugt contra_list/3 */

note_contra(H,Clause) :-
	translit(:-,If),
	Clause=..[If,Head,Body],
	make_body_list(H,Body,BodyList),
	assert(contra_list(H,Head,BodyList)), !.
note_contra(H,Clause) :-
	translit(:-,If),
	Clause=..[If,Body],
	make_body_list(H,Body,BodyList),
	assert(contra_list(H,[],BodyList)), !.
note_contra(H,Fact) :-
	assert(contra_list(H,Fact,[])).

make_body_list(H,Var,[]) :-
	var(Var),
	me_proof_error(var_body,H).
make_body_list(H,Body,L) :-
	translit(',',And),
	Body=..[And,C1,C2],
	make_body_list(H,C1,L1),
	make_body_list(H,C2,L2),
	append(L1,L2,L).
make_body_list(_,Lit,[Lit]).


/* note_used_head/3 und note_used_body/3 erzeugen instance_list/4.
   Sie werden aufgerufen fuer den "ersten" bzw. fuer jeden anderen
   Sohn. note_ext/2 wird fuer den Vater aufgerufen, merkt sich die
   benutzte Kontraposition in used_contra/2 und legt, wenn es noch 
   nicht vorhanden ist, instance_list/4 an (man beachte, des es
   ohne "ersten" Sohn auch "Vaeter" geben kann, die gar keine Soehne
   haben). note_ext/3 erledigt die gleiche Aufgabe fuer Extensionsschritte,
   die direkt aus den Axiomen abgeleitet sind, legt aber zusaetzlich noch
   Informationen fuer eine "dummy"-Kontraposition ab und erzeugt Fakten
   fuer used_ax mit einem Node-Handle im ersten Argument */
   
note_used_head(H,FirstSon) :-
	retract(instance_list(H,BodyList,V,Sons)),
	(var(V) ; me_proof_error(double_firstson,H,[FirstSon,V])),
	assert(instance_list(H,BodyList,FirstSon,Sons)), !.
note_used_head(H,FirstSon) :-
	assert(instance_list(H,[],FirstSon,[])).

note_used_body(H,Son,Lit) :-
	retract(instance_list(H,BodyList,FirstSon,Sons)),
	assert(instance_list(H,[Lit|BodyList],FirstSon,[Son|Sons])). 
note_used_body(H,Son,Lit) :-
	assert(instance_list(H,[Lit],_,[Son])).

note_ext(H,Contra) :-
	assert(used_contra(H,Contra)),
	(instance_list(H,_,_,_)
	 ;
	 assert(instance_list(H,[],_,[]))
	), !.

note_ext(H,_,_) :-
	ilf_state(setheo_with_contrapositives,on),
	proof_me_error(with_contra,[H]),
	fail.
note_ext(H,Axiom,Father) :-
	gensym(contra,Contra),
	assert(contra_dummy(H,Contra,Axiom,Father)),
	assert(used_ax(H,Axiom)),
	note_ext(H,none).

	
/* check_me_ext/0 ueberprueft, ob die benutzten Literale tatsaechlich 
   eine Instanz der verwendeten Kontraposition sind.
   Dazu werden die von analyze_me_proof erzeugten Fakten contra_list/3
   und instance_list/4 benutzt. 
   me_proof_sign/1 zeigt an, ob der urspruengliche Beweis positiv oder 
   negativ war (das wurde anhand der an der Wurzel angewandten Kontraposition 
   durch check_me_root/0 festgestellt). */

check_me_ext :-
	not me_root(_,_,_), !.
check_me_ext :-
	set_me_proof_sign,
	fail.
check_me_ext :-
	instance_list(H,UsedBody,FirstSon,Sons),
	check_me_ext(H,UsedBody,FirstSon,Sons),
	fail.
check_me_ext.
	
check_me_ext(H,UsedBody,FirstSon,_) :-
	proof(H,contents,Contents),
	check_me_head(H,FirstSon,Contents),
	used_contra(H,Contra),
	me_proof_sign(Flag),
	(Contra=none
	 ;
	 contra_list(Contra,Head,Body),
	 check_head_instance(Flag,Contents,Head,H,Contra),
	 check_body_instance(Flag,UsedBody,Body,H,Contra)
	), !.
check_me_ext(H,_,_,_) :-
	me_root(H,_,_), !.
check_me_ext(H,_,_,_) :-
	 me_proof_error(empty_contents,H), !.

check_head_instance(Flag,Contents,Head,_,_) :- is_instance(Flag,Contents,Head).
check_head_instance(_,Contents,Head,H,contra) :- 
	me_proof_error(head,H,[_,_,Head,Contents]).

check_body_instance(Flag,UsedBody,Body,_,_) :- is_instance(Flag,UsedBody,Body).
check_body_instance(_,_,_,H,Contra) :-
	 me_proof_error(head,H,[_,Contra,_,_]).


/* set_me_proof_sign/0 bestimmt das Vorzeichen des Beweises ('+' fuer 
   Stickl-/Prolog-Stil, '-' fuer Setheo-/Tableau-Stil) anhand der an der
   Wurzel des Beweisbaumes angewandten Kontraposition. Ist diese
   Entscheidung nicht moeglich, wird '+' angenommen. */

set_me_proof_sign :-
	ilf_state(me_proof_sign,Flag),
	assert(me_proof_sign(Flag)), !.
set_me_proof_sign :-
	me_root(_,_,[]),
	ilf_serv_log(writeln("WARNING: Assuming goal-oriented representation.\n(ilf_state me_proof_sign is not set and contrapositive for root is not available)")),
	assert(me_proof_sign(+)), !.
set_me_proof_sign :-
	me_root(Root,_,Contra),
	instance_list(Root,UsedBody,_,_),
	contra_list(Contra,_,Body),
	is_instance(Flag,UsedBody,Body),
	(Flag=0,
	 me_proof_error(body_root,Root,[Contra,UsedBody]),
	 assert(me_proof_sign(+))
	 ;
	 assert(me_proof_sign(Flag))
	), !.
	
/* check_me_head/3 testet einen evtl. vorhandenen Sohn auf seinen Inhalt.
   Ein inkorrekter Inhalt fuehrt zu einer Fehlermeldung. */

check_me_head([_,_],FirstSon,_) :- 
	var(FirstSon), !.
check_me_head(H,FirstSon,Lit) :-
	(proof(FirstSon,contents,UsedLit)
	 ;
	 me_proof_error(empty_contents,FirstSon)
	),
	(me_negation(Lit,UsedLit)
	 ;
	 me_proof_warning(head_son,H,[FirstSon])
	), !.

/* me_negation/2 gibt im zweiten Argument das Komplement des Literals im
   ersten Argument zurueck. */

me_negation([],[]) :- !.
me_negation(NotX,X) :- 
	translit(not,Not),
	NotX=..[Not,X],
	!.
me_negation(X,NotX):- 
	translit(not,Not),
	NotX=..[Not,X],
	!.

/* member(X,M,D) trifft zu, wenn M = D u {X}.  */

member(X,[X|R],R).
member(X,[Y|S],[Y|R]) :- member(X,S,R).
member(+,X,Y,Z) :- member(X,Y,Z).
member(-,X,Y,Z) :- me_negation(X,NotX), member(NotX,Y,Z).

is_instance(_,[],[]) :- !.
is_instance(Flag,[X|S],T) :- 
	!,
	(member(Flag,X,T,R), 
	 is_instance(Flag,S,R)
	 ;
	 Flag=0
	).
is_instance(+,X,X).
is_instance(-,X,NotX) :- me_negation(X,NotX).
is_instance(0,_,_).

/* check_me_fac/0, check_me_red/0 ueberprueft, ob die Partner zu
   den Knoten, die durch Faktorisierung/Reduktion abgeschlossen wurden,
   existieren und den richtigen Inhalt haben */

check_me_fac :-
        proof(H,status,fac(F)),
        once((
                proof(H,contents,Lit),
                (proof(F,contents,FLit),
                 (Lit == FLit
                  ;
                  me_proof_error(fac,H,[F,Lit,FLit])
                 )
                 ;
                 me_proof_error(empty_contents,F)
                )
        )),
        fail.
check_me_fac.

check_me_red :-
        proof(H,status,red(R)),
        once((
                proof(H,contents,Lit),
                (proof(R,contents,RLit),
                 (me_negation(RLit,NegRLit), Lit = NegRLit
                  ;
                  me_proof_error(red,H,[R,Lit,RLit])
                 )
                 ;
                 me_proof_error(empty_contents,R)
                )
        )),
        fail.
check_me_red.

/*  fix_me_proof/0 stellt den Beweisbaum ggf. auf die von me2bl geforderte
   "negative" Form um und fuegt ggf. die Negation des Vaters als ersten
   Sohn hinzu. Ausserdem werden alle Reduktionen mit der Wurzel geloescht. */

fix_me_proof :-
	me_proof_sign(+),
	instance_list(_,_,_,Sons),
	fix_me_body(Sons),
	fail.
fix_me_proof :-
	instance_list(H,_,FirstSon,_),
	fix_me_head(H,FirstSon),
	fail.
fix_me_proof :-
	me_root(R,_,_),
	top_retract(proof(H,status,red(R))),
	top_retract_all(proof(H,_,_)),
	fail.
fix_me_proof.

/* fix_me_body/1 erhaelt als Argument eine Liste von Handlen. In allen
   diesen Handlen wird der contents durch seine Negation ersetzt. */

fix_me_body([]) :- !.
fix_me_body([H|R]) :-
	top_retract(proof(H,contents,Lit)),
	me_negation(Lit,NegLit),
	top_assert(proof(H,contents,NegLit)),
	fix_me_body(R), !.
fix_me_body([H|R]) :-
	me_proof_error(empty_contents,H),
	fix_me_body(R), !.

/* fix_me_head/3 traegt den fuer me2bl notwendigen "ersten Sohn" (die Negation
   des Inhalts des Vaterknoten) ein. Ein bereits vorhandener "erster Sohn"
   wird ersetzt. Dabei muss mindestens der predecessors-Fakt des "ersten"
   Sohnes vor dem der anderen Soehne stehen (vgl. premise/4 in me2bl/0) */

fix_me_head([PH,NH],FirstSon) :-
	var(FirstSon),
	me_nnr(FirstSon),
	fix_me_head([PH,NH],[PH,FirstSon]), !.
fix_me_head(Father,FirstSon) :-
	get_flag(toplevel_module,Top),
	call(retract_all(proof(FirstSon,_,_)),Top),
	proof(Father,contents,Lit),
	me_negation(Lit,NegLit),
	call((
		assert(proof(FirstSon,contents,NegLit)),
		assert(proof(FirstSon,status,none)),
		asserta(proof(FirstSon,predecessors,[Father]))
	),Top), !.

/* fix_me_contra/0 erzeugt die dummy-Kontrapositionen. Die Informationen dafuer
   wurden mit note_ext/3 erzeugt. */

fix_me_contra :-
	get_flag(toplevel_module,Top),
	contra_dummy([PH,NH],Contra,Axiom,Father),
	once(call(
		retract(proof([PH,NH],predecessors,_)),
		assert(proof([PH,NH],predecessors,[[PH,Contra]|Father])),
		assert(proof([PH,Contra],status,contra)),
		assert(proof([PH,Contra],contents,contra)),
		assert(proof([PH,Contra],predecessors,[Axiom]))
	),Top),
	fail.
fix_me_contra.

/* me_proof_error/2,3 erzeugt die Fehlerausschriften im Logfile.
   note_me_proof_error/0 assertiert ggf. me_proof_error/1,4 fuer die
   spaetere Auswertung */
   
me_proof_error(Code,H) :- 
	note_me_proof_error(Code,H,[]),
	me_log(error,Code,H,[]).
me_proof_error(_,_). 
me_proof_error(Code,H,Info) :-
	note_me_proof_error(Code,H,Info),
	me_log(error,Code,H,Info).
me_proof_error(_,_,_).

me_proof_warning(Code,H) :-
	me_log(warning,Code,H,[]).
me_proof_warning(Code,H,Info) :-
	me_log(warning,Code,H,Info).

note_me_proof_error(Code,H,Info) :-
	me_proof_error(_,Code,H,Info),
	!,fail.
note_me_proof_error(Code,H,Info) :-
	(retract(me_proof_error(N)),
	 N1 is N+1
	 ;
	 N1 is 1
	),
	assert(me_proof_error(N1)),
	assert(me_proof_error(N1,Code,H,Info)).

me_log(Type,Code,H,Info) :-
	me_log,
	ilf_serv_log((
	 	write("PROOF CHECK "),
	 	(Type=error, write("ERROR") ; write("WARNING")),
	 	writeln(":"),
	 	me_error_msg(Code,H,Info)
	)).
me_log(_,_,_,_).

me_log :-
	(retract(me_log_counter(N)),
	 N1 is N+1
	 ;
	 N1 is 1
	 ),
	 assert(me_log_counter(N1)),
	 !, me_log(N1).

me_log(21) :-
	ilf_serv_log(writeln("\n... too many errors/warnings\n")),
	!, fail.
me_log(N) :- N < 21.

/* Fehler beim Matchen der Soehne der Wurzel gegen die Goal-Kontraposition */
me_error_msg(body_root,H,[Contra,UsedBody]) :-
	proof(Contra,contents,Contrapos),
	printf("The contrapositive %w applied at the root %w has the contents:\n",[Contra,H]),
	write(Contrapos), 
	write(",\nbut the contents of it's sons is:\n"),
	me_write_body(+,UsedBody), nl,
	printf("I cannot see that this is a proper application of %w. Therefore I am not\nable to determine the \"sign\" of your proof, I assume \"+\" (goal-oriented).\n",
	[Contra]).

/* Soehne stimmen nicht mit dem Body der verwendeten Kontraposition ueberein */
me_error_msg(body,H,[0,Contra,Contents,UsedBody]) :-
	proof(Contra,contents,Contrapos),
	printf("The contrapositive %w applied at node %w has the contents:\n",[Contra,H]),
	write(Contrapos), 
	printf(",\nbut the clause actually used (see the contents of %w and it's sons) is:\n",[H]),
	me_write_clause(Contents,UsedBody), nl,
	writeln("I cannot see that the latter is an instance of the former.").
me_error_msg(body,H,[Flag,Contra,Contents,UsedBody]) :-
	proof(Contra,contents,Contrapos),
	printf("The contrapositive %w applied at node %w has the contents:\n",[Contra,H]),
	write(Contrapos), 
	write(".\nI assume that you are using a "),
	((Flag='+'), write("tableau-style")
	 ;
	 write("goal-oriented")
	),
	printf(" representation of the ME proof,\nso the clause you actually used (see the contents of %w and it's sons) is:\n",[H]),
	me_write_clause(Contents,UsedBody), nl,
	writeln("You have to use the same signs in the whole proof.").

/* Literal stimmt nicht mit dem Head der verwendeten Kontraposition ueberein */
me_error_msg(head,H,[0,Contra,ContraLit,Lit]) :-
	printf("The contrapositive %w applied at node %w has the head: ",
	[Contra,H]),
	write(ContraLit),
	printf(".\nThe contents of %w is: %w.\nI cannot see that the latter is an instance of the former.",[H,Lit]).
me_error_msg(head,H,[Flag,Contra,ContraLit,Lit]) :-
	printf("The contrapositive %w has the head:\n",[Contra]),
	write(ContraLit),
	printf(".\nNode %w has a contents of\n %w.\nSince I suppose you are using a ",[H,Lit]),
	((Flag='+'), write("tableau-style")
	 ;
	 write("goal-oriented")
	),
	printf(" representation of the ME proof\nI must state that the contrapositive %w is not applicable to %w.\n",[Contra,H]).

/* Fehler beim "ersten" Sohn */
me_error_msg(head_son,H,[FirstSon]) :-
	proof(H,contents,Lit),
	proof(FirstSon,contents,LitSon),
	printf("The contents of %w is:   %w.\nThe contents of %w (father of %w) is:   %w.\nThese contents should be complementary. A son with a contents complementary \nto it's father's is not required for ilf-serv, so this will be ignored.\n",
	[FirstSon,LitSon,H,FirstSon,Lit]). 

/* Reduktions-Fehler */
me_error_msg(red,H,[RH,Lit,RedLit]) :-
	printf("It is not possible to close node %w by reduction with node %w, since\n\t%w\nand\n\t%w,\nthe respective contents of %w and %w, are not complementary.\n",[H,RH,Lit,RedLit,H,RH]).

/* Faktorisierungs-Fehler */
me_error_msg(fac,H,[FH,Lit,FacLit]) :-
	printf("%w is not factorized by %w since their contents\n\t%w  (%w)\n\t%w  (%w)\ndiffer.\n",[H,FH,Lit,H,FacLit,FH]).

me_error_msg(empty_contents,H,_) :-
	printf("No contents is defined for node %w\n",[H]).
me_error_msg(empty_status,H,_) :-
	printf("No status is defined for node %w\n",[H]).
me_error_msg(var_status,H,_) :-
	printf("The status of node %w is a variable.\n",[H]).
me_error_msg(var_body,H,_) :-
	printf("The body of node %w contains a variable.\n",[H]).
me_error_msg(unknown_status,H,[Stat]) :-
	printf("Node %w: unknown status %w.\n",[H,Stat]).

me_error_msg(no_contra,H,Pred) :-
	printf("None of the predecessors of %w (",[H]),
	me_write_handlelist(Pred),
	writeln(") is an axiom or contrapositive").
me_error_msg(with_contra,H,_) :-
	printf("Node %w has no contrapositive but the ilf_state setheo_with_contrapositives is set.\n",[H]).

me_error_msg(predecessors(axiom),H,Pred) :-
	printf("The axiom %w has predecessors: ",[H]),
	me_write_handlelist(Pred),
	writeln(".\nAn axiom must not have any predecessors.").
me_error_msg(predecessors(contra),H,_) :-
	printf("The unique predecessor of a contra  must be an axiom.\nThis is not true for %w.\n",[H]).
me_error_msg(predecessors(none),H,[Father]) :-
	printf("Since %w has a status of 'none' it's father %w must have the status 'ext'.\n",
	[H,Father]).

me_error_msg(predecessors(Stat),H,[]) :-
	printf("Node %w has no predecessors.\nThis is not allowed for a node with a status of '%w'.\n",[H,Stat]).
me_error_msg(predecessors(Stat),H,Pred) :-
	write("The predecessors "),
	me_write_handlelist(Pred),
	printf(" of %w are illegal\nfor a node with a status of '%w'.\n",[H,Stat]).

me_error_msg(no_root,_,_) :-
	writeln("Cannot find a root of the proof tree.\nThe root is the (unique) node with a status of 'ext' that has one father the\nstatus of which is either 'contra' or 'axiom(...)'.").
me_error_msg(double_root,R,R1) :-
	printf("Both %w and %w appear to be the root of the proof tree.\nThe root is the unique node with a status of 'ext' that has one father the\nstatus of which is either 'contra' or 'axiom(...)'.\n",[R,R1]).

me_error_msg(no_ax,H,[Pred]) :-
	printf("For a node whose status is 'contra' it is required that it's  unique\nfather has the status `axiom(...)'. This is not true for node %w with\npredecessor %w.\n",[H,Pred]).

/* Default-Ausschriften */
me_error_msg(Code,H,[]) :-
	printf("%w: %w\n",[Code,H]).
me_error_msg(Code,H,Info) :-
	printf("%w: %w (info: %w\n)",[Code,H,Info]).

me_write_clause(Head,[]) :-
	me_proof_sign(-),
	me_negation(Head,NotHead),
	printf("%w.",[NotHead]).
me_write_clause(Head,[]) :-
	printf("%w.",[Head]).
me_write_clause(Head,Body) :-
	me_proof_sign(-),
	me_negation(Head,NotHead),
	printf("%w:-",[NotHead]),
	me_write_body(-,Body).
me_write_clause(Head,Body) :-
	printf("%w:-",[Head]),
	me_write_body(+,Body).

me_write_body(_,[]) :-
	write("empty.").
me_write_body(+,[Lit]) :-
	printf("%w.",[Lit]).
me_write_body(-,[Lit]) :-
	me_negation(Lit,NegLit),
	printf("%w.",[NegLit]).
me_write_body(+,[Lit|R]) :-
	printf("%w,",[Lit]),
	me_write_body(+,R).
me_write_body(-,[Lit|R]) :-
	me_negation(Lit,NegLit),
	printf("%w,",[NegLit]),
	me_write_body(-,R).

me_write_handlelist([]) :-
	write("\b").
me_write_handlelist([H|R]) :-
	printf("%w,",[H]),
	me_write_handlelist(R).
	

/************                ilf_serv_do                 **************/

/* ilf_serv_do/0 startet die eigentliche Arbeit. Vorausgesetzt wird,
   dass die ilf_state's 
   - ilf_serv_prover (setheo, komet, proof_me oder none),  
   - ilf_serv_type (me oder block),
   - ilf_serv_commands (Liste der auf den Blockbeweis anzuwendenen Kdos), 
   - ilf_serv_name (der Name der Eingabefiles  ohne Endung),
   - ilf_serv_outname (der Name der Ausgabefiles ohne Endung) und
   - ilf_serv_out (die Endungen der gewuenschten Ausgabefiles)
   bekannt sind. Nach der Erzeugung eines Blockbeweises durch ini_system/1
   und ini_type/1 werden mit check_proof gewisse Grundvoraussetzungen
   geprueft. ilf_serv_do/1 fuehrt die gewuenschten Kommandos aus. */

ilf_serv_do :-
	ilf_state(ilf_serv_prover,System),
	ilf_state(ilf_serv_name,Name),
	(ini_system(System,Name)
	 ;
	 ilf_serv_sys_error(ini_system(System,Name))
	),
	
	not(not(fix_handle)),
	not(not(check_proof)), 
	ilf_state(ilf_serv_type,Type),
	(not(not(ini_type(Type)))
	 ;
	 ilf_serv_sys_error(ini_type(Type))
	),
	ilf_state(ilf_serv_commands,Cmds),
	!,
	ilf_serv_do(Cmds),
	ilf_state(ilf_serv_output,OutputList),
	output(OutputList).

/* ini_system/1 und ini_type/1 fuehren alles aus, was notwendig ist,
   um aus den Eingabefiles das proof/3 Praedikat fuer einen Blockbeweis
   zu erzeugen. */

ini_system(setheo,Name) :-
	!,
	open_right_module("dedsys/setheo/setheo.pl"),
	(import (search_results/3,assert_files/4) from setheo),
	get_flag(toplevel_module,Top),
	Internals=((ax_name/4),(formula_number/2),(lnr/1),(tree/1),(proof/3),(trans_handle/2),(trans_ext/3),(contra/3),(contrapos/3),(setheo_proved/0),(setheo_goal/5),(setheofile/2),(ilf_serv_goal/2)),
	make_abolish(Internals,Top),
	make_dynamic(Internals,Top),
	make_exported(Internals,Top),
	(import Internals from Top),
	call(assert(setheo_goal(Goal,setheo_goal,1,setheo_goal_status,1) :-
	ilf_serv_goal(_,Goal)),Top),
	call((import (search_results/3) from setheo),Top),
	assert_files(Name,LopFile,_,Top),
	concat_string([LopFile,"p"],LoppFile),
	concat_string([LopFile,"name"],LopnameFile),
	get_ax_name(LoppFile,LopnameFile),
	call(search_results(setheo,1,1),Top),
	concat_string([Name,".out"],Outfile),
	get_uih_file(Outfile,OutF),
	compile(OutF,Top).
ini_system(komet,Name) :-
	!,
	open_right_module("dedsys/komet/komet.pl"),
	port_komet(assert_files(1,Name,LopFile)),
	LoppFile is_string LopFile & "p",
	LopnameFile is_string LopFile & "name",
	get_ax_name(LoppFile,LopnameFile),
	port_komet(search_results(komet,1,1)),
	Outfile is_string Name & ".out",
	compile(Outfile),
	erase_module(setheo).
ini_system(otter,Name) :-
	!,
	/* otter.pl only needed for writing to otter (?) */
	% open_right_module("dedsys/otter/otter.pl"),
	Outfile is_string Name & ".out",
	get_right_file(Outfile,Outfile1),
	reconsult(Outfile1),
	set_goal_no,
	retract(goal_no(GoalNo)),
	proof([1,GoalNo],contents,Cont),
	( Cont=not(NegCont), Goal=NegCont
	;
	Goal=not(Cont) ),
	port_otter(assert(otterfile(Outfile))),
	port_otter(assert(ilf_serv_goal(goal,Goal))),
	port_otter(tell_append(Outfile)),
        port_otter(writeln("proof([1,global],goal,(%)).",[Goal])),
        port_otter(writeln("proof([1,global],system,otter).")),
        port_otter(told_append(Outfile)),
	port_otter(search_results(otter,1,1)),
	compile(Outfile),
	(o2bl ; ilf_serv_sys_error(o2bl)),!.
ini_system(discount,Name) :-
	!,
	Outfile is_string Name & ".tmp",
	compile(Outfile),
	(dsc2bl ; ilf_serv_sys_error(dsc2bl)),!.
ini_system(_,Name) :-
	Outfile is_string Name & ".out",
	compile(Outfile).

ini_type(me) :- 
	!,

	fix_me_status,
	check_for_query,
	(check_me_proof ; ilf_serv_error(nl)),
	(me2bl ; ilf_serv_sys_error(me2bl)), 
	make_ilf_state(ilf_serv_type,block),  /* insbesondere fuer refix_handle */
	remove_ax_names,
	(remove_query ; ilf_serv_sys_error(remove_query)),
	/* Behandlung von Antwortsubstitutionen */
	(me_answers ; ilf_serv_sys_error(me_answers)),
	!.
ini_type(discount) :- 
	!.
ini_type(otter) :-
	!.
ini_type(_).

/* check_proof/0 testet die Existenz eines Goal und erzeugt ggf. die 
   ready/proved-Fakten. */

check_proof :-
	check_goal,
	(proof([_,global],control,proved)
	 ;
	 assert(proof([_,global],control,proved))
	),
	(proof([_,global],control,ready)
	 ;
	 assert(proof([_,global],control,ready))
	), !.

check_goal :- 
	proof([_,global],goal,_), !.
check_goal :-
	exporter(proof/N,situation),
	N > 3,
	once((
		ilf_state(handle_separator,Separator),
	 	fix_handle([],Separator,[PH,global],Hglobal)
	 	;
	 	Hglobal=[PH,global]
	)),
	ArgList=[Hglobal,goal|GoalList],
	length(ArgList,N),
	Proof =.. [proof|ArgList],
	clause(proof/N,Proof,_),
	list2goal(GoalList,Goal),
	asserta(proof([PH,global],goal,Goal)), !.
check_goal :-
	ilf_serv_error(writeln("No goal found.")).

list2goal([Formula],Formula).
list2goal([Formula|R],(Formula,Conj)) :- list2goal(R,Conj).
	


/* output/1 erzeugt die Ausgabefiles mit den als Liste uebergebenen Endungen.
   Gibt es dabei einen Fehler, wird das entsprechende File geloescht, die
   anderen Files werden aber, wenn moeglich, trotzdem erzeugt */

output([]).
output([Ext|R]) :-
        ilf_state(ilf_serv_outname,Name),
        (try_output(Name,Ext),
         ilf_serv_log(writeln("%-file written.",[Ext]))
         ;
         ilf_serv_log(writeln("error writing %-file",[Ext])),
         rm_output(Name,Ext)
        ),
        output(R).

try_output(_,".log") :- !.
try_output(Name,".tex") :-
	!,
        TexName is_string Name & ".tex",
        prooftex1(TexName).
try_output(Name,".out") :-
	!,
        OutName is_string Name & ".out",
        refix_handle,
        tell(OutName),
        listing(proof/3),
        told,
        fix_handle.       /* falls das .tv-File danach geschrieben wird */
try_output(Name,".tv") :-
	!,
	TvName is_string Name & ".tv",
	show_block_dependencies(TvName).
try_output(_,String) :-
	string(String),
	!,
	ilf_serv_log(printf("Don't know how to create a %w-file.\n",[String])).
try_output(_,Other) :-
	ilf_serv_sys_error(try_output(Other)).

rm_output(Name,Ext) :-
	FileSpec is_string Name & Ext,
	exists(FileSpec),
	delete_file(FileSpec).
rm_output(_,_).


/* ilf_serv_do/1 fuehrt die uebergebene Liste von Prologkommandos aus.
   Wird dabei ein illegales Kommando gefunden (die Pruefung auf Zulaessigkeit 
   wird dabei durch ilf_serv_command/1 vorgenommen) oder schlaegt ein Kommando 
   fehl, bricht die Abarbeitung mit einer entsprechenden Meldung ab. */

ilf_serv_do([]) :-
	ilf_serv_log((
		write("ilf-serv commands done."),nl
	)).
ilf_serv_do([Cmd|R]) :-
	(ilf_serv_do_1(Cmd)
	 ;
	 ilf_serv_error(printf("%w failed.\n",[Cmd])) 
	),
	ilf_serv_log(printf("%w succeded.\n",[Cmd])),
	!,
	ilf_serv_do(R).

ilf_serv_do_1(Cmd) :- 
	ilf_serv_command(Cmd),
	!,
	call(Cmd).
ilf_serv_do_1(Cmd) :- 
	ilf_serv_error(printf("Illegal ilf-serv command: %w\n",[Cmd])).

/*************         Fehlerbehandlung/Logging          ******************/

/* ilf_serv_errror/4 ist der Errorhandler fuer Prolog-Fehler. Er schreibt
   alle verfuegbaren Informationen ins Logfile und bricht die Abarbeitung
   dann ab. Im Falle eines Syntax-Fehlers wird versucht, das File zu 
   ermitteln, in dem der Fehler auftrat und ueber error_msg eine 
   moeglichst aussagekraeftige Fehlermeldung zu erzeugen. */

ilf_serv_error(0,Number,_,_) :-
	state(error_goal,_,error), 
	state(output,_,ilf_serv_log),
	state(input,Stream,Stream),
	(stream(Stream,_,_,file(FileName),_) ; FileName=unknown),
	error_msg(FileName,VisibleFileName,Message,Report),
	(error_file(Number,PrologMessage,_)
	 ;
	 number_string(Number,NumberS),
	 concat_string(["Error ", NumberS],PrologMessage) 
	),
	printf("Syntax error in %w: %w",[VisibleFileName,PrologMessage]),
	writeln(Message), 
	Report,
	writeln("Context: "), 
	print_context, 
	ilf_serv_halt.
ilf_serv_error(_,Number,Goal,Extra) :-
	state(error_goal,_,error), 
	state(output,_,ilf_serv_log),
	write("ilf_serv prolog error: "),
	(error_file(Number,PrologMessage,_)
	 ;
	 PrologMessage is_string "Error " & string(Number,display)
	),
	writeln(PrologMessage),
	(Extra=[]
	 ;
	 writeln("Extra: %",[Extra])
	),
	writeln("Goal: %",[Goal]), 
	please_report,
	ilf_serv_halt.

error_msg(FileName,VisibleFileName,Message,Report) :-
	L is length(FileName),
	ext(FileName,Ext,L),
	error_msg1(Ext,VisibleFileName,Message,Report).

ext(unknown,unknown,_).
ext(FileName,signature,L) :- 
	Start is L - 13,
	Start is index(FileName,"signature.pro",Start).
ext(FileName,ilf_state,L) :- 
	Start is L - 13,
	Start is index(FileName,"ilf_state.pro",Start).
ext(FileName,texop,L) :- 
	Start is L - 9,
	Start is index(FileName,"texop.pro",Start).
ext(FileName,tree,L) :- 
	Start is L - 5,
	Start is index(FileName,".tree",Start).
ext(FileName,lop,L) :- 
	Start is L - 5,
	Start is index(FileName,".lopp",Start).
ext(FileName,lopname,L) :- 
	Start is L - 8,
	Start is index(FileName,".lopname",Start).
ext(FileName,out,L) :- 
	Start is L - 4,
	Start is index(FileName,".out",Start).

error_msg1(signature,"signature.pro","Please check the SIGNATURE part of your mail.",true).
error_msg1(ilf_state,"ilf_state.pro","Please check the ILF_STATE part of your mail.",true).
error_msg1(ilf_state,"texop.pro","Please check the TEXOP part of your mail.",true).
error_msg1(out,"out-file","Please check the .outfile you mailed.",true) :-
	ilf_state(ilf_serv_prover,none).
error_msg1(tree,"tree-file","Please check the .tree- and the _pp.lop-file you mailed.",true) :-
	ilf_state(ilf_serv_prover,setheo).
error_msg1(tree,"tree-file","Please check the .xptree- and the .ilf-file you mailed.",true) :-
	ilf_state(ilf_serv_prover,komet).
error_msg1(lop,".lop-file","Please check the .lop-file you mailed",true).
error_msg1(lopname,".lopname-file","Please check the .lopname-file you mailed.",true).
error_msg1(unknown,"unknown file","ilf-serv internal error",please_report).
error_msg1(Ext,Name,"ilf-serv internal error",please_report) :-
	Name is_string Ext & "-file".

/* ilf_serv_log/1 und ilf_serv_error/1 sind die Routinen, die von anderen
   Moduln aus aufgerufen werden koennen, um etwas ins Logfile zu schreiben
   oder die Abarbeitung nach einem Fehler zu beenden. Werden sie unter
   ilf aufgerufen, geht die Ausgabe zum gegenwaertigen output-Stream.
   ilf_serv_only/1 macht unter ilf gar nichts. Im standalone-Betrieb wird
   das Argument ausgefuehrt. */

ilf_serv_log(X) :- 
	ilf_state(ilf_serv,on),
	!,
	do_ilf_serv_log(X),
	!.
ilf_serv_log(X) :- call(X).

do_ilf_serv_log(X) :-
	ilf_state(ilf_serv_debug,on),
	write("ilf_serv log: "),
	once(X),
	fail.
do_ilf_serv_log(X) :-
	state(output,OldOutput,ilf_serv_log),
	(call(X) ; true),
	!,
	state(output,_,OldOutput).

ilf_serv_error(X) :- 
	ilf_state(ilf_serv,on),
	ilf_serv_log(X),
	ilf_serv_halt.
ilf_serv_error(X) :- call(X).

ilf_serv_sys_error(Pred) :-
	ilf_serv_error((
		writeln("ilf_serv internal error: % failed.",[Pred]),
		please_report
	)).

ilf_serv_only(X) :- 
	ilf_state(ilf_serv,on),
	!,
	call(X).
ilf_serv_only(_).

please_report :- 
	writeln("Please report to ilf-serv-request@mathematik.hu-berlin.de."). 
help_contact :- 
	writeln("Please contact ilf-serv-request@mathematik.hu-berlin.de if you need further information."). 


/* ilf_serv_halt/0 wird bei jedem Fehler aufgerufen. Es beendet Prolog und
   schreibt die Nachricht ins Logfile, nach der in ilf-serv.exe gegrept
   wird */

ilf_serv_halt :- 
	ilf_serv_log((nl,writeln("ilf_serv error halt."))),
	halt.

/************                     debugging                  ***********/


set_error_goal :- ilf_state(ilf_serv_debug,on), !. 
set_error_goal :- state(error_goal,_,ilf_serv_error).

% :- spy_ilf,ilf_serv_top.
