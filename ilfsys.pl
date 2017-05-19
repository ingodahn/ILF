/* Module ilfsys for reduced ILF system 2016 */

:- module(ilfsys).

:- export
	(initialize_ilfmodules)/0,
	(ini_ness_ilfmodules)/0,
	(ini_poss_ilfmodules)/0,
	(ilf_state)/2,
	(ilf_state/3),
	get_right_file/2,
	get_uih_file/2,
	spy_ilf/0.

:- dynamic 
	(ilf_state)/1,
	(ilf_state)/2,
	(user_end_goal)/1,
	(signature)/3,
	(x_xilfpro_pipe)/1,
	(x_proxilf_pipe/1),
	expert_file/2.   % eingelesen aus $UIH/tmp/ilf_state.pl

?- import
	registrate_err/2
			from errman.
	
:- export (ilf_debug/1,ilf_debug/2).	
ilf_debug(X) :- current_module(M),ilf_debug(X,M).
ilf_debug(X,Y) :- getval(debug,on),!,call(X,Y).
ilf_debug(_,_).

:- export (ilf_error/1).
ilf_error(X) :- current_module(M), ilf_error_body2(X,M).

:- export (ilf_warning/1).
ilf_warning(X) :- current_module(M),ilf_warning_body2(X,M).

:- export(ilf_error/2).
ilf_error(Format,Message) :- current_module(M),ilf_error_body3(Format,Message,M).

:- export (ilf_warning/2).
ilf_warning(Format,Message) :- current_module(M),ilf_warning_body3(Format,Message,M).

/* Dummy zum Debuggen  */
spy_ilf.

ilfsys_top :- 
	make_ilf_state(userilfhome, './'),
	make_ilf_state(ilfhome, './'),
	make_ilf_state(prologhome, 'PROLOGHOME'),
	load_ilf_state,
   	ilf_prompt,
	ilf_debug((write("ILFSYS version 1.77 updated 01/19/99 installed."),nl)).


/* initialize_ilfmodules/0
 * Anlegen der Arbeitsmoduln situation, axioms und tactics.
 * Oeffnen der Programmoduln.
 */
initialize_ilfmodules:-
	ini_ness_ilfmodules,
	ini_poss_ilfmodules.
	
/* Die Module die ilf zum Hochfahren braucht */	
ini_ness_ilfmodules:-           (current_module(axioms);create_module(axioms),call(dynamic(signature/3),axioms)),        
        (current_module(tactics);create_module(tactics)),
		compile("parasys.pl").
ini_poss_ilfmodules:-        
	compile("tools.pl"),
%	open_right_module("errman.pl"),
	compile("errman.pl"),
%	open_right_module("thman.pl"),
	compile("thman.pl"),
%    compile("ilf.pl"),
	compile("ilf_serv.pl"),
	compile("situation.pl"), %neu hinzugefuegt T.Baar
	erase_module(p3),
	create_module(p3),
	/* For restricted ILF 2016 we compile proof/3 directly into p3 */
	call((
%		compile_term([(proof(X,Y,Z) :- call(proof(X,Y,Z),situation))]),
		export(proof/3)),p3),
	compile("proof.pl"),
	compile("block.pl"),
	compile("outtools.pl"),
	compile("genout.pl"),
	compile("thout.pl"),
	compile("proofout.pl"),
        !.

% Fuer Errorausschriften steht ilf_error(MsgSL) und ilf_error(FormatS,MsgL)
% zur Verfuegung
% Analog ilf_warning


/* Normierte Error-Ausschriften. Zeigt Module mit an, deshalb als tool */
:- export (ilf_error/1,ilf_error_body2/2).

% MsgSL muss eine Liste von Strings oder Atomen sein, kurz was man mit
% concat_string/2 ausdrucken kann
ilf_error_body2(MsgSL,Module):-
	length(MsgSL, _),
	append(["ILF-ERROR: ",Module,": "],MsgSL,MsgSL1),
	append(MsgSL1,["\n"],MsgSl2),
	concat_string(MsgSl2,Output),
	(
	 current_predicate(msg_write/1),msg_write(Output)
	;
	 write(Output)
	),
	registrate_err(1, [Output]),

	flush(output),
	ilf_debug( spy_ilf ),  
	!.
ilf_error_body2(A, B):-
	ilf_error("ilf_error_body2(%w, %w) unexpected failed. May be %w is not a list?", [A, B, A]),
	!.

:- export ilf_error/2,ilf_error_body3/3.
ilf_error_body3(FormatS,MsgL,Module):-
	concat_string(["ILF-ERROR: ",Module,": ",FormatS,"\n"],ExtFS),
	(
	 current_predicate(msg_write/2),msg_write(ExtFS,MsgL)
	;
	 printf(ExtFS,MsgL)
	),  
	open("", string, Buf),   % now error-msg as OutString
	printf(Buf, ExtFS, MsgL), 
	current_stream(OutString, _, Buf),
	close(Buf),
	registrate_err(1, [OutString]),

	flush(output),
	ilf_debug( spy_ilf ),  
	!.



:- export (ilf_warning/1,ilf_warning_body2/2).

% MsgSL muss eine Liste von Strings oder Atomen sein, kurz was man mit
% concat_string/2 ausdrucken kann
ilf_warning_body2(MsgSL,Module):-
	length(MsgSL, _),
	append(["ILF-WARNING: ",Module,": "],MsgSL,MsgSL1),
	append(MsgSL1,["\n"],MsgSl2),
	concat_string(MsgSl2,Output),
	(
	 current_predicate(msg_write/1),msg_write(Output)
	;
	 write(Output)
	),  
	registrate_err(2, [Output]),

	flush(output),
	!.
ilf_warning_body2(A, B):-
	ilf_warning("ilf_warning_body2(%w, %w) unexpected failed. May be %w is not a list?", [A, B, A]),
	!.

:- export ilf_warning/2,ilf_warning_body3/3.
ilf_warning_body3(FormatS,MsgL,Module):-
	concat_string(["ILF-WARNING: ",Module,": ",FormatS,"\n"],ExtFS),
	(
	 current_predicate(msg_write/2),msg_write(ExtFS,MsgL)
	;
	 printf(ExtFS,MsgL)
	),  
	open("", string, Buf),   % now warning-msg as OutString
	printf(Buf, ExtFS, MsgL), 
	current_stream(OutString, _, Buf),
	close(Buf),
	registrate_err(2, [OutString]),

	flush(output),
	!.

		/* ilf_state */
		
load_ilf_state :- load_ilf_state("ilf_state.pl").

load_ilf_state(Fullname) :-
	exists(Fullname),
	!,
	retract_all(ilf_state(_)),
	assert(ilf_state(userilfhome)),
	assert(ilf_state(ilfhome)),
	assert(ilf_state(prologhome)),
	assert(ilf_state(style)),
	assert(ilf_state(tex_format)),
	assert(ilf_state(known_rules)),
	assert(ilf_state(known_theory)),
	assert(ilf_state(proof_title)),
	assert(ilf_state(proof_author)),
	make_default_ilfstates,
   	set_flag(variable_names, on),
   	compile(Fullname),
   	set_flag(variable_names, check_singletons),
	!.
load_ilf_state(Fullname) :-
	ilf_error("%w: file not found.\nilf_states unchanged.\n", [Fullname]).
	

reload_ilf_state :-
	reload_ilf_state0("").

reload_ilf_state(FileName) :-
	concat_string([" -i ", FileName], Arg),
	reload_ilf_state0(Arg).

reload_ilf_state0(Arg) :-
	get_right_file("bin/ilf", Ilf),
        get_uih_file("tmp/ilf_state.pl", IlfStateFile),
        concat_string([Ilf, Arg, " -ilf_state ", IlfStateFile], Cmd),
        sh(Cmd),
	load_ilf_state(IlfStateFile).

make_ilf_state(occur,on) :- set_flag(occur_check,on),fail.
make_ilf_state(State,Value) :-
	atom(State),
	(
		ilf_state(State)
		;
		assert(ilf_state(State))
	),
	setval(State,Value),
	!.

remove_ilf_state(State) :-
	retract(ilf_state(State)),
	!.
	 
ilf_state(S,X) :- ilf_state(S), !, getval(S,X).

ilf_state(occur,X,Y) :- get_flag(occur_check,X),
	set_flag(occur_check,Y),
	current_module(thman),
	once(call(	(
		clause_pool(occur,C),
		get_flag(all_dynamic,D),
		set_flag(all_dynamic,off),
		compile_term(C),
		set_flag(all_dynamic,D)
		),
	thman)),setval(occur,Y),xilf_set_buttons,!.
ilf_state(S,X,Y) :- ilf_state(S,X), setval(S,Y), !.

make_env_state(State,Env) :- getenv(Env,Val),
	make_ilf_state(State,Val).

/* set_ilf_state/2 koennte vom ilf-Skript anstelle von make_ilf_state benutzt
   werden, um bei nicht durch make_default_ilfstates definierten ILF States
   eine Warnung auszugeben. */

set_ilf_state(State, Value) :-
	ilf_state(State, _, Value),
	!.
set_ilf_state(State, Value) :-
	ilf_warning("unknown ILF state: %w", [State]),
	make_ilf_state(State, Value).

/* Default ilf_state */

make_default_ilfstates :- make_ilf_state(debug,off),
	make_ilf_state(debug_ini,off),
	make_ilf_state(default_max_sec,120),
	make_ilf_state(default_flexy_sec,30),
	make_ilf_state(discounthosts,[]),
	make_ilf_state(occur,off),
	make_ilf_state(x,off),
	make_ilf_state(xterm,on),
	make_ilf_state(mousemenu,proof),
	make_ilf_state(menu_level,1),
	make_ilf_state(experts,on),
	make_ilf_state(exp_mnu,on),
	make_ilf_state(exptty,on),
	make_ilf_state(host,none),
	make_ilf_state(display,":0.0"),
	make_ilf_state(tty,"/dev/tty"),
	make_ilf_state(treeviewer,off),
	make_ilf_state(print_types,off),
	make_ilf_state(typed_mode, typed),
	make_ilf_state(esetheo_split,off),
	make_ilf_state(setheo_split,off),
	make_ilf_state(setheo_eq,off),
	make_ilf_state(discountpar,standard),
	make_ilf_state(setheo_ch,off),
	make_ilf_state(discount_ch,off),
	make_ilf_state(pad_bg_ch,off),
	make_ilf_state(setheo_reord,on),
	make_ilf_state(tcl,on),
	make_ilf_state(compile_message, on),
	make_ilf_state(kb, on),
	make_ilf_state(out_mode, latex),
	make_ilf_state(default_proof_file, ".proof"),
	make_ilf_state(default_th_file, ".th"),
	make_ilf_state(default_theory, [_X - _Y]),
	make_ilf_state(pre_text, ""),
	make_ilf_state(post_text, ""),
	make_ilf_state(style,none),
	make_ilf_state(known_theory,[]),
	make_ilf_state(default_pad_preds, ".pad_preds"),
	make_ilf_state(default_pad_th, ".pad_th.th"),
	true.

/* Filesystem */

make_sd_file(Relname):-
	get_uih_file(Relname,Absname),
	exists(Absname),
	write("ILFSYS: precompile "),writeln(Absname),
	dump(Absname).

get_uih_file(Relname,Absname):-
	getval(userilfhome,Userilfhome),
	concat_string([Userilfhome, "/", Relname],Absname),
	!.
get_ih_file(Relname,Absname):-
	getval(ilfhome,Ilfhome),
	concat_string([Ilfhome, "/", Relname],Absname),
	!.

last_slash_pos(String,Pos) :- 
	string_length(String,LString),
	substring(String,Pos,1,"/"),
	(L is LString - Pos),
	(Pos1 is Pos+1),
	substring(String,Pos1,L,String1),
	not substring(String1,"/",_),!.

get_file_name(Relname,Name) :- last_slash_pos(Relname,Pos),
	string_length(Relname,LRN),
	(Len is (LRN-Pos)),
	(Pos1 is Pos+1),
	substring(Relname,Pos1,Len,Name),!.

get_right_file(Relname,Absname):-
	getval(userilfhome,Userilfhome),
	concat_string([Userilfhome, "/", Relname],Absname),
	exists(Absname),!.
get_right_file(Relname,Absname):- 
	getval(ilfhome,Ilfhome),
	concat_string([Ilfhome,"/",Relname],Absname),
	exists(Absname),!.
get_right_file(Relname,Absname) :- 
	get_file_name(Relname,Name),
	concat_string(["pl/",Name],PLName),
	(get_uih_file(PLName,Absname)
	;
	get_ih_file(PLName,Absname)),
	exists(Absname).
	
get_right_file(Absname, Absname):-
	is_abs_filename(Absname),
	exists(Absname),!.
get_right_file(Relname,_) :-
	ilf_warning("get_right_file: cannot find file %w", [Relname]),
        !,fail.	

get_right_exec_file(Relname,Absname):-
        getval(userilfhome,Userilfhome),
        concat_string([Userilfhome, "/", Relname],Absname),
        exists(Absname),
	get_file_info(Absname,executable, on),
	!.
get_right_exec_file(Relname,Absname):-
        getval(ilfhome,Ilfhome),
        concat_string([Ilfhome,"/",Relname],Absname),
        exists(Absname),
        (
         get_file_info(Absname,executable, on)
        ;
         ilf_debug((
		    ilf_warning("file %w not executable", [Absname])
		    %write("WARNING: file: "), write(Relname), write(" not executable"), nl
         )), fail
        ), !.
get_right_exec_file(Relname,_) :-
        ilf_debug((
          write("file: "), write(Relname), write(" not found"), nl
        )),
        fail.   

is_abs_filename(Absname):-
	atom(Absname),
	atom_string(Absname, AbsnameS),
	!,
	is_abs_filename(AbsnameS).
is_abs_filename(AbsnameS):-
	string(AbsnameS),
	AbsnameS \= "",
	open(AbsnameS, string, Str),
	get_char(Str, Char),
	close(Str),
	(
	    Char = "/", !
	;
	    !,fail
	).
	

	/* Prompt */
ilf_prompt(_,_) :- ilf_state(ilf_prompt,S),
	printf(toplevel_output,S,[]),
	flush(toplevel_output).
	
ilf_prompt :- ilf_state(ilf_prompt,_),
	set_error_handler(153,ilf_prompt/2).
ilf_prompt.

:- ilfsys_top.