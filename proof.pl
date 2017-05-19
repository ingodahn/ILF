/* File @(#) proof.pl 1.20 (01/08/99) for reduced version of ILF 2016
   Behandlung und Konvertierung des Praedikates proof/3
   enthalten sind alle proof-related Funktionalitaeten von ILF
   Modul ist Bestandteil des Vordergrundes
   Autoren: Allner, Dahn, Wolf, Wernhard
*/

:- module(proof).

:- export
	get_proof/1,
	select_proof/0,
	present_proof/0,
	proof2ilf/0,
	put_proof/1,
	show_proof/0,
	undo/0,
	undo_enable/0.
/*	
:- import ilf_serv.
*/
:- import ilfsys.

:- import proof/3 from situation.

:- export 
	  access_mode/1,
	  current_access_mode/1,

	  line_id/2,
          line_proof/2,
          line_status/2,
          line_subproof/2,
	  line_predecessors/2,
	  line_successor/2,
	  line_contents/2,
	  line_control/2,
	  line_name/2,
	  line_declaration/2,
	  line_supers/2,

	  proof_id/2,
	  proof_lines/2,
	  proof_line/2,
	  proof_superline/2,
	  proof_firstline/2.


:-export                            %%  for now this is here          

	  install_p3_dynamic/1,
	  install_p3_module/1,
	  install_p3_compile/1,
	  install_p3_compile_term/1,

	  p3_assert/1,
          p3_asserta/1,
          p3_retract/1,
          p3_retract_all/1,
	  p3_listing/1.




?- begin_module(proof).

proof_top :- ilf_debug(write("ProofManager 1.20 (01/08/99) installed\n")).

/* Lesen und schreiben von proof/3 */

undo_enable :-
	get_flag(toplevel_module,Top),
	call(current_predicate(proof/3),Top),
	get_uih_file("tmp/undo.pro",F),
	tell(F),
	call(listing(proof/3),Top),
	told,!.
undo_enable :- write("ILF ERROR: proof/3 not found!\n").

undo :- get_uih_file("tmp/undo.pro",F),
	exists(F),
	get_flag(toplevel_module,Top),
	call((
		dynamic(proof/3),
		compile(F),
		(
		get_flag(proof/3,visibility,exported)
		;
		export(proof/3)
		)
	),Top),
	!.
undo :- ilf_serv_error(write("ILF: ERROR: No undo information available.\n")),!,fail.

get_proof(Job) :-
	sprintf(F, "tmp/ilf.%w.out", Job),
        get_uih_file(F,File),
	get_proof0(File), 
	!.
get_proof(File) :-
	(atom(File) ; string(File)),
	get_proof0(File),
	!.
get_proof(Job) :-
	sprintf(Name, "%w", Job),
	(is_filename(Name) ->
		FileName=Name 
		; 
		sprintf(FileName, "ilf.%w.out", Job)
	),
	ilf_error("File %w not found!", [FileName]),
        !, fail.

/* Fuer die Fehlermeldung von get_proof/1 wird versucht zu erraten, ob
   das Argument eine Jobnummer oder ein Filename war. */

is_filename(Name) :- substring(Name, ".", _), !.
is_filename(Name) :- substring(Name, "/", _), !.

get_proof0(File) :-
        exists(File),
        get_flag(toplevel_module,Top),
	install_p3_dynamic(Top),
        call((
        	% dynamic(proof/3),
        	compile_with_failure(File),
        	(
		get_flag(proof/3,visibility,exported)
		;
		export(proof/3)
		)
	),Top).
	
put_proof(Job) :-
	sprintf(F, "tmp/ilf.%w.out", Job),
        get_uih_file(F,File),
        get_flag(toplevel_module,Top),
        call((
        	current_predicate(proof/3),
        	get_flag(proof/3,stability,dynamic)
        ),Top),
        tell(File),
        call(listing(proof/3),Top),
        told,!.
put_proof(_) :- get_flag(toplevel_module,Mod),
	ilf_warning("Could not save proof in module %w (does not exist or is not dynamic\n",[Mod]).
	
select_proof :- get_uih_file("/tmp/Prover.Name.out",F),
	write("Enter >Name.< to select file "),writeln(F),
	read(Name),
	make_ilf_state(current_proof,Name),
	printf("ilf_state current_proof set to %w\n",[Name]),
	!.

proof2ilf :- ilf_state(current_prover,System),
	ilf_state(current_proof,Nr),
	term_string(Nr,NrS),
	concat_string(["tmp/",System,".",NrS],InS),
	get_uih_file(InS,InFile),
	concat_string([InFile,".tmp"],InFileTmp),
	(exists(InFileTmp) -> delete(InFileTmp);true),
	concat_string(["cp ",InFile,".out ",InFileTmp],Copy),
	exec(Copy,[nil,nil,nil]),!,
	get_right_file("bin/toilf",ToIlf),
	concat_string([ToIlf,".",System," ",InFile],Cmd),
	exec(Cmd,[nil,nil,nil]),!,
	ini_system(System,InS),
	concat_string(["tmp/ilf.",NrS,".out"],Target),
	get_uih_file(Target,TargetFile),
	(exists(TargetFile) -> delete(TargetFile);true),
	concat_string(["mv ",InFile,".out ",TargetFile],TargetCmd),
	exec(TargetCmd,[nil,nil,nil]),
	concat_string(["mv ",InFileTmp," ",InFile,".out"],EndCmd),
	exec(EndCmd,[nil,nil,nil]),
	change_xa_vres,
	put_proof(Nr),
	ilf_state(current_prover,_,ilf),
	writeln("Conversion successful. Current prover set to ilf"),
	write(TargetFile),writeln(" generated."),!.

change_xa_vres :- get_flag(toplevel_module,Top),
	call((
		retract(proof(H,status,axiom(xa_vres_fli(_)))),
		assert(proof(H,status,axiom([]))),
		fail
	),Top).
change_xa_vres.

show_proof :-
	ilf_state(current_proof,Proof),
	term_string(Proof,ProofS),
	concat_string(["tmp/ilf.",ProofS,".out"],Out),
	get_uih_file(Out,File),
	exists(File),!,
	tv_proof(Proof),!.
show_proof :-
	ilf_state(current_proof,Proof),
	term_string(Proof,ProofS),
	concat_string(["tmp/ilf.",ProofS,".out"],Out),
	get_uih_file(Out,File),
	!,
	printf("ILF ERROR: File %w not found.\n",[File]).
show_proof :- writeln("ILF ERROR: ilf_state current_proof not set").

present_proof :- 
	ilf_state(current_proof,Proof),
	get_right_file("bin/make_mail",Mail),
	concat_string([Mail," ",Proof],Cmd),
	exec(Cmd,[nil,S,nil]),
	read_string(S,"\n",_,N),
	writeln(N),
	close(S),!.
present_proof :- writeln("ILF ERROR: No proof selected.").

/* Ende Lesen und schreiben von proof/3 */

?- proof_top.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%
%%%% ACCESSORS
%%%%
%%%% Access predicates for proofs.
%%%%
%%%% Author: Wernhard
%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% 
%%% Depending on the concrete data structures used to represent proofs,
%%% several implementations (called "access modes") for these predicates
%%% can be installed by compiling their definitions. Therefore this file
%%% contains only the module interface and installation routines.
%%% 
%%% The default implementation, working on the proof/3 predicate defined 
%%% in the module p3 is contained in std_accessors.pl, which is compiled
%%% when compiling this file. std_accessors.pl [for now] also contains some
%%% documentation about the semantics of the accessor predicates.
%%%


:- (
	get_flag(library_path, Path1), 
   	ilf_state(ilfhome, IH),
	concat_string([IH, "/pl"], IHpl),
   	set_flag(library_path, [IHpl | Path1])
	;
	true
   ),
   (
	get_flag(library_path, Path2), 
   	ilf_state(userilfhome, UIH),
	concat_string([UIH, "/pl"], UIHpl),
   	set_flag(library_path, [UIHpl | Path2])
	;
	true
   ).

:- make_local_array(current_access_mode).
:- setval(current_access_mode, none).

:- compile(std_accessors).
/*
:- compile(library(std_accessors)).
:- open_right_module("pl/std_accessors").
*/
%%%% 
%%%% current_access_mode(--AccessMode)
%%%% 
%%%% Returns an atom specifying the current access mode.
%%%%

current_access_mode(X) :-
	getval(current_access_mode, X).


%%%% 
%%%% access_mode(++AccessMode)
%%%% 
%%%% Compile the files necessary to ensure that the implementation of 
%%%% the proof accessor predicates is the one specified by AccessMode.
%%%% 

access_mode(X) :-
	current_access_mode(X),
	!.
access_mode(std) :-
	% compile('~ilf/pl/std_accessors').
        compile(library(std_accessors)).
access_mode(db) :-
	access_mode(std),
	% compile('~ilf/pl/db_accessors'),
	compile(library(db_accessors)),
	install_p3_compile_term(
	   [proof(X,Y,Z) :- call(db_proof(X,Y,Z), article)]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%% 
%%%% install_p3...
%%%% 

install_p3(Module) :-
	reset_p3,
	call(compile_term([proof(X,Y,Z) :- call(proof(X,Y,Z), Module)]), p3).

install_p3_compile(File) :-
	reset_p3,
	call(compile(File), p3).

install_p3_compile_term(Term) :-
	reset_p3,
	call(compile_term(Term), p3).

reset_p3 :-
	call(
	  ( is_predicate(proof/3) ->
            abolish(proof/3),
 	    export(proof/3)
            ; true
          ),
          p3).

install_p3_dynamic(Module) :-
	reset_p3,
	( Module \= p3 ->
	  call(
	    ( is_predicate(proof/3) ->
              abolish(proof/3)
            ; true
            ),
          Module),
	  call(compile_term([proof(X,Y,Z) :- call(proof(X,Y,Z), Module)]), p3)
	; true
        ),
	call(dynamic(proof/3), Module),
        compile_term(
	        [p3_assert(X) :- call(assert(X), Module),
	         p3_asserta(X) :- call(asserta(X), Module),
	         p3_retract(X) :- call(retract(X), Module),
                 p3_retract_all(X) :- call(retract_all(X), Module),
                 p3_listing(X) :- call(listing(X), Module)]).

         


